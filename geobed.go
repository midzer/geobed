package geobed

import (
	"archive/zip"
	"bufio"
	"bytes"
	"context"
	"encoding/gob"
	"fmt"
	"io"
	"log"
	"net/http"
	"os"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"

	geohash "github.com/TomiHiltunen/geohash-golang"
	"golang.org/x/sync/errgroup"
)

// A list of data sources.
var dataSetFiles = []map[string]string{
	{"url": "http://download.geonames.org/export/dump/cities500.zip", "path": "./geobed-data/cities500.zip", "id": "geonamesCities500"},
	{"url": "http://download.geonames.org/export/dump/countryInfo.txt", "path": "./geobed-data/countryInfo.txt", "id": "geonamesCountryInfo"},
}

// A handy map of US state codes to full names.
var UsSateCodes = map[string]string{
	"AL": "Alabama",
	"AK": "Alaska",
	"AZ": "Arizona",
	"AR": "Arkansas",
	"CA": "California",
	"CO": "Colorado",
	"CT": "Connecticut",
	"DE": "Delaware",
	"FL": "Florida",
	"GA": "Georgia",
	"HI": "Hawaii",
	"ID": "Idaho",
	"IL": "Illinois",
	"IN": "Indiana",
	"IA": "Iowa",
	"KS": "Kansas",
	"KY": "Kentucky",
	"LA": "Louisiana",
	"ME": "Maine",
	"MD": "Maryland",
	"MA": "Massachusetts",
	"MI": "Michigan",
	"MN": "Minnesota",
	"MS": "Mississippi",
	"MO": "Missouri",
	"MT": "Montana",
	"NE": "Nebraska",
	"NV": "Nevada",
	"NH": "New Hampshire",
	"NJ": "New Jersey",
	"NM": "New Mexico",
	"NY": "New York",
	"NC": "North Carolina",
	"ND": "North Dakota",
	"OH": "Ohio",
	"OK": "Oklahoma",
	"OR": "Oregon",
	"PA": "Pennsylvania",
	"RI": "Rhode Island",
	"SC": "South Carolina",
	"SD": "South Dakota",
	"TN": "Tennessee",
	"TX": "Texas",
	"UT": "Utah",
	"VT": "Vermont",
	"VA": "Virginia",
	"WA": "Washington",
	"WV": "West Virginia",
	"WI": "Wisconsin",
	"WY": "Wyoming",
	// Territories
	"AS": "American Samoa",
	"DC": "District of Columbia",
	"FM": "Federated States of Micronesia",
	"GU": "Guam",
	"MH": "Marshall Islands",
	"MP": "Northern Mariana Islands",
	"PW": "Palau",
	"PR": "Puerto Rico",
	"VI": "Virgin Islands",
	// Armed Forces (AE includes Europe, Africa, Canada, and the Middle East)
	"AA": "Armed Forces Americas",
	"AE": "Armed Forces Europe",
	"AP": "Armed Forces Pacific",
}

// Contains all of the city and country data. Cities are split into buckets by country to increase lookup speed when the country is known.
type GeoBed struct {
	cities    Cities
	countries []CountryInfo
}

type Cities []GeobedCity

func (c Cities) Len() int           { return len(c) }
func (c Cities) Swap(i, j int)      { c[i], c[j] = c[j], c[i] }
func (c Cities) Less(i, j int) bool { return strings.ToLower(c[i].City) < strings.ToLower(c[j].City) }

// GeobedCity is the combined city struct (the various data sets have different fields, this combines what's available and keeps things smaller).
type GeobedCity struct {
	City    string
	CityAlt string
	// TODO: Think about converting this to a small int to save on memory allocation. Lookup requests can have the strings converted to the same int if there are any matches.
	// This could make lookup more accurate, easier, and faster even. IF the int uses less bytes than the two letter code string.
	Country    string
	Region     string
	Population int32
	Geohash    string
}

// Holds information about the index ranges for city names (1st and 2nd characters) to help narrow down sets of the GeobedCity slice to scan when looking for a match.
var cityNameIdx map[string]int

// CountryInfo about each country from Geonames including; ISO codes, FIPS, country capital, area (sq km), population, and more.
// Particularly useful for validating a location string contains a country name which can help the search process.
// Adding to this info, a slice of partial geohashes to help narrow down reverse geocoding lookups (maps to country buckets).
type CountryInfo struct {
	Country            string
	Capital            string
	Area               int32
	Population         int32
	GeonameID          int32
	ISONumeric         int16
	ISO                string
	ISO3               string
	Fips               string
	Continent          string
	Tld                string
	CurrencyCode       string
	CurrencyName       string
	Phone              string
	PostalCodeFormat   string
	PostalCodeRegex    string
	Languages          string
	Neighbours         string
	EquivalentFipsCode string
}

// An index range struct that's used for narrowing down ranges over the large Cities struct.
type searchRange struct {
	from int
	to   int
}

// NewGeobed creates a new Geobed instance. You do not need more than one. You do not want more than one. There's a fair bit of data to load into memory.
func NewGeobed() (*GeoBed, error) {
	gBed := &GeoBed{}

	var err error
	gBed.cities, err = loadGeobedCityData()
	if err != nil && !os.IsNotExist(err) {
		return nil, fmt.Errorf("loadGeobedCityData: %w", err)
	}
	gBed.countries, err = loadGeobedCountryData()
	if err != nil && !os.IsNotExist(err) {
		return nil, fmt.Errorf("loadGeobedCountryData: %w", err)
	}

	if err := loadGeobedCityNameIdx(); err != nil || len(gBed.cities) == 0 {
		if err := gBed.downloadDataSets(context.Background(), nil); err != nil {
			return nil, fmt.Errorf("downloadDataSets: %w", err)
		}
		gBed.loadDataSets()
		gBed.store()
	}

	return gBed, nil
}

// Downloads the data sets if needed.
func (g *GeoBed) downloadDataSets(ctx context.Context, client *http.Client) error {
	// Go over he dataset files and check if there are some missing.
	var pendingFetch []map[string]string
	for _, dataSetEntry := range dataSetFiles {
		if _, err := os.Stat(dataSetEntry["path"]); err == nil {
			continue
		} else if err != nil && !os.IsNotExist(err) {
			return fmt.Errorf("read stat %q: %w", dataSetEntry["path"], err)
		}
		pendingFetch = append(pendingFetch, dataSetEntry)
	}
	// Nothing is missing, stop here.
	if len(pendingFetch) == 0 {
		return nil
	}

	// Make sure the target directory exists.
	if err := os.Mkdir("./geobed-data", 0777); err != nil && !os.IsExist(err) {
		return fmt.Errorf("mkdir ./geobed-data: %w", err)
	}

	if client == nil {
		client = &http.Client{}
	}

	// Download everything in parallel.
	wg, ctx := errgroup.WithContext(ctx)

	for _, dataSetEntry := range dataSetFiles {
		dataSetEntry := dataSetEntry
		wg.Go(func() (err error) {
			defer func() {
				if err != nil { // If we have an error, delete the file so next run will retry.
					_ = os.Remove(dataSetEntry["path"])
				}
			}()
			f, err := os.Create(dataSetEntry["path"])
			if err != nil {
				return fmt.Errorf("create file %q: %w", dataSetEntry["path"], err)
			}
			defer func() { _ = f.Close() }() // Beset effort.

			req, err := http.NewRequestWithContext(ctx, http.MethodGet, dataSetEntry["url"], nil)
			if err != nil {
				return fmt.Errorf("invalid url %q: %w", dataSetEntry["url"], err)
			}

			resp, err := client.Do(req)
			if err != nil {
				return fmt.Errorf("fetch %q: %w", dataSetEntry["url"], err)
			}
			defer func() { _ = resp.Body.Close() }() // Best effort.
			if _, err := io.Copy(f, resp.Body); err != nil {
				return fmt.Errorf("consume %q: %w", dataSetEntry["url"], err)
			}

			return nil
		})
	}

	if err := wg.Wait(); err != nil {
		return err
	}

	return nil
}

var reTab = regexp.MustCompile("\t")

// Unzips the data sets and loads the data.
func (gBed *GeoBed) loadDataSets() {
	for _, dataSetEntry := range dataSetFiles {
		// This one is zipped
		if dataSetEntry["id"] == "geonamesCities500" {
			zipReader, err := zip.OpenReader(dataSetEntry["path"])
			if err != nil {
				log.Fatal(err)
			}
			defer func() { _ = zipReader.Close() }() // Best effort.

			for _, zipFileEntry := range zipReader.File {
				f, err := zipFileEntry.Open()
				if err != nil {
					log.Fatal(err)
				}
				defer func() { _ = f.Close() }() // Best effort.

				// Geonames uses a tab delineated format and it's not even consistent. No CSV reader that I've found for Go can understand this.
				// I'm not expecting any reader to either because it's an invalid CSV to be frank. However, we can still split up each row by \t
				scanner := bufio.NewScanner(f)
				scanner.Split(bufio.ScanLines)

				for scanner.Scan() {
					// So regexp, sadly, must be used (well, unless I wanted parse each string byte by byte, pushing each into a buffer to append to a slice until a tab is reached, etc.).
					// But I'd have to also then put in a condition if the next byte was a \t rune, then append an empty string, etc. This just, for now, seems nicer (easier).
					// This is only an import/update, so it shouldn't be an issue for performance. If it is, then I'll look into other solutions.
					fields := reTab.Split(scanner.Text(), 19)

					// NOTE: Now using a combined GeobedCity struct since not all data sets have the same fields.
					// Plus, the entire point was to geocode forward and reverse. Bonus information like elevation and such is just superfluous.
					// Leaving it here because it may be configurable... If options are passed to NewGeobed() then maybe Geobed can simply be a Geonames search.
					// Don't even load in MaxMind data...And if that's the case, maybe that bonus information is desired.
					if len(fields) != 19 {
						continue
					}

					latitude, _ := strconv.ParseFloat(fields[4], 64)
					longitude, _ := strconv.ParseFloat(fields[5], 64)
					population, _ := strconv.Atoi(fields[14])

					gHash := geohash.Encode(latitude, longitude)
					// This is produced with empty lat/lng values - don't store it.
					if gHash == "7zzzzzzzzzzz" {
						gHash = ""
					}

					gCity := GeobedCity{
						City:       strings.Trim(string(fields[1]), " "),
						CityAlt:    string(fields[3]),
						Country:    string(fields[8]),
						Region:     string(fields[10]),
						Population: int32(population),
						Geohash:    gHash,
					}

					// Don't include entries without a city name. If we want to geocode the centers of countries and states, then we can do that faster through other means.
					if len(gCity.City) > 0 {
						gBed.cities = append(gBed.cities, gCity)
					}
				}
			}
		}

		// And this one is just plain text.
		if dataSetEntry["id"] == "geonamesCountryInfo" {
			fi, err := os.Open(dataSetEntry["path"])

			if err != nil {
				log.Fatal(err)
			}
			defer func() { _ = fi.Close() }() // Best effort.

			scanner := bufio.NewScanner(fi)
			scanner.Split(bufio.ScanLines)

			for scanner.Scan() {
				t := scanner.Text()
				// There are a bunch of lines in this file that are comments, they start with #.
				if string(t[0]) == "#" {
					continue
				}

				fields := regexp.MustCompile("\t").Split(t, 19)
				// Skip invalid lines.
				if len(fields) != 19 || fields[0] == "" || fields[0] != "0" {
					continue
				}

				isoNumeric, _ := strconv.Atoi(fields[2])
				area, _ := strconv.Atoi(fields[6])
				pop, _ := strconv.Atoi(fields[7])
				gid, _ := strconv.Atoi(fields[16])

				countryInfo := CountryInfo{
					ISO:                string(fields[0]),
					ISO3:               string(fields[1]),
					ISONumeric:         int16(isoNumeric),
					Fips:               string(fields[3]),
					Country:            string(fields[4]),
					Capital:            string(fields[5]),
					Area:               int32(area),
					Population:         int32(pop),
					Continent:          string(fields[8]),
					Tld:                string(fields[9]),
					CurrencyCode:       string(fields[10]),
					CurrencyName:       string(fields[11]),
					Phone:              string(fields[12]),
					PostalCodeFormat:   string(fields[13]),
					PostalCodeRegex:    string(fields[14]),
					Languages:          string(fields[15]),
					GeonameID:          int32(gid),
					Neighbours:         string(fields[17]),
					EquivalentFipsCode: string(fields[18]),
				}

				gBed.countries = append(gBed.countries, countryInfo)
			}
		}
	}

	// Sort []GeobedCity by city names to help with binary search (the City field is the most searched upon field and the matching names can be easily filtered down from there).
	sort.Sort(gBed.cities)

	// Index the locations of city names in the g.c []GeoCity slice. This way when searching the range can be limited so it will be faster.
	cityNameIdx = make(map[string]int, len(gBed.cities))
	for k, v := range gBed.cities {
		// Get the index key for the first character of the city name.
		indexKey := strings.ToLower(string(v.City[0]))
		if val, ok := cityNameIdx[indexKey]; ok {
			// If this key number is greater than what was previously recorded, then set it as the new indexed key.
			if val < k {
				cityNameIdx[indexKey] = k
			}
		} else {
			// If the index key has not yet been set for this value, then set it.
			cityNameIdx[indexKey] = k
		}
	}
}

// When geocoding, this provides a scored best match.
func (gBed *GeoBed) matchLocation(n string) GeobedCity {
	countryCode, usStateCode, abbrevSlice, nSlice := gBed.extractLocationPieces(n)
	// Take the reamining unclassified pieces (those not likely to be abbreviations) and get our search range.
	// These pieces are likely contain the city name. Narrowing down the search range will make the lookup faster.
	ranges := gBed.getSearchRange(nSlice)

	bestMatchingKeys := map[int]int{}
	bestMatchingKey := 0

	for _, rangeElem := range ranges {
		// When adjusting the range, the keys become out of sync. Start from rng.f
		currentKey := rangeElem.from

		for _, v := range gBed.cities[rangeElem.from:rangeElem.to] {
			currentKey++

			// Mainly useful for strings like: "Austin, TX" or "Austin TX" (locations with US state codes). Smile if your location string is this simple.
			if usStateCode != "" {
				if strings.EqualFold(n, v.City) && strings.EqualFold(usStateCode, v.Region) {
					return v
				}
			}

			// Abbreviations for state/country
			// Region (state/province)
			for _, av := range abbrevSlice {
				lowerAv := strings.ToLower(av)
				if len(av) == 2 && strings.EqualFold(v.Region, lowerAv) {
					if val, ok := bestMatchingKeys[currentKey]; ok {
						bestMatchingKeys[currentKey] = val + 5
					} else {
						bestMatchingKeys[currentKey] = 5
					}
				}

				// Country (worth 2 points if exact match)
				if len(av) == 2 && strings.EqualFold(v.Country, lowerAv) {
					if val, ok := bestMatchingKeys[currentKey]; ok {
						bestMatchingKeys[currentKey] = val + 3
					} else {
						bestMatchingKeys[currentKey] = 3
					}
				}
			}

			// A discovered country name converted into a country code
			if countryCode != "" {
				if countryCode == v.Country {
					if val, ok := bestMatchingKeys[currentKey]; ok {
						bestMatchingKeys[currentKey] = val + 4
					} else {
						bestMatchingKeys[currentKey] = 4
					}
				}
			}

			// A discovered state name converted into a region code
			if usStateCode != "" && usStateCode == v.Region {
				if val, ok := bestMatchingKeys[currentKey]; ok {
					bestMatchingKeys[currentKey] = val + 4
				} else {
					bestMatchingKeys[currentKey] = 4
				}
			}

			// If any alternate names can be discovered, take them into consideration.
			if v.CityAlt != "" {
				alts := strings.Fields(v.CityAlt)
				for _, altV := range alts {
					if strings.EqualFold(altV, n) {
						if val, ok := bestMatchingKeys[currentKey]; ok {
							bestMatchingKeys[currentKey] = val + 3
						} else {
							bestMatchingKeys[currentKey] = 3
						}
					}
					// Exact, a case-sensitive match means a lot.
					if altV == n {
						if val, ok := bestMatchingKeys[currentKey]; ok {
							bestMatchingKeys[currentKey] = val + 5
						} else {
							bestMatchingKeys[currentKey] = 5
						}
					}
				}
			}

			// Exact city name matches mean a lot.
			if strings.EqualFold(n, v.City) {
				if val, ok := bestMatchingKeys[currentKey]; ok {
					bestMatchingKeys[currentKey] = val + 7
				} else {
					bestMatchingKeys[currentKey] = 7
				}
			}

			for _, ns := range nSlice {
				ns = strings.TrimSuffix(ns, ",")

				// City (worth 2 points if contians part of string)
				if strings.Contains(strings.ToLower(v.City), strings.ToLower(ns)) {
					if val, ok := bestMatchingKeys[currentKey]; ok {
						bestMatchingKeys[currentKey] = val + 2
					} else {
						bestMatchingKeys[currentKey] = 2
					}
				}

				// If there's an exat match, maybe there was noise in the string so it could be the full city name, but unlikely. For example, "New" or "Los" is in many city names.
				// Still, give it a point because it could be the bulkier part of a city name (or the city name could be one word). This has helped in some cases.
				if strings.EqualFold(v.City, ns) {
					if val, ok := bestMatchingKeys[currentKey]; ok {
						bestMatchingKeys[currentKey] = val + 1
					} else {
						bestMatchingKeys[currentKey] = 1
					}
				}

			}
		}
	}

	return gBed.cities[bestMatchingKey]
}

var abbrevRe = regexp.MustCompile(`[\S]{2,3}`)

var cacheLock sync.Mutex
var cachedRe = map[string]*regexp.Regexp{}

// Splits a string up looking for potential abbreviations by matching against a shorter list of abbreviations.
// Returns country, state, a slice of strings with potential abbreviations (based on size; 2 or 3 characters), and then a slice of the remaning pieces.
// This does a good job at separating things that are clearly abbreviations from the city so that searching is faster and more accuarate.
func (gBed *GeoBed) extractLocationPieces(n string) (string, string, []string, []string) {
	// Extract all potential abbreviations.
	abbrevSlice := abbrevRe.FindStringSubmatch(n)

	// Convert country to country code and pull it out. We'll use it as a secondary form of validation. Remove the code from the original query.
	countryCode := ""
	for _, co := range gBed.countries {
		exp := "(?i)^" + co.Country + ",?\\s|\\s" + co.Country + ",?\\s" + co.Country + "\\s$"

		cacheLock.Lock()
		re, ok := cachedRe[exp]
		if !ok {
			re = regexp.MustCompile(exp)
			cachedRe[exp] = re
		}
		cacheLock.Unlock()

		if re.MatchString(n) {
			countryCode = co.ISO
			// And remove it so we have a cleaner query string for a city.
			n = re.ReplaceAllString(n, "")
		}
	}

	// Find US State codes and pull them out as well (do not convert state names, they can also easily be city names).
	usStateCode := ""
	for sc, _ := range UsSateCodes {
		exp := "(?i)^" + sc + ",?\\s|\\s" + sc + ",?\\s|\\s" + sc + "$"
		cacheLock.Lock()
		re, ok := cachedRe[exp]
		if !ok {
			re = regexp.MustCompile(exp)
			cachedRe[exp] = re
		}
		cacheLock.Unlock()

		if re.MatchString(n) {
			usStateCode = sc
			// And remove it too.
			n = re.ReplaceAllString(n, "")
		}
	}
	// Trim spaces and commas off the modified string.
	n = strings.Trim(n, " ,")

	// Now extract words (potential city names) into a slice. With this, the index will be referenced to pinpoint sections of the g.c []GeobedCity slice to scan.
	// This results in a much faster lookup. This is over a simple binary search with strings.Search() etc. because the city name may not be the first word.
	// This should not contain any known country code or US state codes.
	nSlice := strings.Split(n, " ")

	return countryCode, usStateCode, abbrevSlice, nSlice
}

// There's potentially 2.7 million items to range though, let's see if we can reduce that by taking slices of the slice in alphabetical order.
func (gBed *GeoBed) getSearchRange(nSlice []string) []searchRange {
	// NOTE: A simple binary search was not helping here since we aren't looking for one specific thing. We have multiple elements, city, state, country.
	// So we'd end up with multiple binary searches to piece together which could be quite a few exponentially given the possible combinations...And so it was slower.

	ranges := make([]searchRange, 0, len(nSlice))
	for _, ns := range nSlice {
		if ns = strings.TrimSuffix(ns, ","); len(ns) == 0 {
			continue
		}
		// Get the first character in the string, this tells us where to stop.
		firstChar := strings.ToLower(string(ns[0]))
		// Get the previous index key (by getting the previous character in the alphabet) to figure out where to start.
		previousIndexKey := string(prev(rune(firstChar[0])))

		// To/from key
		fromKey := 0
		toKey := 0
		if val, ok := cityNameIdx[previousIndexKey]; ok {
			fromKey = val
		}
		if val, ok := cityNameIdx[firstChar]; ok {
			toKey = val
		}
		// Don't let the to key be out of range.
		if toKey == 0 {
			toKey = len(gBed.cities) - 1
		}
		ranges = append(ranges, searchRange{from: fromKey, to: toKey})
	}

	return ranges
}

func prev(r rune) rune { return r - 1 }

// Reverse geocode
func (gBed *GeoBed) ReverseGeocode(latitude, longitude float64) GeobedCity {
	gCity := GeobedCity{}

	gHash := geohash.Encode(latitude, longitude)
	// This is produced with empty lat/lng values - don't look for anything.
	if gHash == "7zzzzzzzzzzz" {
		return gCity
	}

	// Note: All geohashes are going to be 12 characters long. Even if the precision on the lat/lng isn't great. The geohash package will center things.
	// Obviously lat/lng like 37, -122 is a guess. That's no where near the resolution of a city. Though we're going to allow guesses.
	mostMatched := 0
	matched := 0
	for k, v := range gBed.cities {
		// check first two characters to reduce the number of loops
		if v.Geohash[0] == gHash[0] && v.Geohash[1] == gHash[1] {
			matched = 2
			for i := 2; i <= len(gHash); i++ {
				if v.Geohash[0:i] == gHash[0:i] {
					matched++
				}
			}
			// tie breakers go to city with larger population (NOTE: There's still a chance that the next pass will uncover a better match)
			if matched == mostMatched && gBed.cities[k].Population > gCity.Population {
				gCity = gBed.cities[k]
			}
			if matched > mostMatched {
				gCity = gBed.cities[k]
				mostMatched = matched
			}
		}
	}

	return gCity
}

// Dumps the Geobed data to disk. This speeds up startup time on subsequent runs (or if calling NewGeobed() multiple times which should be avoided if possible).
func (g GeoBed) store() error {
	buf := bytes.NewBuffer(nil)

	// Store the city info
	encoder := gob.NewEncoder(buf)

	if err := encoder.Encode(g.cities); err != nil {
		return fmt.Errorf("gob.Encode cities: %w", err)
	}

	citiesFile, err := os.Create("./geobed-data/cities.dmp")
	if err != nil {
		return fmt.Errorf("openFile %q: %w", "./geobed-data/cities.dmp", err)
	}
	defer func() { _ = citiesFile.Close() }() // Best effort.

	if _, err := buf.WriteTo(citiesFile); err != nil {
		return fmt.Errorf("writeTo %q: %w", "./geobed-data/cities.dmp", err)
	}

	// Store the country info as well (this is all now repetition - refactor)
	buf.Reset()
	if err := encoder.Encode(g.countries); err != nil {
		return fmt.Errorf("gob.Encode countries: %w", err)
	}

	countriesFile, err := os.Create("./geobed-data/countries.dmp")
	if err != nil {
		return fmt.Errorf("openFile %q: %w", "./geobed-data/countries.dmp", err)
	}
	defer func() { _ = countriesFile.Close() }() // Best effort.

	if _, err := buf.WriteTo(countriesFile); err != nil {
		return fmt.Errorf("writeTo %q: %w", "./geobed-data/countries.dmp", err)
	}

	// Store the index info (again there's some repetition here)
	buf.Reset()
	if err := encoder.Encode(cityNameIdx); err != nil {
		return fmt.Errorf("gob.Encode cityNameIdx: %w", err)
	}

	cityNameIdxFile, err := os.Create("./geobed-data/cityNameIdx.dmp")
	if err != nil {
		return fmt.Errorf("openFile %q: %w", "./geobed-data/cityNameIdx.dmp", err)
	}
	defer func() { _ = cityNameIdxFile.Chdir() }() // Best effort.

	if _, err := buf.WriteTo(cityNameIdxFile); err != nil {
		return fmt.Errorf("writeTo %q: %w", "./geobed-data/cityNameIdx.dmp", err)
	}

	buf.Reset()
	return nil
}

// Loads a GeobedCity dump, which saves a bit of time.
func loadGeobedCityData() ([]GeobedCity, error) {
	fh, err := os.Open("./geobed-data/cities.dmp")
	if err != nil {
		return nil, err
	}
	gc := []GeobedCity{}
	dec := gob.NewDecoder(fh)
	err = dec.Decode(&gc)
	if err != nil {
		return nil, err
	}
	return gc, nil
}

func loadGeobedCountryData() ([]CountryInfo, error) {
	fh, err := os.Open("./geobed-data/countries.dmp")
	if err != nil {
		return nil, err
	}
	co := []CountryInfo{}
	dec := gob.NewDecoder(fh)
	err = dec.Decode(&co)
	if err != nil {
		return nil, err
	}
	return co, nil
}

func loadGeobedCityNameIdx() error {
	fh, err := os.Open("./geobed-data/cityNameIdx.dmp")
	if err != nil {
		return err
	}
	dec := gob.NewDecoder(fh)
	cityNameIdx = make(map[string]int)
	err = dec.Decode(&cityNameIdx)
	if err != nil {
		return err
	}
	return nil
}
