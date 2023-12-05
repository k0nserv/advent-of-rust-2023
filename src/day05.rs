use std::ops::Range;
use std::str::FromStr;

use anyhow::{anyhow, Context, Result};

pub fn star_one(input: &str) -> Result<u64> {
    let almanac: Almanac = input.parse().expect("Almanc to be parsable");

    let ranges: Vec<Range<u64>> = almanac.seeds.iter().map(|&s| s..s + 1).collect();

    let chain = [
        almanac.find_map("seed-to-soil")?,
        almanac.find_map("soil-to-fertilizer")?,
        almanac.find_map("fertilizer-to-water")?,
        almanac.find_map("water-to-light")?,
        almanac.find_map("light-to-temperature")?,
        almanac.find_map("temperature-to-humidity")?,
        almanac.find_map("humidity-to-location")?,
    ];

    let result = chain.iter().fold(ranges, |acc, m| {
        acc.into_iter().flat_map(|r| m.map_range(r)).collect()
    });

    result
        .into_iter()
        .map(|r| r.start)
        .min()
        .ok_or_else(|| anyhow!("Failed to compute at least one destination"))
}

pub fn star_two(input: &str) -> Result<u64> {
    let almanac: Almanac = input.parse().expect("Almanc to be parsable");

    let ranges: Vec<Range<u64>> = almanac
        .seeds
        .chunks(2)
        .map(|c| {
            let start = c[0];
            let end = start + c[1];

            start..end
        })
        .collect();

    let chain = [
        almanac.find_map("seed-to-soil")?,
        almanac.find_map("soil-to-fertilizer")?,
        almanac.find_map("fertilizer-to-water")?,
        almanac.find_map("water-to-light")?,
        almanac.find_map("light-to-temperature")?,
        almanac.find_map("temperature-to-humidity")?,
        almanac.find_map("humidity-to-location")?,
    ];

    let result = chain.iter().fold(ranges, |acc, m| {
        acc.into_iter().flat_map(|r| m.map_range(r)).collect()
    });

    result
        .into_iter()
        .map(|r| r.start)
        .min()
        .ok_or_else(|| anyhow!("Failed to compute at least one destination"))
}

#[derive(Debug)]
struct Almanac {
    seeds: Vec<u64>,
    maps: Vec<Map>,
}

#[derive(Debug)]
struct Map {
    name: String,
    mappings: Vec<Mapping>,
}

#[derive(Debug)]
struct Mapping {
    destination_start: u64,
    source_start: u64,
    len: u64,
}

impl Almanac {
    fn find_map(&self, name: &str) -> Result<&Map> {
        self.maps
            .iter()
            .find(|m| m.name == name)
            .ok_or_else(|| anyhow!("No map with name {name}"))
    }
}

impl Map {
    fn map_range(&self, range: Range<u64>) -> impl Iterator<Item = Range<u64>> + '_ {
        // Is sorted
        self.mappings.iter().filter_map(move |m| {
            let start = m.source_start;
            let end = m.source_start.saturating_add(m.len);
            let outside = range.end <= start || range.start >= end;
            if outside {
                return None;
            }
            let new_start = m.destination_start + (range.start.max(start) - m.source_start);
            let new_end = m.destination_start + (range.end.min(end) - m.source_start);

            Some(new_start..new_end)
        })
    }
}

impl FromStr for Almanac {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Example
        // seeds: 79 14 55 13

        // seed-to-soil map:
        // 50 98 2
        // 52 50 48
        //
        // <More maps>

        let mut groups = s.split("\n\n").map(str::trim).filter(|s| !s.is_empty());

        let seed_group = groups
            .next()
            .ok_or_else(|| anyhow!("Missing initial seed specification"))
            .with_context(|| s.to_string())?;

        let (label, seeds) = seed_group
            .split_once(':')
            .ok_or_else(|| anyhow!("Invalid see specification"))
            .with_context(|| s.to_string())?;
        if label.trim() != "seeds" {
            return Err(anyhow!("Unexpected seed label {label}")).with_context(|| s.to_string());
        }
        let seeds = seeds
            .split_whitespace()
            .map(str::parse)
            .collect::<Result<Vec<_>, _>>()?;

        let maps = groups.map(str::parse).collect::<Result<Vec<_>, _>>()?;

        Ok(Self { seeds, maps })
    }
}

impl FromStr for Map {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Example map
        // seed-to-soil map:
        // 50 98 2
        // 52 50 48

        let mut lines = s.lines().map(str::trim);
        let (name, suffix) = lines
            .next()
            .ok_or_else(|| anyhow!("Missing first line in map defintion"))
            .and_then(|s| {
                s.split_once(char::is_whitespace)
                    .ok_or_else(|| anyhow!("Invalid first line in map defintion"))
            })
            .with_context(|| s.to_string())?;
        if suffix.trim() != "map:" {
            return Err(anyhow!(
                "Invalid map definition, missing `map:` suffix in first line"
            ))
            .with_context(|| s.to_string());
        }

        let mut explicit_mappings = lines.map(str::parse).collect::<Result<Vec<Mapping>, _>>()?;
        explicit_mappings.sort_by(|a, b| a.source_start.cmp(&b.source_start));

        // Materialize implicit mappings
        let mut previous_end = 0;
        let num_mappings = explicit_mappings.len();
        let mappings = explicit_mappings
            .into_iter()
            .enumerate()
            .flat_map(|(i, m)| {
                let new_len = m.source_start - previous_end;
                let new_range = if new_len > 0 {
                    Some(Mapping {
                        source_start: previous_end,
                        destination_start: previous_end,
                        len: new_len,
                    })
                } else {
                    None
                };

                previous_end = m.source_start + m.len;

                let trailer = if i + 1 == num_mappings {
                    Some(Mapping {
                        source_start: previous_end,
                        destination_start: previous_end,
                        len: u64::MAX,
                    })
                } else {
                    None
                };

                new_range
                    .into_iter()
                    .chain(std::iter::once(m))
                    .chain(trailer)
            })
            .collect();

        Ok(Self {
            name: name.to_string(),
            mappings,
        })
    }
}

impl FromStr for Mapping {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Example mapping
        // 50 98 2

        let mut parts = s.split_whitespace().map(str::trim);
        let destination_start = parts
            .next()
            .ok_or_else(|| anyhow!("Missing destination start"))
            .and_then(|s| s.parse().map_err(Into::into))
            .with_context(|| s.to_string())?;

        let source_start = parts
            .next()
            .ok_or_else(|| anyhow!("Missing source start"))
            .and_then(|s| s.parse().map_err(Into::into))
            .with_context(|| s.to_string())?;

        let len = parts
            .next()
            .ok_or_else(|| anyhow!("Missing len"))
            .and_then(|s| s.parse().map_err(Into::into))
            .with_context(|| s.to_string())?;

        Ok(Self {
            destination_start,
            source_start,
            len,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use anyhow::Result;

    const INPUT: &'static str = r#"
seeds: 79 14 55 13

seed-to-soil map:
50 98 2
52 50 48

soil-to-fertilizer map:
0 15 37
37 52 2
39 0 15

fertilizer-to-water map:
49 53 8
0 11 42
42 0 7
57 7 4

water-to-light map:
88 18 7
18 25 70

light-to-temperature map:
45 77 23
81 45 19
68 64 13

temperature-to-humidity map:
0 69 1
1 0 69

humidity-to-location map:
60 56 37
56 93 4"#;

    #[test]
    fn test_star_one() -> Result<()> {
        assert_eq!(star_one(INPUT)?, 35);

        Ok(())
    }

    #[test]
    fn test_star_two() -> Result<()> {
        assert_eq!(star_two(INPUT)?, 46);

        Ok(())
    }

    #[test]
    fn test_map_range() {
        let map = Map {
            name: "foo".to_string(),
            mappings: vec![Mapping {
                destination_start: 49,
                source_start: 53,
                len: 8,
            }],
        };

        let mut iter = map.map_range(57..68);
        assert_eq!(iter.next(), Some(53..57));
    }

    #[test]
    fn test_map_range_end() {
        let map = Map {
            name: "foo".to_string(),
            mappings: vec![Mapping {
                destination_start: 70,
                source_start: 70,
                len: u64::MAX,
            }],
        };

        let mut iter = map.map_range(82..83);
        assert_eq!(iter.next(), Some(82..83));
    }
}
