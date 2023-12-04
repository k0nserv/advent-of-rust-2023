use std::collections::{HashMap, HashSet};
use std::str::FromStr;

use anyhow::{anyhow, Context};

use crate::parse_lines;

pub fn star_one(input: &str) -> u64 {
    let draws = parse_lines::<Draw>(input);

    draws.map(|d| d.score()).sum()
}

pub fn star_two(input: &str) -> u64 {
    let draws = parse_lines::<Draw>(input).map(|d| (d.card.id, d));
    let mut extras: HashMap<u64, u64> = Default::default();
    let mut total = 0;

    for (i, d) in draws {
        let count = d.matching_numbers();
        let extra_count = *extras.get(&i).unwrap_or(&0);

        for j in (i + 1)..(i + 1 + count) {
            let e = extras.entry(j).or_default();
            *e += 1 + extra_count;
        }

        let new_cards = 1 + extra_count;
        total += new_cards;
    }

    total
}

#[derive(Debug)]
struct Draw {
    card: Card,
    winners: HashSet<u64>,
}

#[derive(Debug)]
struct Card {
    id: u64,
    numbers: HashSet<u64>,
}

impl Draw {
    fn score(&self) -> u64 {
        let count = self.matching_numbers();
        if count == 0 {
            return 0;
        }

        2_u64.pow(count as u32 - 1)
    }

    fn matching_numbers(&self) -> u64 {
        self.card
            .numbers
            .iter()
            // NB: The number of entries in this set is so small that a `Vec` might outperform it
            .filter(|n| self.winners.contains(n))
            .count() as u64
    }
}

impl FromStr for Draw {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (left, right) = s
            .split_once('|')
            .ok_or_else(|| anyhow!("Missing `|` in input"))
            .with_context(|| s.to_string())?;

        let card = left.trim().parse()?;
        let winners = right
            .trim()
            .split_whitespace()
            .map(str::parse)
            .collect::<Result<HashSet<_>, _>>()?;

        Ok(Self { card, winners })
    }
}

impl FromStr for Card {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (left, right) = s
            .split_once(':')
            .ok_or_else(|| anyhow!("Missing `|` in input"))
            .with_context(|| s.to_string())?;

        let id = left
            .split_whitespace()
            .next_back()
            .ok_or_else(|| anyhow!("Missing card id"))
            .with_context(|| s.to_string())
            .and_then(|s| s.parse().map_err(Into::into))?;

        let numbers = right
            .trim()
            .split_whitespace()
            .map(str::parse)
            .collect::<Result<HashSet<_>, _>>()?;

        Ok(Self { id, numbers })
    }
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};
    const INPUT: &'static str = r#"
Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53
Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19
Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1
Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83
Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36
Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11"#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 13);
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT), 30);
    }
}
