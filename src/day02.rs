use std::str::FromStr;

use anyhow::{anyhow, Context};

use crate::parse_lines;

pub fn star_one(input: &str) -> u64 {
    let games = parse_lines::<Game>(input);
    let cons = Set {
        red: 12,
        green: 13,
        blue: 14,
    };

    games.filter(|g| g.satisfies(cons)).map(|g| g.id).sum()
}

pub fn star_two(input: &str) -> u64 {
    let games = parse_lines::<Game>(input);

    games.map(|g| g.min_set()).map(Set::power).sum()
}

#[derive(Debug)]
struct Game {
    id: u64,
    sets: Vec<Set>,
}

#[derive(Default, Debug, Clone, Copy)]
struct Set {
    red: u64,
    green: u64,
    blue: u64,
}

impl Game {
    fn satisfies(&self, constraint: Set) -> bool {
        self.sets.iter().all(|s| {
            s.blue <= constraint.blue && s.green <= constraint.green && s.red <= constraint.red
        })
    }

    fn min_set(&self) -> Set {
        self.sets.iter().fold(Set::default(), |acc, s| Set {
            red: s.red.max(acc.red),
            green: s.green.max(acc.green),
            blue: s.blue.max(acc.blue),
        })
    }
}

impl Set {
    fn power(self) -> u64 {
        self.red * self.green * self.blue
    }
}

// Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
impl FromStr for Game {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts = s
            .split_once(':')
            .ok_or_else(|| anyhow!("Game should contain a `:`"))?;

        let id = parts
            .0
            .split_whitespace()
            .next_back()
            .ok_or_else(|| anyhow!("Game should contain an ID"))
            .and_then(|s| s.parse().context("Game ID should be parsable"))?;

        let sets = parts
            .1
            .split(';')
            .map(str::parse::<Set>)
            .collect::<Result<_, _>>()?;

        Ok(Self { id, sets })
    }
}

// 3 blue, 4 red
impl FromStr for Set {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut set = Self::default();
        let splits = s.split(',');

        for split in splits {
            let mut parts = split.split_whitespace();
            let count = parts
                .next()
                .expect("Draw to contain a count and color")
                .parse()
                .expect("Draw count to parsable");
            let color = parts.next().expect("Draw to contain a color").trim();

            match color {
                "blue" => set.blue = count,
                "green" => set.green = count,
                "red" => set.red = count,
                _ => return Err(anyhow!("Unknown color {color}")),
            }
        }

        Ok(set)
    }
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};
    const INPUT: &'static str = r#"
Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green"#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 8);
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT), 2286);
    }
}
