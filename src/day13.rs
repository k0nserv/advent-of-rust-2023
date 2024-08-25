use std::fmt;
use std::str::FromStr;

use anyhow::anyhow;

pub fn star_one(input: &str) -> usize {
    let patterns = parse(input);

    patterns
        .iter()
        .map(|p| {
            let result = p.find_reflection(false);

            if result == 0 {
                println!("Found no reflections in:\n{p:?}");
            }

            result
        })
        .sum()
}

pub fn star_two(input: &str) -> usize {
    let patterns = parse(input);

    patterns
        .iter()
        .map(|p| {
            let result = p.find_reflection(true);

            if result == 0 {
                println!("Found no reflections in:\n{p:?}");
            }

            result
        })
        .sum()
}

fn parse(input: &str) -> Vec<Pattern> {
    input
        .split("\n\n")
        .map(str::parse)
        .collect::<Result<_, _>>()
        .expect("Parsable input")
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Location {
    Ash,
    Rock,
}

struct Pattern {
    // Pattern from input
    pattern: Vec<Vec<Location>>,
    // Transposed pattern
    transpose: Vec<Vec<Location>>,
}

impl Pattern {
    fn find_reflection(&self, fix_smudges: bool) -> usize {
        if let Some(rows) = Self::find_reflection_in(&self.pattern, fix_smudges).map(|x| x * 100) {
            return dbg!(rows);
        };
        if let Some(columns) = Self::find_reflection_in(&self.transpose, fix_smudges) {
            return dbg!(columns);
        }

        0
    }

    fn find_reflection_in(pattern: &[Vec<Location>], fix_smudges: bool) -> Option<usize> {
        let num_lines = pattern.len() as isize;
        let mid_point = num_lines / 2 as isize;

        (0..=num_lines).find_map(|i| {
            let top = if i % 2 == 0 {
                (mid_point + i / 2) as usize
            } else {
                (mid_point - (i / 2)) as usize
            };
            let bottom = (top + 1) as usize;

            let (valid, fixed_smudge) = (0..=top).rev().zip(bottom..num_lines as usize).fold(
                (None, false),
                |mut acc, (t, b)| {
                    // `Iterator::all` returns `true` for empty iterators, we don't want this,
                    // hence `fold`.
                    let value = acc.0.get_or_insert(true);
                    if !*value {
                        return acc;
                    }

                    let mut diffed = diff(pattern[t].as_slice(), pattern[b].as_slice());
                    let smudge = diffed.next();

                    // If we have a smudge and we haven't already fixed one
                    if fix_smudges {
                        let single_smude = diffed.next().is_none();
                        let fixable = smudge.is_some() && single_smude;

                        if fixable {
                            acc.1 = true;
                        }

                        *value = *value && (smudge.is_none() || fixable);
                    } else {
                        *value = *value && smudge.is_none();
                    }

                    acc
                },
            );

            if fix_smudges {
                valid.and_then(|x| (x && fixed_smudge).then_some(bottom))
            } else {
                valid.and_then(|x| x.then_some(bottom))
            }
        })
    }
}

fn diff<'a, T: Eq>(a: &'a [T], b: &'a [T]) -> impl Iterator<Item = usize> + 'a {
    a.iter()
        .zip(b.iter())
        .enumerate()
        .flat_map(|(i, (a, b))| if a != b { Some(i) } else { None })
}

impl FromStr for Pattern {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let pattern: Vec<Vec<_>> = s
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(|l| {
                l.chars()
                    .map(TryInto::try_into)
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<_, _>>()?;
        let transpose: Vec<Vec<_>> = (0..pattern[0].len())
            .map(|x| (0..pattern.len()).map(|y| pattern[y][x]).collect())
            .collect();
        assert!(pattern.len() == transpose[0].len());
        assert!(pattern[0].len() == transpose.len());

        Ok(Self { pattern, transpose })
    }
}

impl TryFrom<char> for Location {
    type Error = anyhow::Error;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '.' => Ok(Self::Ash),
            '#' => Ok(Self::Rock),
            _ => Err(anyhow!("Unrecgonised location {value}")),
        }
    }
}

impl fmt::Debug for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_pattern(f, &self.pattern)?;
        writeln!(f, "")?;
        write_pattern(f, &self.transpose)?;

        Ok(())
    }
}

fn write_pattern(f: &mut fmt::Formatter<'_>, pattern: &[Vec<Location>]) -> fmt::Result {
    for row in pattern {
        for col in row {
            write!(f, "{:?}", col)?;
        }
        writeln!(f, "")?;
    }

    Ok(())
}

impl fmt::Debug for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Location::Ash => write!(f, "."),
            Location::Rock => write!(f, "#"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};

    const INPUT: &'static str = r#"
#.##..##.
..#.##.#.
##......#
##......#
..#.##.#.
..##..##.
#.#.##.#.

#...##..#
#....#..#
..##..###
#####.##.
#####.##.
..##..###
#....#..#"#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 405);
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT), 400);
    }
}
