use std::marker::PhantomData;
use std::str::FromStr;

use anyhow::{anyhow, Context, Result};
use either::Either;

pub fn star_one(input: &str) -> Result<u64> {
    solve::<BadKern>(input)
}

pub fn star_two(input: &str) -> Result<u64> {
    solve::<GoodKern>(input)
}

fn solve<K: Kerning>(input: &str) -> Result<u64> {
    let document: Document<K> = input.parse()?;

    Ok(document
        .races
        .iter()
        .map(|r| high(r.time, r.distance + 1) - low(r.time, r.distance + 1) + 1)
        .product())
}

// Solve Tx-x^2 = D
// Where T=time, D=duration

/// Compute low root
fn low(time: u64, distance: u64) -> u64 {
    let c = time as f64;
    let y = distance as f64;

    (1.0 / 2.0 * (c - (c.powf(2.0) - 4.0 * y).sqrt())).ceil() as u64
}

/// Compute high root
fn high(time: u64, distance: u64) -> u64 {
    let c = time as f64;
    let y = distance as f64;

    (1.0 / 2.0 * ((c.powf(2.0) - 4.0 * y).sqrt() + c)).floor() as u64
}

trait Kerning {
    fn bad_kern() -> bool;
}

#[derive(Debug)]
struct BadKern;
#[derive(Debug)]
struct GoodKern;

impl Kerning for BadKern {
    fn bad_kern() -> bool {
        true
    }
}

impl Kerning for GoodKern {
    fn bad_kern() -> bool {
        false
    }
}

#[derive(Debug)]
struct Document<K> {
    races: Vec<Race>,

    _phantom: PhantomData<K>,
}

#[derive(Debug)]
struct Race {
    time: u64,
    distance: u64,
}

impl<K: Kerning> FromStr for Document<K> {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut lines = s.lines().map(str::trim).filter(|l| !l.is_empty());

        let first = lines
            .next()
            .ok_or_else(|| anyhow!("Missing first line"))
            .with_context(|| s.to_string())?;
        let second = lines
            .next()
            .ok_or_else(|| anyhow!("Missing second line"))
            .with_context(|| s.to_string())?;

        let times = parse_line(first, "Time", K::bad_kern())?;
        let distances = parse_line(second, "Distance", K::bad_kern())?;

        let races = times
            .zip(distances)
            .map(|(t, d)| {
                t.and_then(|t| {
                    d.map(|d| Race {
                        time: t,
                        distance: d,
                    })
                })
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(Self {
            races,
            _phantom: PhantomData,
        })
    }
}

fn parse_line<'l>(
    line: &'l str,
    expected_label: &str,
    bad_kerning: bool,
) -> Result<impl Iterator<Item = Result<u64>> + 'l> {
    let (label, rest) = line
        .split_once(':')
        .ok_or_else(|| anyhow!("Line not parsable, missing label"))
        .with_context(|| line.to_string())?;

    if label.trim() != expected_label {
        return Err(anyhow!(
            "Line did not have {expected_label} label, found label {label}"
        ))
        .with_context(|| line.to_string());
    }

    let iter = rest
        .split_whitespace()
        .map(str::parse)
        .map(|r| r.map_err(Into::into));

    if bad_kerning {
        Ok(Either::Left(iter))
    } else {
        let v = iter
            .rev()
            .fold(Ok((0_u64, 0_u32)), |acc, v| {
                acc.and_then(|acc| {
                    v.map(|v| {
                        let value = acc.0 + v * 10_u64.pow(acc.1);

                        (value, acc.1 + (v as f64).log10().floor() as u32 + 1)
                    })
                })
            })
            .map(|(v, _)| v);

        Ok(Either::Right(std::iter::once(v)))
    }
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};

    use anyhow::Result;

    const INPUT: &'static str = r#"
Time:      7  15   30
Distance:  9  40  200"#;

    #[test]
    fn test_star_one() -> Result<()> {
        assert_eq!(star_one(INPUT)?, 288);

        Ok(())
    }

    #[test]
    fn test_star_two() -> Result<()> {
        assert_eq!(star_two(INPUT)?, 71503);

        Ok(())
    }
}
