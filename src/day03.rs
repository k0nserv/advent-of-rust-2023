use std::collections::HashSet;
use std::ops::Range;

pub fn star_one(input: &str) -> u64 {
    assert!(
        input.is_ascii(),
        "This solution is only valid for ASCII strings"
    );
    let parts = extract_parts(input);
    let relevant_parts: HashSet<_> = find_symbols(input, &parts)
        .flat_map(|s| s.parts.into_iter())
        .collect();

    relevant_parts.into_iter().map(|p| p.number).sum()
}

pub fn star_two(input: &str) -> u64 {
    assert!(
        input.is_ascii(),
        "This solution is only valid for ASCII strings"
    );
    let parts = extract_parts(input);
    find_symbols(input, &parts)
        .filter(|s| s.symbol == '*' && s.parts.len() == 2)
        .map(|s| s.parts.iter().map(|p| p.number).product::<u64>())
        .sum()
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
struct Part {
    /// Zero indexed line.
    line: usize,

    /// Byte range within the line.
    range: Range<usize>,

    number: u64,
}

#[derive(Debug)]
struct Symbol {
    /// The symbol
    symbol: char,
    /// Adjacent parts
    parts: HashSet<Part>,
}

fn extract_parts(input: &str) -> Vec<Vec<Part>> {
    input
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .enumerate()
        .map(|(lidx, l)| {
            let mut chars = l.chars().enumerate();
            let mut parts = vec![];

            loop {
                let Some((range, number)) = to_num(
                    chars
                        .by_ref()
                        .skip_while(|(_, c)| !c.is_ascii_digit())
                        .map_while(|(idx, c)| c.to_digit(10).map(|d| (idx, d))),
                ) else {
                    break;
                };

                parts.push(Part {
                    line: lidx,
                    range,
                    number,
                })
            }

            parts
        })
        .collect()
}

/// Find all the symbols, and their adjacent parts
fn find_symbols<'s>(input: &'s str, parts: &'s [Vec<Part>]) -> impl Iterator<Item = Symbol> + 's {
    let clean_lines = input.lines().map(str::trim).filter(|l| !l.is_empty());

    clean_lines.enumerate().flat_map(move |(lidx, line)| {
        line.chars().enumerate().filter_map(move |(i, c)| {
            if c.is_ascii_digit() || c == '.' {
                // Not a symbol
                return None;
            }

            let parts = adjacent_parts(i, lidx, parts);
            Some(Symbol { symbol: c, parts })
        })
    })
}

/// Determine all the parts adjacent to a specific location, that of a symbol.
fn adjacent_parts(x: usize, y: usize, parts: &[Vec<Part>]) -> HashSet<Part> {
    const DIRS: &[(isize, isize); 8] = &[
        (-1, 1),
        (0, 1),
        (1, 1),
        (1, 0),
        (1, -1),
        (0, -1),
        (-1, -1),
        (-1, 0),
    ];
    let mut adjacent_parts = HashSet::new();

    for dir in DIRS {
        let l = ((x as isize) - dir.0, (y as isize) - dir.1);
        if l.0 < 0 || l.1 < 0 || (l.1 as usize) >= parts.len() {
            continue;
        }
        let x = l.0 as usize;
        let y = l.1 as usize;

        let line = &parts[y];

        for part in line.iter() {
            if part.range.contains(&x) {
                adjacent_parts.insert(part.clone());
            }
        }
    }

    adjacent_parts
}

/// Build a u64 from an iterator over [`char`] also return the byte range of the number within the
/// string.
/// **Note:** Numbers larger than 100 digits not supported
fn to_num(mut iter: impl Iterator<Item = (usize, u32)>) -> Option<(Range<usize>, u64)> {
    // 100 digits ought to be enough
    let mut digits = [None; 100];
    let mut i = 0;
    let mut range: Option<Range<usize>> = None;

    for (idx, d) in iter {
        digits[i] = Some(d as u64);
        i += 1;

        let r = range.get_or_insert_with(|| idx..idx + 1);
        *r = r.start..idx + 1;
    }

    let range = range?;

    let number = (0..i).rev().fold(0, |acc, idx| {
        acc + (digits[idx].unwrap() * 10_u64.pow((i as u32) - (idx as u32) - 1))
    });

    Some((range, number))
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};
    const INPUT: &'static str = r#"
467..114..
...*......
..35..633.
......#...
617*......
.....+.58.
..592.....
......755.
...$.*....
.664.598.."#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 4361);
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT), 467835);
    }
}
