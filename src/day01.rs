use std::borrow::Cow;
use std::collections::HashMap;

const DIGITS: [&str; 9] = [
    "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
];

pub fn star_one(input: &str) -> u32 {
    input
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(|l| {
            let first = l
                .chars()
                .find_map(|c| c.to_digit(10))
                .expect("At least one number");
            let last = l
                .chars()
                .rev()
                .find_map(|c| c.to_digit(10))
                .expect("At least one number");

            first * 10 + last
        })
        .sum()
}

pub fn star_two(input: &str) -> u32 {
    let mappings: HashMap<_, _> = DIGITS
        .iter()
        .enumerate()
        .map(|(idx, d)| (d.to_string(), (idx + 1) as u32))
        .collect();
    let reverse_mappings: HashMap<_, _> = DIGITS
        .iter()
        .enumerate()
        .map(|(idx, d)| (d.chars().rev().collect::<String>(), (idx + 1) as u32))
        .collect();

    input
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(|l| {
            let first = (0..l.len())
                .find_map(|i| find_digit(|| l.chars().skip(i), &mappings))
                .expect("At least one number");
            let last = (0..l.len())
                .find_map(|i| find_digit(|| l.chars().rev().skip(i), &reverse_mappings))
                .expect("At least one number");

            first * 10 + last
        })
        .sum()
}

fn find_digit<F, I>(f: F, mappings: &HashMap<String, u32>) -> Option<u32>
where
    F: Fn() -> I,
    I: Iterator<Item = char>,
{
    let mut i = f();
    if let Some(d) = i.next().and_then(|c| c.to_digit(10)) {
        return Some(d);
    }

    for (d, v) in mappings.iter() {
        let i = f();
        if d.chars().zip(i).all(|(a, b)| a == b) {
            return Some(*v);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};
    const INPUT: &'static str = r#"
1abc2
pqr3stu8vwx
a1b2c3d4e5f
treb7uchet
    "#;

    const INPUT_2: &'static str = r#"
two1nine
eightwothree
abcone2threexyz
xtwone3four
4nineeightseven2
zoneight234
7pqrstsixteen
    "#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 142);
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT_2), 281);
    }
}
