use anyhow::Result;

pub fn star_one(input: &str) -> i64 {
    input
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(|l| extrapolate(l, Method::Last))
        .map(Result::unwrap)
        .sum()
}

pub fn star_two(input: &str) -> i64 {
    input
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(|l| extrapolate(l, Method::First))
        .map(Result::unwrap)
        .sum()
}

fn extrapolate(line: &str, method: Method) -> Result<i64> {
    // Use two vectors of equal size and swap them after each extrapolation, avoids needless
    // allocation
    let mut a = line
        .split_whitespace()
        .map(str::parse)
        .map(|r| r.map_err(Into::into))
        .collect::<Result<Vec<_>>>()?;
    let mut b = vec![0; a.len()];

    let mut final_values: Vec<_> = match method {
        Method::First => a.first().into_iter().copied().collect(),
        Method::Last => a.last().into_iter().copied().collect(),
    };

    let mut current_len = a.len();
    let mut current = &mut a;
    let mut difference = &mut b;

    loop {
        let diff_len = current_len - 1;
        for (i, (x, y)) in current
            .iter()
            .zip(current.iter().skip(1))
            .enumerate()
            .take(diff_len)
        {
            difference[i] = y - x;
        }

        match method {
            Method::First => {
                final_values.push(difference[0]);
            }
            Method::Last => {
                final_values.push(difference[current_len - 2]);
            }
        }
        if difference.iter().take(diff_len).all(|x| x == &0) {
            break;
        }

        std::mem::swap(&mut current, &mut difference);
        current_len -= 1;
    }

    match method {
        Method::First => Ok(final_values.into_iter().rev().fold(0, |acc, v| v - acc)),
        Method::Last => Ok(final_values.into_iter().rev().fold(0, |acc, v| acc + v)),
    }
}

enum Method {
    First,
    Last,
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};
    const INPUT: &'static str = r#"
0 3 6 9 12 15
1 3 6 10 15 21
10 13 16 21 30 45"#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 114);
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT), 2);
    }
}
