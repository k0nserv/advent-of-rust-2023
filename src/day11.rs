use std::collections::{HashMap, HashSet};

use itertools::iproduct;

use crate::math::Vector2;

pub fn star_one(input: &str) -> u64 {
    solve(input, 1)
}

pub fn star_two(input: &str, expansion: u64) -> u64 {
    solve(input, expansion)
}

fn solve(input: &str, expansion: u64) -> u64 {
    let map = Map::parse(input, expansion);
    map.shortest_path_sum()
}

type Coordinate = Vector2<isize>;

#[derive(Debug)]
struct Map {
    galaxies: Vec<Coordinate>,
    width: isize,
    height: isize,
}

impl Map {
    fn parse(input: &str, expansion: u64) -> Self {
        let grid: Vec<Vec<_>> = input
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(|l| l.chars().collect())
            .collect();
        let expand_y: Vec<_> = (0..grid.len())
            .filter(|y| grid[*y].iter().all(|c| c == &'.'))
            .collect();
        let expand_x: Vec<_> = (0..grid[0].len())
            .filter(|x| grid.iter().all(|r| r[*x] == '.'))
            .collect();

        let y_extra = &mut 0;
        let expand_x_ref = &expand_x;
        let expand_y_ref = &expand_y;
        let galaxies = grid
            .iter()
            .enumerate()
            .flat_map(move |(y, row)| {
                if expand_y_ref.contains(&y) {
                    *y_extra += expansion as isize;
                }

                let y_extra = *y_extra;
                let mut x_extra = 0;
                row.iter().enumerate().filter_map(move |(x, c)| {
                    if expand_x_ref.contains(&x) {
                        x_extra += expansion as isize;
                        return None;
                    }

                    let x_extra = x_extra;
                    (c == &'#')
                        .then(move || Coordinate::new(x_extra + x as isize, y_extra + y as isize))
                })
            })
            .collect();

        Self {
            galaxies,
            width: (grid[0].len() + expand_x.len()) as isize,
            height: (grid.len() + expand_y.len()) as isize,
        }
    }

    fn shortest_path_sum(&self) -> u64 {
        let mut computed: HashSet<(Coordinate, Coordinate)> = Default::default();
        iproduct!(self.galaxies.iter(), self.galaxies.iter())
            .filter_map(|(a, b)| {
                let key = if a < b { (*a, *b) } else { (*b, *a) };

                if computed.contains(&key) {
                    return None;
                }
                computed.insert(key);

                Some(a.manhattan_distance(*b) as u64)
            })
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};

    // ....1........
    // .........2...
    // 3............
    // .............
    // .............
    // ........4....
    // .5...........
    // .##.........6
    // ..##.........
    // ...##........
    // ....##...7...
    // 8....9.......
    const INPUT: &'static str = r#"
...#......
.......#..
#.........
..........
......#...
.#........
.........#
..........
.......#..
#...#....."#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 374)
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT, 99), 8410);
        assert_eq!(star_two(INPUT, 9), 1030);
    }
}
