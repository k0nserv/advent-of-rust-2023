use std::collections::{HashMap, HashSet};
use std::str::FromStr;

use anyhow::{anyhow, Context, Result};

use crate::math::lcm;

pub fn star_one(input: &str) -> Result<u64> {
    let (instructions_str, network_str) = input
        .split_once("\n\n")
        .ok_or_else(|| anyhow!("Invalid input {input}"))?;
    let instructions: Vec<Instruction> = instructions_str
        .chars()
        .filter(|c| !c.is_whitespace())
        .map(TryInto::try_into)
        .collect::<Result<_>>()?;
    let network: Network = network_str.parse()?;

    let start = Id("AAA".to_string());
    let end = Id("ZZZ".to_string());

    Ok(walk(
        &start,
        |i, _| i == &end,
        instructions.iter().cycle(),
        &network,
    ))
}

pub fn star_two(input: &str) -> Result<u64> {
    let (instructions_str, network_str) = input
        .split_once("\n\n")
        .ok_or_else(|| anyhow!("Invalid input {input}"))?;
    let instructions: Vec<Instruction> = instructions_str
        .chars()
        .filter(|c| !c.is_whitespace())
        .map(TryInto::try_into)
        .collect::<Result<_>>()?;
    let network: Network = network_str.parse()?;

    let path_lengths: Vec<_> = network
        .starts()
        .map(|s| {
            let mut ends: HashMap<&Id, (u64, Option<u64>)> = Default::default();
            let mut current_id = s;
            let mut steps = 0;

            for instruction in instructions.iter().cycle() {
                if current_id.is_terminal() {
                    let e = ends.entry(current_id).or_insert((steps, None));

                    if e.1.is_none() && e.0 != steps {
                        e.1 = Some(steps);
                        // First cycle found, time to stop
                        break;
                    }
                }
                current_id = step(current_id, *instruction, &network);
                steps += 1;
            }

            ends.into_iter()
                .filter_map(|(_, (s, e))| e.map(|e| e - s))
                .min()
                .unwrap()
        })
        .collect();

    // Naive approach no good.
    // Instead find shortest cycle per start, then LCM.
    // Consider four paths:
    //
    // 1. Takes 3 steps to reach end
    // 2. Takes 7 steps to reach end
    // 3. Takes 4 steps to reach end
    // 4. Takes 2 steps to reach end
    //
    // Path 1 cycles at 3 6 9 12 15 18 21 24 27 30 33 [...] 57 60 63 66 69 72 75 78 81 84
    //                                                                                 ^
    // Path 2 cycles at 7 14 21 28 35 42 49 56 63 70 77 84 91
    //                                                  ^
    // Path 3 cycles at 4 8 12 16 20 24 28 32 36 40 44 48 52 56 60 64 68 72 76 80 84
    //                                                                            ^
    // Path 4 cycles at 2 4 8 10 12 14 16 18 20 ...... 66 68 70 72 74 76 78 80 82 84
    //                                                                            ^
    // First ttme cycles line up is at 84 this is LCM(3, 7, 4, 2)

    Ok(lcm(&path_lengths))
}

fn walk<'a>(
    start: &Id,
    end: impl Fn(&Id, u64) -> bool,
    mut instructions: impl Iterator<Item = &'a Instruction>,
    network: &Network,
) -> u64 {
    let mut current_id = start;
    let mut steps = 0;

    while !end(&current_id, steps) {
        let instruction = instructions.next().unwrap();
        current_id = step(current_id, *instruction, network);
        steps += 1;
    }

    steps
}

fn step<'a, 'n>(start: &Id, instruction: Instruction, network: &'n Network) -> &'n Id {
    let current = network.find(&start);

    current.resolve(&instruction)
}

#[derive(Debug, Clone, Copy)]
enum Instruction {
    L,
    R,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct Id(String);
impl Id {
    fn is_terminal(&self) -> bool {
        self.0.ends_with("Z")
    }
}

#[derive(Debug)]
struct Network {
    nodes: HashMap<Id, Node>,
}

#[derive(Debug)]
struct Node {
    id: Id,
    left: Id,
    right: Id,
}

impl Network {
    fn find(&self, id: &Id) -> &Node {
        self.nodes
            .get(id)
            .unwrap_or_else(|| panic!("No node with id: {id:?}"))
    }

    fn starts(&self) -> impl Iterator<Item = &Id> {
        self.nodes.keys().filter(|n| n.0.ends_with("A"))
    }
}

impl Node {
    fn resolve(&self, instruction: &Instruction) -> &Id {
        match instruction {
            Instruction::L => &self.left,
            Instruction::R => &self.right,
        }
    }
}

impl TryFrom<char> for Instruction {
    type Error = anyhow::Error;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            'L' => Ok(Self::L),
            'R' => Ok(Self::R),
            _ => Err(anyhow!("Invalid instruction `{value}`")),
        }
    }
}

impl FromStr for Network {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let nodes = s
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(str::parse::<Node>)
            .map(|r| r.map(|n| (n.id.clone(), n)))
            .collect::<Result<_>>()?;

        Ok(Self { nodes })
    }
}

impl FromStr for Node {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> std::prelude::v1::Result<Self, Self::Err> {
        let (id, branches) = s
            .split_once('=')
            .ok_or_else(|| anyhow!("Missing = in node line"))
            .with_context(|| s.to_string())?;
        let (left, right) = branches
            .split_once(',')
            .ok_or_else(|| anyhow!("Missing = in node line"))
            .with_context(|| s.to_string())?;

        let left = Id(left.chars().filter(|c| c.is_ascii_alphanumeric()).collect());
        let right = Id(right
            .chars()
            .filter(|c| c.is_ascii_alphanumeric())
            .collect());

        Ok(Self {
            id: Id(id.trim().to_string()),
            left,
            right,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{star_one, star_two};
    use anyhow::Result;
    const INPUT_1: &'static str = r#"
LLR

AAA = (BBB, BBB)
BBB = (AAA, ZZZ)
ZZZ = (ZZZ, ZZZ)"#;

    const INPUT_2: &'static str = r#"
LR

11A = (11B, XXX)
11B = (XXX, 11Z)
11Z = (11B, XXX)
22A = (22B, XXX)
22B = (22C, 22C)
22C = (22Z, 22Z)
22Z = (22B, 22B)
XXX = (XXX, XXX)"#;

    #[test]
    fn test_star_one() -> Result<()> {
        assert_eq!(star_one(INPUT_1)?, 6);

        Ok(())
    }

    #[test]
    fn test_star_two() -> Result<()> {
        assert_eq!(star_two(INPUT_2)?, 6);

        Ok(())
    }
}
