use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::hash::Hasher;
use std::str::FromStr;

use anyhow::anyhow;
use either::Either;
use itertools::Itertools;

use crate::mem::{Arena, Idx};

// This solution is very messy...
// Revisit and replace with simpler version or DFA

pub fn star_one(input: &str) -> usize {
    // Build a graph, traverse it backwards with dynamic programming
    let map: Map = input.parse().expect("Parsable input");
    let graphs = map.rows.iter().map(|r| (Graph::build(r), r));

    graphs
        .map(|(g, r)| (r, g.traverse_valid_count()))
        .map(|(_, c)| c)
        .sum()
}

pub fn star_two(input: &str) -> usize {
    // Build a graph, unfold it, traverse it backwards with dynamic programming
    let map = input.parse::<Map>().expect("Parsable input");
    let graphs = map.rows.iter().map(|r| Graph::build(r).times(5));

    graphs.map(|g| g.traverse_valid_count()).sum()
}

#[derive(Debug)]
struct Graph {
    arena: Arena<Node>,
    origins: Vec<Idx>,
    terminals: Vec<Idx>,
    meta: Vec<u64>,
}

#[derive(Debug, Clone)]
struct Node {
    parents: BTreeSet<Idx>,
    count: u64,
    kind: Spring,
}

impl Graph {
    fn build(row: &Row) -> Graph {
        #[derive(Default)]
        struct Builder {
            arena: Arena<Node>,
            origins: Option<Vec<Idx>>,
            terminals: Option<Vec<Idx>>,
            /// Mapping from fixed springs and the generated nodes, used to dedupe.
            cache: HashMap<usize, [Option<Idx>; 2]>,
            meta: Vec<u64>,
        }

        impl Builder {
            fn new(meta: Vec<u64>) -> Self {
                Self {
                    meta,
                    ..Default::default()
                }
            }

            fn recruse(&mut self, springs: &[Group], spring_idx: usize, parent_idx: Option<Idx>) {
                if spring_idx == springs.len() {
                    unreachable!();
                }
                let current = springs[spring_idx];

                let idxs = if current.spring == Spring::Operational
                    || current.spring == Spring::Damaged
                {
                    if let Some([Some(idx), None]) = self.cache.get(&spring_idx) {
                        self.arena[*idx].parents.insert(parent_idx.unwrap());

                        Either::Left(*idx)
                    } else {
                        // Operational or damaged
                        let node = Node {
                            parents: parent_idx.into_iter().collect(),
                            count: current.count,
                            kind: current.spring,
                        };
                        let node_idx = self.arena.insert(node);
                        assert!(!self.cache.contains_key(&spring_idx));
                        self.cache.insert(spring_idx, [Some(node_idx), None]);

                        Either::Left(node_idx)
                    }
                } else {
                    if let Some([Some(left_idx), Some(right_idx)]) = self.cache.get(&spring_idx) {
                        self.arena[*left_idx].parents.insert(parent_idx.unwrap());
                        self.arena[*right_idx].parents.insert(parent_idx.unwrap());

                        Either::Right([*left_idx, *right_idx])
                    } else {
                        // Unknown, generate two nodes
                        let left = Node {
                            parents: parent_idx.into_iter().collect(),
                            count: 1,
                            kind: Spring::Operational,
                        };
                        let right = Node {
                            parents: parent_idx.into_iter().collect(),
                            count: 1,
                            kind: Spring::Damaged,
                        };

                        let left_idx = self.arena.insert(left);
                        let right_idx = self.arena.insert(right);
                        self.cache
                            .insert(spring_idx, [Some(left_idx), Some(right_idx)]);

                        Either::Right([left_idx, right_idx])
                    }
                };
                if self.origins.is_none() {
                    // Set start nodes
                    self.origins = Some(idxs.either(|l| vec![l], |r| r.to_vec()));
                }

                if spring_idx == springs.len() - 1 {
                    let idxs = idxs.as_ref().either(|l| vec![*l], |r| r.to_vec());
                    // This was the last group, stop processing
                    self.terminals = Some(idxs.clone());

                    return;
                }

                match idxs {
                    Either::Left(l) => self.recruse(springs, spring_idx + 1, Some(l)),
                    Either::Right([l, r]) => {
                        self.recruse(springs, spring_idx + 1, Some(l));
                        self.recruse(springs, spring_idx + 1, Some(r));
                    }
                }
            }
        }

        impl From<Builder> for Graph {
            fn from(
                Builder {
                    arena,
                    origins,
                    terminals,
                    meta,
                    ..
                }: Builder,
            ) -> Self {
                Self {
                    arena,
                    origins: origins.expect("To have at least one origin"),
                    terminals: terminals.expect("To have at least one terminal"),
                    meta,
                }
            }
        }

        let mut builder = Builder::new(row.meta.clone());
        builder.recruse(&row.groups, 0, None);

        builder.into()
    }

    /// Multiply this graph by fuzing it with a copy of itself, joining using an unknown node
    /// between the copies
    fn times(mut self, count: usize) -> Self {
        // 1. Copy self
        // 2. Fix up relationships
        // 3. Add two connection nodes
        // 4. Fuse previous terminals to connection nodes
        // 5. Fuse new origins to new connection nodes

        let original_graph = self.arena.all_items().map(|(i, _)| i).collect_vec();
        let mut current_terminals = self.terminals.clone();
        for _ in 0..count - 1 {
            // Build a copy of all nodes, with no parent links
            // Keep mapping from old idx to new to repair parent links
            let cache = {
                // Need `collect` to drop borrow on arena
                let new_nodes: Vec<_> = original_graph
                    .iter()
                    .map(|idx| {
                        let node = &self.arena[*idx];
                        (
                            idx,
                            Node {
                                parents: BTreeSet::new(),
                                kind: node.kind,
                                count: node.count,
                            },
                        )
                    })
                    .collect();
                let mut cache = HashMap::with_capacity(new_nodes.len());
                for (old_idx, node) in new_nodes {
                    let new_idx = self.arena.insert(node);

                    cache.insert(old_idx, new_idx);
                }

                cache
            };
            let mut stack: Vec<_> = self.terminals.iter().map(|t| (*t, None)).collect();

            while let Some((old_idx, child)) = stack.pop() {
                if let Some(child) = child {
                    let new_node = &mut self.arena[*cache.get(&child).unwrap()];
                    // Fix up the parent link
                    new_node.parents.insert(*cache.get(&old_idx).unwrap());
                }

                for parent in self.arena[old_idx].parents.iter() {
                    stack.push((*parent, Some(old_idx)));
                }
            }

            // Add two nodes for new unknown, set parents to old terminals
            let join_left = Node {
                parents: current_terminals.iter().copied().collect(),
                kind: Spring::Damaged,
                count: 1,
            };
            let join_right = Node {
                parents: current_terminals.iter().copied().collect(),
                kind: Spring::Operational,
                count: 1,
            };

            let join_left_idx = self.arena.insert(join_left);
            let join_right_idx = self.arena.insert(join_right);
            current_terminals = self
                .terminals
                .iter()
                .map(|i| *cache.get(i).unwrap())
                .collect();

            // Connect new and old graph
            for old_origin in self.origins.iter() {
                let new_origin = cache.get(old_origin).unwrap();

                self.arena[*new_origin].parents.insert(join_left_idx);
                self.arena[*new_origin].parents.insert(join_right_idx);
            }
        }

        let meta_count = self.meta.len();
        Self {
            arena: self.arena,
            origins: self.origins, // Origins remain the same
            terminals: current_terminals,
            meta: self
                .meta
                .into_iter()
                .cycle()
                .take(meta_count * count)
                .collect(),
        }
    }

    /// Count _distinct, valid_ paths through the graph.
    pub fn traverse_valid_count(&self) -> usize {
        let mut result = 0;

        for terminal in &self.terminals {
            let current_meta = self.meta.last().copied();
            let meta: Vec<_> = self.meta.iter().copied().rev().collect();
            let mut cache: HashMap<Key, usize> = HashMap::with_capacity(10_000);
            result += self.recurse_traverse_valid_count(*terminal, &meta, current_meta, &mut cache);
        }

        result
    }

    fn recurse_traverse_valid_count<'m>(
        &self,
        node_idx: Idx,
        mut meta: &'m [u64],
        mut current_meta: Option<u64>,
        cache: &mut HashMap<Key<'m>, usize>,
    ) -> usize {
        let key = Key {
            node_idx,
            meta,
            current_meta,
        };

        if let Some(result) = cache.get(&key) {
            return *result;
        }

        let node = &self.arena[node_idx];

        match (node.kind, current_meta.as_mut()) {
            // Invalid path, consumed too many damaged
            (Spring::Damaged, Some(m)) if *m < node.count => return 0,
            // Invalid path, consumed all damaged groups
            (Spring::Damaged, None) => return 0,

            // Valid path, consume part of the current group
            (Spring::Damaged, Some(m)) if *m >= node.count => {
                *m -= node.count;
            }
            // Valid path, current group ran out
            (Spring::Operational, Some(0)) => {
                meta = &meta[1..];
                current_meta = meta.iter().next().copied();
            }
            // Invalid path, operational after having consumed only a partial group
            (Spring::Operational, Some(m))
                if meta.iter().next().map(|a| a != m).unwrap_or(false) =>
            {
                return 0;
            }
            (Spring::Operational, _) => {}
            (Spring::Unknown, _) => unreachable!(),
            (Spring::Damaged, Some(_)) => unreachable!("The compiler can't figure this out"),
        }
        let reached_end = node.parents.is_empty();
        let meta_exhausted =
            meta.is_empty() || current_meta.map(|m| m == 0).unwrap() && meta.len() == 1;

        if reached_end && meta_exhausted {
            return 1;
        }

        if reached_end && !meta_exhausted {
            return 0;
        }

        let mut result = 0;
        for parent in &node.parents {
            let sub_result = self.recurse_traverse_valid_count(*parent, meta, current_meta, cache);
            result += sub_result;
        }
        cache.insert(key, result);

        result
    }

    fn iterative_traverse_valid_count<'m>(
        &self,
        start_idx: Idx,
        meta: &'m [u64],
        cache: &mut HashMap<Key<'m>, usize>,
    ) -> usize {
        let mut final_result = 0;
        let mut stack = vec![(start_idx, Some(meta[0]), meta)];

        while let Some((node_idx, mut current_meta, mut meta)) = stack.pop() {
            let key = Key {
                node_idx,
                meta,
                current_meta,
            };

            if let Some(result) = cache.get(&key) {
                final_result += *result;
                continue;
            }

            let node = &self.arena[node_idx];

            match (node.kind, current_meta.as_mut()) {
                // Invalid path, consumed too many damaged
                (Spring::Damaged, Some(m)) if *m < node.count => continue,
                // Invalid path, consumed all damaged groups
                (Spring::Damaged, None) => continue,

                // Valid path, consume part of the current group
                (Spring::Damaged, Some(m)) if *m >= node.count => {
                    *m -= node.count;
                }
                // Valid path, current group ran out
                (Spring::Operational, Some(0)) => {
                    meta = &meta[1..];
                    current_meta = meta.iter().next().copied();
                }
                // Invalid path, operational after having consumed only a partial group
                (Spring::Operational, Some(m))
                    if meta.iter().next().map(|a| a != m).unwrap_or(false) =>
                {
                    return 0;
                }
                (Spring::Operational, _) => {}
                (Spring::Unknown, _) => unreachable!(),
                (Spring::Damaged, Some(_)) => unreachable!("The compiler can't figure this out"),
            }
            let reached_end = node.parents.is_empty();
            let meta_exhausted =
                meta.is_empty() || current_meta.map(|m| m == 0).unwrap() && meta.len() == 1;

            if reached_end && meta_exhausted {
                return 1;
            }

            if reached_end && !meta_exhausted {
                continue;
            }

            for parent in &node.parents {
                stack.push((*parent, current_meta, meta));
            }
        }

        final_result
    }

    /// Produce a DOT representation of this graph for debugging
    fn to_dot(&self) -> anyhow::Result<String> {
        use std::fmt::Write;

        let mut output = String::new();
        writeln!(output, "digraph G {{")?;
        writeln!(output, "    orientation=L")?;

        for (idx, n) in self.arena.all_items() {
            writeln!(output, r#"    {}[label="{}({})"]"#, idx, n.kind, n.count)?;
        }
        writeln!(output, "")?;

        for (idx, n) in self.arena.all_items() {
            for parent in n.parents.iter() {
                writeln!(output, "    {} -> {}", idx, parent)?;
            }
        }

        writeln!(output, "}}")?;

        Ok(output)
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
struct Key<'a> {
    node_idx: Idx,
    meta: &'a [u64],
    current_meta: Option<u64>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Spring {
    Operational,
    Damaged,
    Unknown,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Map {
    rows: Vec<Row>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Row {
    groups: Vec<Group>,
    meta: Vec<u64>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Group {
    count: u64,
    spring: Spring,
}

impl FromStr for Map {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let rows = s
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(FromStr::from_str)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self { rows })
    }
}

impl FromStr for Row {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (springs, meta) = s
            .split_once(char::is_whitespace)
            .ok_or_else(|| anyhow!("Invalid row {s}"))?;

        let groups = iter_to_groups(springs.chars().map(TryFrom::try_from))?;

        let meta = meta
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(str::parse)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self { groups, meta })
    }
}

impl TryFrom<char> for Spring {
    type Error = anyhow::Error;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '#' => Ok(Self::Damaged),
            '.' => Ok(Self::Operational),
            '?' => Ok(Self::Unknown),
            _ => Err(anyhow!("Invalid spring {value}")),
        }
    }
}

fn iter_to_groups<E>(mut iter: impl Iterator<Item = Result<Spring, E>>) -> Result<Vec<Group>, E> {
    let (mut result, last) = iter.fold_ok((vec![], None), |(mut result, previous), current| {
        let Some((previous, count)) = previous else {
            return (result, Some((current, 1)));
        };

        if previous != current || previous == Spring::Unknown {
            result.push(Group {
                count,
                spring: previous,
            });
            return (result, Some((current, 1)));
        }

        return (result, Some((previous, count + 1)));
    })?;
    if let Some((spring, count)) = last {
        result.push(Group { count, spring });
    }

    Ok(result)
}

impl fmt::Display for Row {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_rowish(f, self.groups.iter().copied(), self.meta.iter().copied())
    }
}

impl fmt::Display for Spring {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Spring::Operational => write!(f, "."),
            Spring::Damaged => write!(f, "#"),
            Spring::Unknown => write!(f, "?"),
        }
    }
}

fn write_rowish(
    f: &mut dyn fmt::Write,
    groups: impl IntoIterator<Item = Group>,
    meta: impl IntoIterator<Item = u64>,
) -> fmt::Result {
    for g in groups {
        for _ in 0..g.count {
            write!(f, "{}", g.spring)?;
        }
    }

    write!(f, " ")?;
    let iter = meta.into_iter();

    for m in iter {
        write!(f, "{m}, ")?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const INPUT: &'static str = r#"
???.### 1,1,3
.??..??...?##. 1,1,3
?#?#?#?#?#?#?#? 1,3,1,6
????.#...#... 4,1,1
????.######..#####. 1,6,5
?###???????? 3,2,1"#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 21);
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT), 525152);
    }

    #[test]
    fn test_traverse_valid_count() {
        let map: Map = "?###???????? 3,2,1".parse().expect("To be parsable");

        let graph = Graph::build(&map.rows[0]);
        assert_eq!(graph.traverse_valid_count(), 10);
    }
}
