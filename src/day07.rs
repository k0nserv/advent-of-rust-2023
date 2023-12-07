use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;

use anyhow::{anyhow, Context, Result};

use crate::parse_lines;

pub fn star_one(input: &str) -> u64 {
    let mut hands: Vec<_> = parse_lines::<Hand<Card>>(input).collect();
    hands.sort();

    hands
        .into_iter()
        .enumerate()
        .map(|(i, h)| (i + 1) as u64 * h.bet)
        .sum()
}

pub fn star_two(input: &str) -> u64 {
    let mut hands: Vec<_> = parse_lines::<Hand<AltCard>>(input).collect();
    hands.sort();

    hands
        .into_iter()
        .enumerate()
        .map(|(i, h)| (i + 1) as u64 * h.bet)
        .sum()
}

#[derive(Debug, PartialEq, Eq)]
struct Hand<Kard> {
    cards: Vec<Kard>,
    kind: Kind,
    bet: u64,
}

impl<Kard: Ord> PartialOrd for Hand<Kard> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let kind_order = self.kind.cmp(&other.kind);
        if kind_order != Ordering::Equal {
            return Some(kind_order);
        }

        self.cards
            .iter()
            .zip(other.cards.iter())
            .find_map(|(c1, c2)| {
                let order = c1.cmp(&c2);
                if order != Ordering::Equal {
                    return Some(order);
                }

                None
            })
    }
}

impl<Kard: Ord> Ord for Hand<Kard> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(&other).unwrap()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Kind {
    HighCard,
    OnePair,
    TwoPair,
    ThreeOfAKind,
    FullHouse,
    FourOfAKind,
    FiveOfAKind,
}

impl Kind {
    const ALL: &[Self; 7] = &[
        Self::HighCard,
        Self::OnePair,
        Self::TwoPair,
        Self::ThreeOfAKind,
        Self::FullHouse,
        Self::FourOfAKind,
        Self::FiveOfAKind,
    ];
}

impl<Kard> FromStr for Hand<Kard>
where
    Kard: TryFrom<char, Error = anyhow::Error> + Kindable,
{
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (card, bet) = s
            .split_once(char::is_whitespace)
            .ok_or_else(|| anyhow!("Invalid hand, misisng whitespace"))
            .with_context(|| s.to_string())?;

        let cards: Vec<Kard> = card
            .chars()
            .map(TryInto::try_into)
            .collect::<anyhow::Result<_, _>>()?;

        let bet = bet.parse().with_context(|| s.to_string())?;
        let card_ref: &[Kard; 5] = cards.as_slice().try_into()?;
        let kind = Kard::kind(card_ref);

        Ok(Self { cards, kind, bet })
    }
}

// A, K, Q, J, T, 9, 8, 7, 6, 5, 4, 3, or 2
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
enum Card {
    Ace = 14,
    King = 13,
    Queen = 12,
    Jack = 11,
    Ten = 10,
    Nine = 9,
    Eight = 8,
    Seven = 7,
    Six = 6,
    Five = 5,
    Four = 4,
    Three = 3,
    Two = 2,
}

impl TryFrom<char> for Card {
    type Error = anyhow::Error;

    fn try_from(c: char) -> Result<Self, Self::Error> {
        match c {
            'A' => Ok(Card::Ace),
            'K' => Ok(Card::King),
            'Q' => Ok(Card::Queen),
            'J' => Ok(Card::Jack),
            'T' => Ok(Card::Ten),
            '9' => Ok(Card::Nine),
            '8' => Ok(Card::Eight),
            '7' => Ok(Card::Seven),
            '6' => Ok(Card::Six),
            '5' => Ok(Card::Five),
            '4' => Ok(Card::Four),
            '3' => Ok(Card::Three),
            '2' => Ok(Card::Two),
            _ => Err(anyhow!("Invalid card {c}")),
        }
    }
}

impl From<&[Card; 5]> for Kind {
    fn from(cards: &[Card; 5]) -> Self {
        let counts: HashMap<Card, usize> =
            cards.iter().fold(HashMap::with_capacity(5), |mut acc, c| {
                let e = acc.entry(*c).or_insert(0);
                *e += 1;

                acc
            });

        if counts.len() == 1 {
            return Kind::FiveOfAKind;
        }

        if counts.len() == 2 && counts.iter().any(|(_, c)| *c == 4) {
            return Kind::FourOfAKind;
        }

        if counts.len() == 2 && counts.iter().any(|(_, c)| *c == 3) {
            return Kind::FullHouse;
        }

        if counts.len() == 3 && counts.iter().any(|(_, c)| *c == 3) {
            return Kind::ThreeOfAKind;
        }

        if counts.len() == 3 && counts.iter().filter(|(_, c)| **c == 2).count() == 2 {
            return Kind::TwoPair;
        }

        if counts.len() == 4 && counts.iter().filter(|(_, c)| **c == 2).count() == 1 {
            return Kind::OnePair;
        }

        Kind::HighCard
    }
}

// A, K, Q, T, 9, 8, 7, 6, 5, 4, 3, 2, or J
// J is Joker
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
enum AltCard {
    Ace = 14,
    King = 13,
    Queen = 12,
    Ten = 10,
    Nine = 9,
    Eight = 8,
    Seven = 7,
    Six = 6,
    Five = 5,
    Four = 4,
    Three = 3,
    Two = 2,
    Joker = 1,
}

impl TryFrom<char> for AltCard {
    type Error = anyhow::Error;

    fn try_from(c: char) -> Result<Self, Self::Error> {
        match c {
            'A' => Ok(Self::Ace),
            'K' => Ok(Self::King),
            'Q' => Ok(Self::Queen),
            'J' => Ok(Self::Joker),
            'T' => Ok(Self::Ten),
            '9' => Ok(Self::Nine),
            '8' => Ok(Self::Eight),
            '7' => Ok(Self::Seven),
            '6' => Ok(Self::Six),
            '5' => Ok(Self::Five),
            '4' => Ok(Self::Four),
            '3' => Ok(Self::Three),
            '2' => Ok(Self::Two),
            _ => Err(anyhow!("Invalid card {c}")),
        }
    }
}

impl From<&[AltCard; 5]> for Kind {
    fn from(cards: &[AltCard; 5]) -> Self {
        let counts: HashMap<AltCard, usize> =
            cards.iter().fold(HashMap::with_capacity(5), |mut acc, c| {
                let e = acc.entry(*c).or_insert(0);
                *e += 1;

                acc
            });
        let num_jokers = *counts.get(&AltCard::Joker).unwrap_or(&0);
        let max_count = *counts
            .iter()
            .filter(|(c, _)| **c != AltCard::Joker)
            .map(|(_, c)| c)
            .max()
            .unwrap_or(&0);

        if max_count == 1 && num_jokers == 0 {
            return Kind::HighCard;
        }

        if max_count + num_jokers == 5 {
            return Kind::FiveOfAKind;
        }

        if max_count + num_jokers == 4 {
            return Kind::FourOfAKind;
        }

        // If you have two jokers in a full house potential hand, it becomes four of a kind.
        if num_jokers == 1 && max_count == 2 && counts.values().filter(|c| **c == 2).count() == 2 {
            return Kind::FullHouse;
        }

        if num_jokers == 0 && max_count == 3 && counts.values().any(|c| *c == 2) {
            return Kind::FullHouse;
        }

        if max_count + num_jokers == 3 {
            return Kind::ThreeOfAKind;
        }

        // If you have two jokers in potential two pair, it becomes three of a kind
        if num_jokers == 1 && max_count == 2 && counts.values().any(|c| *c == 1) {
            // Two of a kind
            return Kind::TwoPair;
        }

        if num_jokers == 0 && max_count == 2 && counts.values().filter(|c| **c == 2).count() == 2 {
            // Two of a kind
            return Kind::TwoPair;
        }

        // Anything else should be a pair, by elimination
        return Kind::OnePair;
    }
}

trait Kindable: Sized {
    fn kind(value: &[Self; 5]) -> Kind;
}

impl Kindable for Card {
    fn kind(value: &[Self; 5]) -> Kind {
        value.into()
    }
}

impl Kindable for AltCard {
    fn kind(value: &[Self; 5]) -> Kind {
        value.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const INPUT: &'static str = r#"
32T3K 765
T55J5 684
KK677 28
KTJJT 220
QQQJA 483"#;

    #[test]
    fn test_star_one() {
        assert_eq!(star_one(INPUT), 6440);
    }

    #[test]
    fn test_star_two() {
        assert_eq!(star_two(INPUT), 5905);
    }

    #[test]
    fn test_alt_card_kindable() {
        use AltCard::*;

        assert_eq!(
            AltCard::kind(&[Joker, Two, Two, Three, Three]),
            Kind::FullHouse
        );

        assert_eq!(
            AltCard::kind(&[Two, Five, Three, Four, Ace]),
            Kind::HighCard
        );

        assert_eq!(
            AltCard::kind(&[Joker, Two, Two, Three, Four]),
            Kind::ThreeOfAKind
        );

        assert_eq!(
            AltCard::kind(&[Joker, Two, Two, Two, Four]),
            Kind::FourOfAKind
        );

        assert_eq!(
            AltCard::kind(&[Joker, Two, Two, Two, Two]),
            Kind::FiveOfAKind
        );

        assert_eq!(
            AltCard::kind(&[Joker, Joker, Joker, Joker, Joker]),
            Kind::FiveOfAKind
        );

        assert_eq!(
            AltCard::kind(&[Joker, Five, Two, Three, Four]),
            Kind::OnePair
        );

        assert_eq!(
            AltCard::kind(&[Three, Three, Three, Two, Two]),
            Kind::FullHouse
        );

        assert_eq!(
            AltCard::kind(&[Three, Three, Five, Two, Two]),
            Kind::TwoPair
        );
    }
}
