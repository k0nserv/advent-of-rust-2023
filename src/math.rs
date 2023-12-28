use std::fmt;
use std::hash::Hash;
use std::ops::{Add, Neg, Sub};

#[derive(Copy, Clone, Hash, PartialEq, Eq, Ord, PartialOrd)]
pub struct Vector2<T> {
    pub y: T,
    pub x: T,
}

impl<T> Vector2<T> {
    pub fn new(x: T, y: T) -> Self {
        Self { x, y }
    }
}

impl<T: Default> Default for Vector2<T> {
    fn default() -> Self {
        Self {
            x: T::default(),
            y: T::default(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Vector2<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<Vector2 x={:?} y={:?} >", self.x, self.y)
    }
}

impl<T: Add<Output = T>> Add for Vector2<T> {
    type Output = Vector2<T>;

    fn add(self, rhs: Vector2<T>) -> Self::Output {
        Vector2::<T> {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl<T: Sub<Output = T>> Sub for Vector2<T> {
    type Output = Vector2<T>;

    fn sub(self, rhs: Vector2<T>) -> Self::Output {
        Vector2::<T> {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl<T: Neg<Output = T> + Hash + PartialEq> Neg for Vector2<T> {
    type Output = Vector2<T>;

    fn neg(self) -> Self::Output {
        Vector2::<T> {
            x: -self.x,
            y: -self.y,
        }
    }
}

pub trait Abs {
    type Output;

    fn abs(self) -> Self::Output;
}

macro_rules! define_abs {
    ($T:ident) => {
        impl Abs for $T {
            type Output = $T;

            fn abs(self) -> Self::Output {
                self.abs()
            }
        }
    };
}

define_abs!(isize);

impl<T: Abs<Output = T> + Sub<Output = T> + Add<Output = T>> Vector2<T> {
    pub fn manhattan_distance(self, other: Self) -> T {
        (self.x - other.x).abs() + (self.y - other.y).abs()
    }
}

pub fn gcm(nums: &[u64]) -> u64 {
    fn recurse(a: u64, rest: &[u64]) -> u64 {
        if rest.len() == 1 {
            return gcd_base(a, rest[0]);
        }

        return gcd_base(a, recurse(rest[0], &rest[1..]));
    }

    recurse(nums[0], &nums[1..])
}
fn gcd_base(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }

    a
}

pub fn lcm(nums: &[u64]) -> u64 {
    fn base(mut a: u64, mut b: u64) -> u64 {
        a * b / gcd_base(a, b)
    }

    fn recurse(a: u64, rest: &[u64]) -> u64 {
        if rest.len() == 1 {
            return base(a, rest[0]);
        }

        return base(a, recurse(rest[0], &rest[1..]));
    }

    recurse(nums[0], &nums[1..])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gcm() {
        assert_eq!(gcm(&[48, 18]), 6);
        assert_eq!(gcm(&[48, 18, 24, 6]), 6);
        assert_eq!(gcm(&[8, 12, 17]), 1);
    }

    #[test]
    fn test_lcm() {
        assert_eq!(lcm(&[4, 3, 7, 2]), 84);
    }
}
