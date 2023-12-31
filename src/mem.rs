use std::fmt;
use std::ops::{Index, IndexMut};

pub struct Arena<T> {
    storage: Vec<T>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Idx(usize);

impl<T> Arena<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            storage: Vec::with_capacity(capacity),
        }
    }

    pub fn insert(&mut self, value: T) -> Idx {
        let idx = self.storage.len();
        self.storage.push(value);

        Idx(idx)
    }

    pub fn storage(&self) -> &[T] {
        &self.storage
    }

    pub fn all_items(&self) -> impl Iterator<Item = (Idx, &T)> {
        self.storage.iter().enumerate().map(|(i, t)| (Idx(i), t))
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self { storage: vec![] }
    }
}

impl<T> fmt::Debug for Arena<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Arena")
            .field("storage_len", &self.storage.len())
            .finish()
    }
}

impl fmt::Display for Idx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T> Index<Idx> for Arena<T> {
    type Output = T;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.storage[index.0]
    }
}

impl<T> IndexMut<Idx> for Arena<T> {
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.storage[index.0]
    }
}
