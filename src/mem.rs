use std::ops::{Index, IndexMut};

struct Arena<T> {
    storage: Vec<T>,
}

#[derive(Clone, Copy)]
struct Idx(usize);

impl<T> Arena<T> {
    pub fn insert(&mut self, value: T) -> Idx {
        self.storage.push(value);

        Idx(self.storage.len())
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
