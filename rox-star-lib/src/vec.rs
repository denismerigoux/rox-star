
use std::ops::{Index, IndexMut};

pub struct RoxVec<T>(Vec<T>);

impl<T> RoxVec<T> {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn valid_index(&self, i:usize) -> bool {
        i < self.len()
    }
}

impl<T> Index<usize> for RoxVec<T> {
    type Output = T;
    //#[requires |self, i:usize| => self.valid_index(i)]
    fn index(&self, i:usize) -> &T {
        &self.0[i]
    }
}

impl<T> IndexMut<usize> for RoxVec<T> {
    //#[requires |self, i:usize| => self.valid_index(i)]
    fn index_mut(&mut self, i:usize) -> &mut T {
        &mut self.0[i]
    }
}
