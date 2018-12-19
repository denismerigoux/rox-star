
use std::ops::{Index, IndexMut};
use crate::integers::*;
use std::iter;

pub struct RoxArray<T : Clone> {
    contents: Vec<T>,
    len: Usize
}

impl<T : Clone> RoxArray<T> {
    pub fn new(len: Usize, default:T) -> RoxArray<T> {
        RoxArray {
            contents: iter::repeat(default).take(len.into_repr()).collect(),
            len: len
        }
    }

    pub fn len(&self) -> Usize {
        self.len
    }

    pub fn valid_index(&self, i:Usize) -> bool {
        i < self.len
    }
}

impl<T : Clone> Index<Usize> for RoxArray<T> {
    type Output = T;
    //#[requires |self, i:usize| => self.valid_index(i)]
    fn index(&self, i:Usize) -> &T {
        &self.contents[i.into_repr()]
    }
}

impl<T : Clone> IndexMut<Usize> for RoxArray<T> {
    //#[requires |self, i:usize| => self.valid_index(i)]
    fn index_mut(&mut self, i:Usize) -> &mut T {
        &mut self.contents[i.into_repr()]
    }
}
