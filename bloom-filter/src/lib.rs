/// This code is  inspired by Servo's bloom filter implementation
/// contained in the file
/// [`servo/components/selector/bloom.rs`](https://github.com/servo/servo/blob/master/components/selectors/bloom.rs)

extern crate rox_star_lib;

use rox_star_lib::*;

fn key_size() -> Usize { 12.into() }
fn array_size() -> Usize { Usize::from_repr(1) << key_size() }
fn key_mask() -> Usize { (Usize::from_repr(1) << key_size()) - 1.into() }

pub struct BloomStorageU8 {
    //#[invariant (| arr | => arr.len() == ARRAY_SIZE)]
    counters: RoxArray<U8>,
}

fn valid_index(i: Usize) -> bool {
    i < array_size()
}

#[inline]
fn hash1(hash: U32) -> U32 {
    hash & key_mask().into()
}

#[inline]
fn hash2(hash: U32) -> U32 {
    (hash >> key_size().into()) & key_mask().into()
}

impl Default for BloomStorageU8 {
    fn default() -> Self {
        BloomStorageU8 {
            counters: RoxArray::new(array_size(),0.into()),
        }
    }
}


impl BloomStorageU8 {

    #[inline]
    fn first_slot_index(hash: U32) -> Usize {
        hash1(hash).into()
    }

    #[inline]
    fn second_slot_index(hash: U32) -> Usize {
        hash2(hash).into()
    }

    #[inline]
    fn slot_value(&self, index: Usize) -> U8 {
        verif_pre!(valid_index(index));
        self.counters[index]
    }

    #[inline]
    fn slot_is_empty(&self, index: Usize) -> bool {
        verif_pre!(valid_index(index));
        self.slot_value(index) == 0.into()
    }

    #[inline]
    fn first_slot_is_empty(&self, hash: U32) -> bool {
        self.slot_is_empty(Self::first_slot_index(hash))
    }

    #[inline]
    fn second_slot_is_empty(&self, hash: U32) -> bool {
        self.slot_is_empty(Self::second_slot_index(hash))
    }

    /// Check whether the filter might contain an item with the given hash.
    /// This can sometimes return true even if the item is not in the filter,
    /// but will never return false for items that are actually in the filter.
    #[inline]
    pub fn might_contain_hash(&self, hash: U32) -> bool {
        !self.first_slot_is_empty(hash) && !self.second_slot_is_empty(hash)
    }

    #[inline]
    fn adjust_slot(&mut self, index: Usize, increment: bool) {
        verif_pre!(valid_index(index));
        let slot = &mut self.counters[index];
        if *slot != 0xff.into() {
            // full
            if increment {
                *slot = *slot + 1.into();
            } else {
                *slot = *slot - 1.into();
            }
        }
    }

    #[inline]
    fn adjust_first_slot(&mut self, hash: U32, increment: bool) {
        self.adjust_slot(Self::first_slot_index(hash), increment)
    }

    #[inline]
    fn adjust_second_slot(&mut self, hash: U32, increment: bool) {
        self.adjust_slot(Self::second_slot_index(hash), increment)
    }

    /// Inserts an item with a particular hash into the bloom filter.
    #[inline]
    pub fn insert_hash(&mut self, hash: U32) {
        self.adjust_first_slot(hash, true);
        self.adjust_second_slot(hash, true);
    }

    /// Removes an item with a particular hash from the bloom filter.
    #[inline]
    pub fn remove_hash(&mut self, hash: U32) {
        self.adjust_first_slot(hash, false);
        self.adjust_second_slot(hash, false);
    }

    /// Creates a new bloom filter.
    #[inline]
    pub fn new() -> Self {
         Default::default()
    }

}

#[test]
fn create_and_insert_some_stuff() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_as_str(i: usize) -> U32 {
        let mut hasher = DefaultHasher::new();
        let s = i.to_string();
        s.hash(&mut hasher);
        let hash: u64 = hasher.finish();
        U32::from_repr((hash >> 32) as u32 ^ (hash as u32))
    }

    let mut bf = BloomStorageU8::new();

    for i in 0_usize..1000 {
        bf.insert_hash(hash_as_str(i));
    }

    for i in 0_usize..1000 {
        assert!(bf.might_contain_hash(hash_as_str(i)));
    }

    let false_positives = (1001_usize..2000)
        .filter(|i| bf.might_contain_hash(hash_as_str(*i)))
        .count();

    assert!(false_positives < 190, "{} is not < 190", false_positives); // 19%.

    for i in 0_usize..100 {
        bf.remove_hash(hash_as_str(i));
    }

    for i in 100_usize..1000 {
        assert!(bf.might_contain_hash(hash_as_str(i)));
    }

    let false_positives = (0_usize..100)
        .filter(|i| bf.might_contain_hash(hash_as_str(*i)))
        .count();

    assert!(false_positives < 20, "{} is not < 20", false_positives); // 20%.

}
