/// This code is  inspired by Servo's bloom filter implementation
/// contained in the file [`servo/components/selector/bloom.rs`]

const KEY_SIZE: usize = 12;

const ARRAY_SIZE: usize = 1 << KEY_SIZE;
const KEY_MASK: u32 = (1 << KEY_SIZE) - 1;

pub struct BloomStorageU8 {
    counters: [u8; ARRAY_SIZE],
}

fn valid_index(i: usize) -> bool {
    i < ARRAY_SIZE
}

#[inline]
fn hash1(hash: u32) -> u32 {
    hash & KEY_MASK
}

#[inline]
fn hash2(hash: u32) -> u32 {
    (hash >> KEY_SIZE) & KEY_MASK
}

impl Default for BloomStorageU8 {
    fn default() -> Self {
        BloomStorageU8 {
            counters: [0; ARRAY_SIZE],
        }
    }
}


impl BloomStorageU8 {

    #[inline]
    fn first_slot_index(hash: u32) -> usize {
        hash1(hash) as usize
    }

    #[inline]
    fn second_slot_index(hash: u32) -> usize {
        hash2(hash) as usize
    }

    /// Creates a new bloom filter.
    #[inline]
    pub fn new() -> Self {
         Default::default()
    }

    #[inline]
    fn adjust_slot(&mut self, index: usize, increment: bool) {
        debug_assert!(valid_index(index));
        let slot = &mut self.counters[index];
        if *slot != 0xff {
            // full
            if increment {
                *slot += 1;
            } else {
                *slot -= 1;
            }
        }
    }

    #[inline]
    fn slot_is_empty(&self, index: usize) -> bool {
        debug_assert!(valid_index(index));
        self.counters[index] == 0
    }

    #[inline]
    pub fn clear(&mut self) {
        self.counters = [0;ARRAY_SIZE];
    }

    /// Inserts an item with a particular hash into the bloom filter.
    #[inline]
    pub fn insert_hash(&mut self, hash: u32) {
        self.adjust_first_slot(hash, true);
        self.adjust_second_slot(hash, true);
    }

    /// Removes an item with a particular hash from the bloom filter.
    #[inline]
    pub fn remove_hash(&mut self, hash: u32) {
        self.adjust_first_slot(hash, false);
        self.adjust_second_slot(hash, false);
    }

    /// Check whether the filter might contain an item with the given hash.
    /// This can sometimes return true even if the item is not in the filter,
    /// but will never return false for items that are actually in the filter.
    #[inline]
    pub fn might_contain_hash(&self, hash: u32) -> bool {
        !self.first_slot_is_empty(hash) && !self.second_slot_is_empty(hash)
    }

    #[inline]
    fn first_slot_is_empty(&self, hash: u32) -> bool {
        self.slot_is_empty(Self::first_slot_index(hash))
    }

    #[inline]
    fn second_slot_is_empty(&self, hash: u32) -> bool {
        self.slot_is_empty(Self::second_slot_index(hash))
    }

    #[inline]
    fn adjust_first_slot(&mut self, hash: u32, increment: bool) {
        self.adjust_slot(Self::first_slot_index(hash), increment)
    }

    #[inline]
    fn adjust_second_slot(&mut self, hash: u32, increment: bool) {
        self.adjust_slot(Self::second_slot_index(hash), increment)
    }

}

#[test]
fn create_and_insert_some_stuff() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_as_str(i: usize) -> u32 {
        let mut hasher = DefaultHasher::new();
        let s = i.to_string();
        s.hash(&mut hasher);
        let hash: u64 = hasher.finish();
        (hash >> 32) as u32 ^ (hash as u32)
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

    bf.clear();

    for i in 0_usize..2000 {
        assert!(!bf.might_contain_hash(hash_as_str(i)));
    }
}
