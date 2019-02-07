use crate::*;
use std::fmt::Display;
use secret_integers::*;

pub fn fill<F, B : Default + Clone>(len:usize, f: F) -> Vec<B> where F: Fn(usize) -> B {
    let mut a = Vec::with_capacity(len);
    a.resize(len, Default::default());
    for i in 0..a.len() {
        a[i] = f(i);
    };
    a
}

pub fn classify_u8s(v: &[u8]) -> Vec<U8> {
    v.iter().map(|x| U8::classify(*x)).collect()
}

pub fn classify_u32s(v: &[u32]) -> Vec<U32> {
    v.iter().map(|x| U32::classify(*x)).collect()
}

pub fn format_bytes<T : Display>(v: &Vec<T>) -> String {
        let mut comma_separated = String::new();

        for num in v {
            comma_separated.push_str(&format!("{}", num));
        }
        comma_separated
    }
