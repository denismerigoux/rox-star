use crate::*;
use std::fmt::Display;
use secret_integers::*;

pub fn u8s_to_uint32s_le(bytes: &[U8]) -> Vec<U32> {
    verif_pre!(bytes.len() % 4 == 0);
    bytes
        .chunks(4)
        .map(|chunk| {
            U32::classify(unsafe {
                std::mem::transmute::<[u8; 4], u32>([
                    U8::declassify(chunk[0]),
                    U8::declassify(chunk[1]),
                    U8::declassify(chunk[2]),
                    U8::declassify(chunk[3])
                ]).to_le()
            })
        })
        .collect::<Vec<U32>>()
}

pub fn u8s_from_uint32s_le(ints: &[U32]) -> Vec<U8> {
    ints.iter().map(|int| {
        let int = U32::declassify(*int);
        let bytes : [u8; 4] = unsafe { std::mem::transmute::<u32, [u8;4]>(int.to_le()) };
        let secret_bytes : Vec<U8> = bytes.iter().map(|x| U8::classify(*x)).collect();
        secret_bytes
    }).flatten().collect()
}

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
