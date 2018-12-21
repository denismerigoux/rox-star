use crate::*;

pub fn u8s_to_uint32s_le(bytes: &[U8]) -> Vec<U32> {
    verif_pre!(bytes.len() % 4 == 0);
    bytes
        .chunks(4)
        .map(|chunk| {
            U32(unsafe {
                std::mem::transmute::<[u8; 4], u32>([
                    chunk[3].0, chunk[2].0, chunk[1].0, chunk[0].0,
                ])
            })
        })
        .collect::<Vec<U32>>()
}

pub fn u8s_from_uint32s_le(ints: &[U32]) -> Vec<U8> {
    ints.iter().map(|int| {
        let U32(int) = int;
        let bytes : [u8; 4] = unsafe { std::mem::transmute::<u32, [u8;4]>(int.to_le()) };
        let secret_bytes : Vec<U8> = bytes.iter().map(|x| U8(*x)).collect();
        secret_bytes
    }).flatten().collect()
}
