extern crate rox_star_lib;

use rox_star_lib::*;

const BLOCK_SIZE : usize = 64;
type State = [U32; 16];
//#[refinement (|x| x.len() == 32)]
type Key = Vec<U8>;
//#[refinement (|x| x.len() == 12)]
type Nonce = Vec<U8>;
type Block = [U8;64];
type Constants = [u32;4];
type Index = usize;
type RotVal = u32;

fn line(a:Index, b:Index, d:Index, s:RotVal, m: &mut State) {
    m[a] = m[a] + m[b];
    m[d] = m[d] ^ m[a];
    m[d] = m[d].rotate_left(s);
}


fn quarter_round(a:Index, b:Index, c:Index, d:Index, m: &mut State) {
    line(a,b,d,16,m);
    line(c,d,b,12,m);
    line(a,b,d,8,m);
    line(c,d,b,7,m);
}

fn double_round(m: &mut State) {
    quarter_round(0,4,8,12,m);
    quarter_round(1,5,9,13,m);
    quarter_round(2,6,10,14,m);
    quarter_round(3,7,11,15,m);

    quarter_round(0,5,10,15,m);
    quarter_round(1,6,11,12,m);
    quarter_round(2,7,8,13,m);
    quarter_round(3,4,9,14,m);
}

const CONSTANTS: Constants = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

fn chacha20_init(k:&Key, counter:U32, nonce:&Nonce) -> State {
    let mut st = [U32::classify(0u32);16];
    st[0..4].copy_from_slice(&classify_u32s(&CONSTANTS));
    st[4..12].copy_from_slice(u8s_to_uint32s_le(k).as_slice());
    st[12] = counter;
    st[13..16].copy_from_slice(u8s_to_uint32s_le(nonce).as_slice());
    st
}

fn chacha20_core(st:&mut State) {
    let mut working_state = st.clone();
    for _ in 0..10 {
        double_round(&mut working_state);
    }
    for i in 0..16 {
        st[i] += working_state[i];
    }
}

fn chacha20(k:&Key, counter:U32, nonce:&Nonce) -> State {
    let mut st = chacha20_init(k, counter, nonce);
    chacha20_core(&mut st);
    st
}

fn chacha20_block(k:&Key, counter:U32, nonce:&Nonce) -> Block {
    let st = chacha20(k, counter, nonce);
    let mut block = [U8::classify(0u8);BLOCK_SIZE];
    block.copy_from_slice(u8s_from_uint32s_le(&st).as_slice());
    block
}

fn xor_block(block: &Block, key_block: &Block) -> Block {
    let v_out = fill(BLOCK_SIZE, &|i| block[i] ^ key_block[i]);
    let mut out = [U8::classify(0u8);BLOCK_SIZE];
    out.copy_from_slice(v_out.as_slice());
    out
}

fn chacha20_counter_mode(key: &Key, counter:U32, nonce:&Nonce, msg:&Vec<U8>) -> Vec<U8> {
    let mut blocks : Vec<[U8;BLOCK_SIZE]> = msg.chunks(BLOCK_SIZE).map(|block| {
        let mut new_block = [U8::classify(0u8);BLOCK_SIZE];
        new_block[0..block.len()].copy_from_slice(block);
        new_block
    }).collect();
    let nb_blocks = blocks.len();
    let mut key_block : [U8; BLOCK_SIZE];
    let mut ctr = counter;
    for i in 0..blocks.len() - 1 {
        key_block = chacha20_block(key, ctr, nonce);
        blocks[i] = xor_block(&blocks[i], &key_block);
        ctr += U32::classify(1u32);
    }
    let last = &mut blocks[nb_blocks - 1];
    key_block = chacha20_block(key, ctr, nonce);
    *last = xor_block(last, &key_block);
    blocks.iter().map(|block| block.to_vec()).flatten().take(msg.len()).collect()
}

pub fn chacha20_encrypt(key: &Key, counter: U32, nonce:&Nonce, msg: &Vec<U8>) -> Vec<U8> {
    chacha20_counter_mode(key, counter, nonce, msg)
}

pub fn chacha20_decrypt(key: &Key, counter: U32, nonce:&Nonce, msg: &Vec<U8>) -> Vec<U8> {
    chacha20_counter_mode(key, counter, nonce, msg)
}

#[test]
fn chacha20_test() {
    let plaintext = classify_u8s(&vec![
        0x4c,0x61,0x64,0x69,0x65,0x73,0x20,0x61,
        0x6e,0x64,0x20,0x47,0x65,0x6e,0x74,0x6c,
        0x65,0x6d,0x65,0x6e,0x20,0x6f,0x66,0x20,
        0x74,0x68,0x65,0x20,0x63,0x6c,0x61,0x73,
        0x73,0x20,0x6f,0x66,0x20,0x27,0x39,0x39,
        0x3a,0x20,0x49,0x66,0x20,0x49,0x20,0x63,
        0x6f,0x75,0x6c,0x64,0x20,0x6f,0x66,0x66,
        0x65,0x72,0x20,0x79,0x6f,0x75,0x20,0x6f,
        0x6e,0x6c,0x79,0x20,0x6f,0x6e,0x65,0x20,
        0x74,0x69,0x70,0x20,0x66,0x6f,0x72,0x20,
        0x74,0x68,0x65,0x20,0x66,0x75,0x74,0x75,
        0x72,0x65,0x2c,0x20,0x73,0x75,0x6e,0x73,
        0x63,0x72,0x65,0x65,0x6e,0x20,0x77,0x6f,
        0x75,0x6c,0x64,0x20,0x62,0x65,0x20,0x69,
        0x74,0x2e]);
    let ciphertext = classify_u8s(&vec![
        0x6e,0x2e,0x35,0x9a,0x25,0x68,0xf9,0x80,
        0x41,0xba,0x07,0x28,0xdd,0x0d,0x69,0x81,
        0xe9,0x7e,0x7a,0xec,0x1d,0x43,0x60,0xc2,
        0x0a,0x27,0xaf,0xcc,0xfd,0x9f,0xae,0x0b,
        0xf9,0x1b,0x65,0xc5,0x52,0x47,0x33,0xab,
        0x8f,0x59,0x3d,0xab,0xcd,0x62,0xb3,0x57,
        0x16,0x39,0xd6,0x24,0xe6,0x51,0x52,0xab,
        0x8f,0x53,0x0c,0x35,0x9f,0x08,0x61,0xd8,
        0x07,0xca,0x0d,0xbf,0x50,0x0d,0x6a,0x61,
        0x56,0xa3,0x8e,0x08,0x8a,0x22,0xb6,0x5e,
        0x52,0xbc,0x51,0x4d,0x16,0xcc,0xf8,0x06,
        0x81,0x8c,0xe9,0x1a,0xb7,0x79,0x37,0x36,
        0x5a,0xf9,0x0b,0xbf,0x74,0xa3,0x5b,0xe6,
        0xb4,0x0b,0x8e,0xed,0xf2,0x78,0x5e,0x42,
        0x87,0x4d
        ]);
    let key = classify_u8s(&vec![
        0u8,1u8,2u8,3u8,4u8,5u8,6u8,7u8,
        8u8,9u8,10u8,11u8,12u8,13u8,14u8,15u8,
        16u8,17u8,18u8,19u8,20u8,21u8,22u8,23u8,
        24u8,25u8,26u8,27u8,28u8,29u8,30u8,31u8
        ]);
    let nonce = classify_u8s(&vec![0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4a,0x0,0x0,0x0,0x0]);
    let computed_ciphertext = chacha20_encrypt(&key, U32::classify(1u32), &nonce, &plaintext);
    for (i, (x1,x2)) in ciphertext.iter().zip(computed_ciphertext).enumerate() {
        assert_eq!(x1.declassify::<u8>(), x2.declassify::<u8>(), "at index {:?}", i);
    }
}
