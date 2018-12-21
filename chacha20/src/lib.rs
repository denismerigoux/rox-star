extern crate rox_star_lib;

use rox_star_lib::*;


const BLOCK_SIZE : usize = 64;
type State = [U32; 16];
type Key = [U8;32];
type Nonce = [U8;12];
type Block = [U8;64];
type Constants = [U32;4];
type Index = usize;
type RotVal = u32;

fn line(a:Index, b:Index, d:Index, s:RotVal, &m:&State) -> State {
    let mut m = m.clone();
    m[a] = m[a] + m[b];
    m[d] = m[d] ^ m[a];
    m[d] = m[d].rotate_left(s);
    m
}

fn quarter_round(a:Index, b:Index, c:Index, d:Index, &m:&State) -> State {
    let m = line(a,b,d,16,&m);
    let m = line(c,d,b,12,&m);
    let m = line(a,b,d,8,&m);
    let m = line(c,d,b,7,&m);
    m
}

fn double_round(&m: &State) -> State {
    let m = quarter_round(0,4,8,12,&m);
    let m = quarter_round(1,5,9,13,&m);
    let m = quarter_round(2,6,10,14,&m);
    let m = quarter_round(3,7,11,15,&m);

    let m = quarter_round(0,5,10,15,&m);
    let m = quarter_round(1,6,11,12,&m);
    let m = quarter_round(2,7,8,13,&m);
    let m = quarter_round(3,4,9,14,&m);
    m
}

const CONSTANTS: Constants = [U32(0x61707865), U32(0x3320646e), U32(0x79622d32), U32(0x6b206574)];

fn chacha20_init(k:&Key, counter:U32, nonce:&Nonce) -> State {
    let mut st = [U32(0);16];
    (&mut st[0..4]).copy_from_slice(&CONSTANTS);
    (&mut st[4..12]).copy_from_slice(u8s_to_uint32s_le(k).as_slice());
    st[12] = counter;
    (&mut st[13..16]).copy_from_slice(u8s_to_uint32s_le(nonce).as_slice());
    st
}

fn chacha20_core(st:&State) -> State {
    let mut working_state = st.clone();
    for _ in 0..10 {
        working_state = double_round(&working_state);
    }
    for i in 0..16 {
        working_state[i] += st[i];
    }
    working_state
}

fn chacha20(k:&Key, counter:U32, nonce:&Nonce) -> State {
    chacha20_core(&chacha20_init(k, counter, nonce))
}

fn chacha20_block(k:&Key, counter:U32, nonce:&Nonce) -> Block {
    let st = chacha20(k, counter, nonce);
    let mut block = [U8(0);BLOCK_SIZE];
    (&mut block).copy_from_slice(u8s_from_uint32s_le(&st).as_slice());
    block
}

fn xor_block(block: &Block, key_block: &Block) -> Block {
    let mut out = block.clone();
    for i in 0..BLOCK_SIZE {
        out[i] ^= key_block[i]
    }
    out
}

fn chacha20_counter_mode(key: &Key, counter:U32, nonce:&Nonce, msg:&[U8]) -> Vec<U8> {
    let mut blocks : Vec<[U8;BLOCK_SIZE]> = msg.chunks(BLOCK_SIZE).map(|block| {
        let mut new_block = [U8(0);BLOCK_SIZE];
        (&mut new_block).copy_from_slice(block);
        new_block
    }).collect();
    let mut last = blocks[blocks.len() - 1];
    blocks.remove(blocks.len() - 1);
    let mut key_block : [U8; BLOCK_SIZE];
    let mut last_block = [U8(0); BLOCK_SIZE];
    let mut ctr = counter;
    for i in 0..blocks.len() {
        key_block = chacha20_block(key, ctr, nonce);
        blocks[i] = xor_block(&blocks[i], &key_block);
        ctr += U32(1);
    }
    key_block = chacha20_block(key, ctr, nonce);
    (&mut last_block).copy_from_slice(&last);
    last_block = xor_block(&last_block, &key_block);
    let last_len = last.len();
    (&mut last).copy_from_slice(&last_block[..last_len]);
    blocks.push(last);
    let blocks : Vec<U8> = blocks.iter().map(|block| block.to_vec()).flatten().collect();
    blocks
}

pub fn chacha20_encrypt(key: &Key, counter: U32, nonce:&Nonce, msg: &[U8]) -> Vec<U8> {
    chacha20_counter_mode(key, counter, nonce, msg)
}

pub fn chacha20_decrypt(key: &Key, counter: U32, nonce:&Nonce, msg: &[U8]) -> Vec<U8> {
    chacha20_counter_mode(key, counter, nonce, msg)
}
