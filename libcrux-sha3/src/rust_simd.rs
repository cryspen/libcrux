mod sha3_arm64;
use sha3_arm64::*;


#[inline(always)]
fn squeeze_first_block2(s: &KeccakStateX2, out0: &mut [u8], out1: &mut [u8]) {
    squeeze2(s, out0, out1)
}

#[inline(always)]
fn squeeze_next_block2(s: &mut KeccakStateX2, out0: &mut [u8], out1: &mut [u8]) {
    keccakf1600(s);
    squeeze2(s, out0, out1)
}

#[inline(always)]
pub fn squeeze_first_three_blocks2(s: &mut KeccakStateX2, out0: &mut [u8], out1: &mut [u8]) {
    squeeze_first_block2(s, out0, out1);
    squeeze_next_block2(s, &mut out0[s.rate..2*s.rate], &mut out1[s.rate..2*s.rate]);
    squeeze_next_block2(s, &mut out0[2*s.rate..3*s.rate], &mut out1[2*s.rate..3*s.rate])
}

#[inline(always)]
fn squeeze_last2(mut s: KeccakStateX2, out0: &mut [u8], out1: &mut [u8]) {
    let mut b0 = [0u8; 200];
    let mut b1 = [0u8; 200];
    squeeze_next_block2(&mut s, &mut b0, &mut b1);
    out0.copy_from_slice(&b0[0..out0.len()]);
    out1.copy_from_slice(&b1[0..out1.len()]);
}

#[inline(always)]
fn squeeze_first_and_last2(s: &KeccakStateX2, out0: &mut [u8], out1: &mut [u8]) {
    let mut b0 = [0u8; 200];
    let mut b1 = [0u8; 200];
    squeeze_first_block2(s, &mut b0, &mut b1);
    out0.copy_from_slice(&b0[0..out0.len()]);
    out1.copy_from_slice(&b1[0..out1.len()]);
}

#[inline(always)]
fn keccak(rate: usize, p: u8, data0: &[u8], data1: &[u8], out0: &mut [u8], out1: &mut [u8]) {
    debug_assert!(data0.len() == data1.len());
    debug_assert!(out0.len() == out1.len());
    let mut s = KeccakStateX2::new(rate, p);
    for i in 0..data0.len()/rate {
        absorb_block2(&mut s, &data0[i*rate..(i+1)*rate], &data1[i*rate..(i+1)*rate]);
    }
    let rem = data0.len() % rate;
    absorb_final2(&mut s, &data0[data0.len()-rem..data0.len()], &data1[data1.len()-rem..data1.len()]);

    let blocks = out0.len()/rate;
    let last = out0.len() - out0.len()%rate;

    if blocks == 0 {
        squeeze_first_and_last2(&s, out0, out1)
    } else {
        squeeze_first_block2(&s, out0, out1);
        for i in 1..blocks {
            squeeze_next_block2(&mut s, &mut out0[i*rate..(i+1)*rate], &mut out1[i*rate..(i+1)*rate]);
        }
        if last < out0.len() {squeeze_last2(s, &mut out0[last..], &mut out1[last..])}
    }
}

pub fn sha3_224(data: &[u8]) -> [u8;28] {
    let mut d0 = [0u8; 28];
    let mut d1 = [0u8; 28];
    keccak(144, 0x06u8, data, data, &mut d0, &mut d1);
    d0
}

pub fn sha3_256(data: &[u8]) -> [u8;32] {
    let mut d0 = [0u8; 32];
    let mut d1 = [0u8; 32];
    keccak(136, 0x06u8, data, data, &mut d0, &mut d1);
    d0
}

pub fn sha3_384(data: &[u8]) -> [u8;48] {
    let mut d0 = [0u8; 48];
    let mut d1 = [0u8; 48];
    keccak(104, 0x06u8, data, data, &mut d0, &mut d1);
    d0
}

pub fn sha3_512(data: &[u8]) -> [u8;64] {
    let mut d0 = [0u8; 64];
    let mut d1 = [0u8; 64];
    keccak(72, 0x06u8, data, data, &mut d0, &mut d1);
    d0
}

pub fn shake128<const LEN:usize>(data: &[u8]) -> [u8; LEN] {
    let mut d0 = [0u8; LEN];
    let mut d1 = [0u8; LEN];
    keccak(168, 0x1fu8, data, data, &mut d0, &mut d1);
    d0
}

pub fn shake128x2_init_absorb_final(data0: &[u8], data1: &[u8]) -> KeccakStateX2 {
    let mut s = KeccakStateX2::new(168, 0x1fu8);
    absorb_final2(&mut s,data0,data1);
    s
}

pub fn shake128x2_squeeze_first_three_blocks(s: &mut KeccakStateX2, out0:&mut [u8], out1:&mut [u8]) {
    squeeze_first_three_blocks2(s, out0, out1)
}

pub fn shake128x2_squeeze_next_block(s: &mut KeccakStateX2, out0: &mut [u8], out1: &mut [u8]) {
    squeeze_next_block2(s, out0, out1)
}

pub fn shake256x2(input0: &[u8], input1: &[u8], out0: &mut [u8], out1: &mut [u8]) {
    keccak(136, 0x1fu8, input0, input1, out0, out1);
}
