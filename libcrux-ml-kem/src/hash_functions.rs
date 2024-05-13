#![allow(non_snake_case)]

use crate::constants::H_DIGEST_SIZE;

use libcrux_sha3::rust_simd::{self, KeccakState4};

#[inline(always)]
pub(crate) fn G(input: &[u8]) -> [u8; 64] {
    //rust_simd::sha3_512(input)
    libcrux_sha3::sha512(input)
}

#[inline(always)]
pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    //rust_simd::sha3_256(input)
    libcrux_sha3::sha256(input)
}

#[inline(always)]
pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    //rust_simd::shake256::<LEN>(input)
    libcrux_sha3::shake256::<LEN>(input)
}

#[cfg(feature = "simd128")]
#[inline(always)]
pub(crate) fn PRFxN<const LEN: usize, const K: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
    let mut out = [[0u8; LEN]; K];
    let mut extra = [0u8; LEN];

    match K {
        2 => { let (out0,out1) = out.split_at_mut(1);
               rust_simd::shake256x2(&input[0], &input[1], &mut out0[0], &mut out1[0]);
             }
        3 => { let (out0,out12) = out.split_at_mut(1);
               let (out1,out2) = out12.split_at_mut(1); 
               rust_simd::shake256x2(&input[0], &input[1], &mut out0[0], &mut out1[0]);
               rust_simd::shake256x2(&input[2], &input[2], &mut out2[0], &mut extra);
             }
        _ => { let (out0,out123) = out.split_at_mut(1);
               let (out1,out23) = out123.split_at_mut(1);
               let (out2,out3) = out23.split_at_mut(1);
               rust_simd::shake256x2(&input[0], &input[1], &mut out0[0], &mut out1[0]);
               rust_simd::shake256x2(&input[2], &input[3], &mut out2[0], &mut out3[0]); 
             }      
    }
    out
}
#[cfg(not(feature = "simd128"))]
#[inline(always)]
pub(crate) fn PRFxN<const LEN: usize, const K: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
    core::array::from_fn(|i| rust_simd::shake256::<LEN>(&input[i]))
}

pub(crate) type Shake128x4State = KeccakState4;

#[cfg(feature = "simd128")]
#[inline(always)]
pub(crate) fn absorb<const K: usize>(input: [[u8; 34]; K]) -> Shake128x4State {
    debug_assert!(K == 2 || K == 3 || K == 4);

    let mut states = rust_simd::shake128x4_init();
    match K {
        2 => {
            rust_simd::shake128x2_absorb_final(&mut states[0],&input[0],&input[1]);
        },
        3 => {
            rust_simd::shake128x2_absorb_final(&mut states[0],&input[0],&input[1]);
            rust_simd::shake128x2_absorb_final(&mut states[1],&input[2],&input[2]);
        },
        _ => {
            rust_simd::shake128x2_absorb_final(&mut states[0],&input[0],&input[1]);
            rust_simd::shake128x2_absorb_final(&mut states[1],&input[2],&input[3]);
        },
    }
    states
}

#[cfg(not(feature = "simd128"))]
#[inline(always)]
pub(crate) fn absorb<const K: usize>(input: [[u8; 34]; K]) -> Shake128x4State {
    debug_assert!(K == 2 || K == 3 || K == 4);
    let mut states = rust_simd::shake128x4_init();
    for i in 0..K {
        rust_simd::shake128_absorb_final(&mut states[i], &input[i]);
    } 
    states
}


pub(crate) const BLOCK_SIZE: usize = 168;
pub(crate) const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

#[cfg(feature = "simd128")]
#[inline(always)]
pub(crate) fn squeeze_three_blocks<const K: usize> (
    state: &mut Shake128x4State,
) -> [[u8; THREE_BLOCKS]; K] {
    let mut out = [[0u8; THREE_BLOCKS]; K];
    let mut extra = [0u8; THREE_BLOCKS];

    match K {
        2 => { let (out0,out1) = out.split_at_mut(1);
               rust_simd::shake128x2_squeeze_first_three_blocks(&mut state[0], &mut out0[0], &mut out1[0]);
             }
        3 => { let (out0,out12) = out.split_at_mut(1);
               let (out1,out2) = out12.split_at_mut(1); 
               rust_simd::shake128x2_squeeze_first_three_blocks(&mut state[0], &mut out0[0], &mut out1[0]);
               rust_simd::shake128x2_squeeze_first_three_blocks(&mut state[1], &mut out2[0], &mut extra);
             }
        _ => { let (out0,out123) = out.split_at_mut(1);
               let (out1,out23) = out123.split_at_mut(1);
               let (out2,out3) = out23.split_at_mut(1);
               rust_simd::shake128x2_squeeze_first_three_blocks(&mut state[0], &mut out0[0], &mut out1[0]);
               rust_simd::shake128x2_squeeze_first_three_blocks(&mut state[1], &mut out2[0], &mut out3[0]); 
             }      
    }
    out
}

#[cfg(not(feature = "simd128"))]
#[inline(always)]
pub(crate) fn squeeze_three_blocks<const K: usize> (
    state: &mut Shake128x4State,
) -> [[u8; THREE_BLOCKS]; K] {
    let mut out = [[0u8; THREE_BLOCKS]; K];
    for i in 0..K {
        rust_simd::shake128_squeeze_first_three_blocks(&mut state[i], &mut out[i]);
    }
    out
}

#[cfg(feature = "simd128")]
#[inline(always)]
pub(crate) fn squeeze_block<const K: usize>(
    state: &mut Shake128x4State,
) -> [[u8; BLOCK_SIZE]; K] {
    let mut out0 = [0u8; BLOCK_SIZE];
    let mut out1 = [0u8; BLOCK_SIZE];
    let mut out2 = [0u8; BLOCK_SIZE];
    let mut out3 = [0u8; BLOCK_SIZE];

    let mut out = [[0u8; BLOCK_SIZE]; K];

    match K {
        2 => { rust_simd::shake128x2_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
               out[0] = out0;
               out[1] = out1; }
        3 => { rust_simd::shake128x2_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
               rust_simd::shake128x2_squeeze_next_block(&mut state[1], &mut out2, &mut out3);
               out[0] = out0;
               out[1] = out1;
               out[2] = out2; }
        _ => { rust_simd::shake128x2_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
               rust_simd::shake128x2_squeeze_next_block(&mut state[1], &mut out2, &mut out3); 
               out[0] = out0;
               out[1] = out1;
               out[2] = out2;
               out[3] = out3; }
    }
    out
}

#[cfg(not(feature = "simd128"))]
#[inline(always)]
pub(crate) fn squeeze_block<const K: usize>(
    state: &mut Shake128x4State,
) -> [[u8; BLOCK_SIZE]; K] {
    let mut out = [[0u8; BLOCK_SIZE]; K];
    for i in 0..K {
        rust_simd::shake128_squeeze_next_block(&mut state[i], &mut out[i]);
    }
    out
}


/// Free the memory of the state.
///
/// **NOTE:** That this needs to be done manually for now.
#[inline(always)]
pub(crate) fn free_state(_xof_state: Shake128x4State) {
}
