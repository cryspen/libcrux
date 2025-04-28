#![allow(non_camel_case_types)]

use crate::{aes_generic::*, platform::AESState};
pub struct AES_CTR_Context<T: AESState, const NUM_KEYS: usize> {
    pub(crate) keyex: ExtendedKey<T, NUM_KEYS>,
    pub(crate) ctr_nonce: [u8; 16],
}

fn aes_ctr_set_nonce<T: AESState, const NUM_KEYS: usize>(
    ctx: &mut AES_CTR_Context<T, NUM_KEYS>,
    nonce: &[u8],
) {
    debug_assert!(nonce.len() == 12);
    ctx.ctr_nonce[0..12].copy_from_slice(nonce);
}

fn aes_ctr_key_block<T: AESState, const NUM_KEYS: usize>(
    ctx: &AES_CTR_Context<T, NUM_KEYS>,
    ctr: u32,
    out: &mut [u8],
) {
    debug_assert!(out.len() == 16);
    let mut st_init = ctx.ctr_nonce;
    st_init[12..16].copy_from_slice(&ctr.to_be_bytes());
    let mut st = T::new();
    st.load_block(&st_init);
    block_cipher(&mut st, ctx.keyex);
    st.store_block(out);
}

fn aes_ctr_xor_block<T: AESState, const NUM_KEYS: usize>(
    ctx: &AES_CTR_Context<T, NUM_KEYS>,
    ctr: u32,
    inp: &[u8],
    out: &mut [u8],
) {
    debug_assert!(inp.len() == out.len() && inp.len() <= 16);
    let mut st_init = ctx.ctr_nonce;
    st_init[12..16].copy_from_slice(&ctr.to_be_bytes());
    let mut st = T::new();
    st.load_block(&st_init);
    block_cipher(&mut st, ctx.keyex);
    st.xor_block(inp, out);
}

fn aes_ctr_xor_blocks<T: AESState, const NUM_KEYS: usize>(
    ctx: &AES_CTR_Context<T, NUM_KEYS>,
    ctr: u32,
    inp: &[u8],
    out: &mut [u8],
) {
    debug_assert!(inp.len() == out.len() && inp.len() % 16 == 0);
    let blocks = inp.len() / 16;
    for i in 0..blocks {
        aes_ctr_xor_block(
            &ctx,
            ctr.wrapping_add(i as u32),
            &inp[i * 16..i * 16 + 16],
            &mut out[i * 16..i * 16 + 16],
        );
    }
}

fn aes_ctr_update<T: AESState, const NUM_KEYS: usize>(
    ctx: &AES_CTR_Context<T, NUM_KEYS>,
    ctr: u32,
    inp: &[u8],
    out: &mut [u8],
) {
    debug_assert!(inp.len() == out.len());
    let blocks = inp.len() / 16;
    aes_ctr_xor_blocks(&ctx, ctr, &inp[0..blocks * 16], &mut out[0..blocks * 16]);
    let last = inp.len() - inp.len() % 16;
    if last < inp.len() {
        aes_ctr_xor_block(
            &ctx,
            ctr.wrapping_add(blocks as u32),
            &inp[last..],
            &mut out[last..],
        );
    }
}

mod aes128_ctr {
    use super::AES_CTR_Context;
    use crate::{
        aes_ctr::{
            aes_ctr_key_block, aes_ctr_set_nonce, aes_ctr_update, aes_ctr_xor_block,
            aes_ctr_xor_blocks,
        },
        aes_generic::*,
        platform::AESState,
    };
    pub type AES128_CTR_Context<T> = AES_CTR_Context<T, 11>;

    pub fn aes128_ctr_init<T: AESState>(key: &[u8], nonce: &[u8]) -> AES128_CTR_Context<T> {
        debug_assert!(nonce.len() == 12);
        debug_assert!(key.len() == 16);
        let mut ctr_nonce = [0u8; 16];
        ctr_nonce[0..12].copy_from_slice(nonce);
        AES128_CTR_Context {
            keyex: aes128_key_expansion(key),
            ctr_nonce,
        }
    }

    pub fn aes128_ctr_set_nonce<T: AESState>(ctx: &mut AES128_CTR_Context<T>, nonce: &[u8]) {
        debug_assert!(nonce.len() == 12);
        aes_ctr_set_nonce(ctx, nonce);
    }

    pub fn aes128_ctr_key_block<T: AESState>(
        ctx: &AES128_CTR_Context<T>,
        ctr: u32,
        out: &mut [u8],
    ) {
        debug_assert!(out.len() == 16);
        aes_ctr_key_block(ctx, ctr, out);
    }

    pub fn aes128_ctr_xor_block<T: AESState>(
        ctx: &AES128_CTR_Context<T>,
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(inp.len() == out.len() && inp.len() <= 16);
        aes_ctr_xor_block(ctx, ctr, inp, out);
    }

    pub fn aes128_ctr_xor_blocks<T: AESState>(
        ctx: &AES128_CTR_Context<T>,
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(inp.len() == out.len() && inp.len() % 16 == 0);
        aes_ctr_xor_blocks(ctx, ctr, inp, out);
    }

    pub fn aes128_ctr_update<T: AESState>(
        ctx: &AES128_CTR_Context<T>,
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(inp.len() == out.len());
        aes_ctr_update(ctx, ctr, inp, out);
    }

    pub fn aes128_ctr_encrypt<T: AESState>(
        key: &[u8],
        nonce: &[u8],
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(nonce.len() == 12);
        debug_assert!(key.len() == 16);
        debug_assert!(inp.len() == out.len());
        let ctx = aes128_ctr_init::<T>(key, nonce);
        aes128_ctr_update(&ctx, ctr, inp, out);
    }
}

mod aes256_ctr {
    use super::AES_CTR_Context;
    use crate::{
        aes_ctr::{
            aes_ctr_key_block, aes_ctr_set_nonce, aes_ctr_update, aes_ctr_xor_block,
            aes_ctr_xor_blocks,
        },
        aes_generic::*,
        platform::AESState,
    };

    pub type AES256_CTR_Context<T> = AES_CTR_Context<T, 15>;

    pub fn aes256_ctr_init<T: AESState>(key: &[u8], nonce: &[u8]) -> AES256_CTR_Context<T> {
        debug_assert!(nonce.len() == 12);
        debug_assert!(key.len() == 32);
        let mut ctr_nonce = [0u8; 16];
        ctr_nonce[0..12].copy_from_slice(nonce);
        AES256_CTR_Context {
            keyex: aes256_key_expansion(key),
            ctr_nonce,
        }
    }

    pub fn aes256_ctr_key_block<T: AESState>(
        ctx: &AES256_CTR_Context<T>,
        ctr: u32,
        out: &mut [u8],
    ) {
        debug_assert!(out.len() == 16);
        aes_ctr_key_block(ctx, ctr, out);
    }

    pub fn aes256_ctr_set_nonce<T: AESState>(ctx: &mut AES256_CTR_Context<T>, nonce: &[u8]) {
        debug_assert!(nonce.len() == 12);
        aes_ctr_set_nonce(ctx, nonce);
    }

    pub fn aes256_ctr_xor_block<T: AESState>(
        ctx: &AES256_CTR_Context<T>,
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(inp.len() == out.len() && inp.len() <= 16);
        aes_ctr_xor_block(ctx, ctr, inp, out);
    }

    pub fn aes256_ctr_xor_blocks<T: AESState>(
        ctx: &AES256_CTR_Context<T>,
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(inp.len() == out.len() && inp.len() % 16 == 0);
        aes_ctr_xor_blocks(ctx, ctr, inp, out);
    }

    pub fn aes256_ctr_update<T: AESState>(
        ctx: &AES256_CTR_Context<T>,
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(inp.len() == out.len());
        aes_ctr_update(ctx, ctr, inp, out);
    }

    pub fn aes256_ctr_encrypt<T: AESState>(
        key: &[u8],
        nonce: &[u8],
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(nonce.len() == 12);
        debug_assert!(key.len() == 32);
        debug_assert!(inp.len() == out.len());
        let ctx = aes256_ctr_init::<T>(key, nonce);
        aes256_ctr_update(&ctx, ctr, inp, out);
    }
}

pub use aes128_ctr::*;
pub use aes256_ctr::*;

#[cfg(test)]
mod test {
    use crate::platform;

    use super::{aes128_ctr_encrypt, aes128_ctr_init, aes128_ctr_xor_block};

    const INPUT: [u8; 32] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
        0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D,
        0x1E, 0x1F,
    ];
    const KEY: [u8; 16] = [
        0x7E, 0x24, 0x06, 0x78, 0x17, 0xFA, 0xE0, 0xD7, 0x43, 0xD6, 0xCE, 0x1F, 0x32, 0x53, 0x91,
        0x63,
    ];
    const NONCE: [u8; 12] = [
        0x00, 0x6C, 0xB6, 0xDB, 0xC0, 0x54, 0x3B, 0x59, 0xDA, 0x48, 0xD9, 0x0B,
    ];
    const EXPECTED: [u8; 32] = [
        0x51, 0x04, 0xA1, 0x06, 0x16, 0x8A, 0x72, 0xD9, 0x79, 0x0D, 0x41, 0xEE, 0x8E, 0xDA, 0xD3,
        0x88, 0xEB, 0x2E, 0x1E, 0xFC, 0x46, 0xDA, 0x57, 0xC8, 0xFC, 0xE6, 0x30, 0xDF, 0x91, 0x41,
        0xBE, 0x28,
    ];

    #[test]
    fn test_ctr_block() {
        let mut computed: [u8; 32] = [0u8; 32];
        let ctx = aes128_ctr_init::<platform::portable::State>(&KEY, &NONCE);
        aes128_ctr_xor_block(&ctx, 1, &INPUT[0..16], &mut computed[0..16]);
        aes128_ctr_xor_block(&ctx, 2, &INPUT[16..32], &mut computed[16..32]);
        for i in 0..32 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature="aes"))]
    #[test]
    fn test_ctr_block_neon() {
        let mut computed: [u8; 32] = [0u8; 32];
        let ctx = aes128_ctr_init::<platform::neon::State>(&KEY, &NONCE);
        aes128_ctr_xor_block(&ctx, 1, &INPUT[0..16], &mut computed[0..16]);
        aes128_ctr_xor_block(&ctx, 2, &INPUT[16..32], &mut computed[16..32]);
        for i in 0..32 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature="aes"))]
    #[test]
    fn test_ctr_block_neon() {
        let mut computed: [u8; 32] = [0u8; 32];
        let ctx = aes128_ctr_init::<platform::neon::State>(&KEY, &NONCE);
        aes128_ctr_xor_block(&ctx, 1, &INPUT[0..16], &mut computed[0..16]);
        aes128_ctr_xor_block(&ctx, 2, &INPUT[16..32], &mut computed[16..32]);
        for i in 0..32 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }

    #[test]
    fn test_ctr_encrypt() {
        let mut computed: [u8; 32] = [0u8; 32];
        aes128_ctr_encrypt::<platform::portable::State>(&KEY, &NONCE, 1, &INPUT, &mut computed);
        for i in 0..32 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature="aes"))]
    #[test]
    fn test_ctr_encrypt_neon() {
        let mut computed: [u8; 32] = [0u8; 32];
        aes128_ctr_encrypt::<platform::neon::State>(&KEY, &NONCE, 1, &INPUT, &mut computed);
        for i in 0..32 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }

    #[cfg(all(target_arch = "x86_64", target_feature="aes"))]
    #[test]
    fn test_ctr_encrypt_intel() {
        let mut computed: [u8; 32] = [0u8; 32];
        aes128_ctr_encrypt::<platform::intel_ni::State>(&KEY, &NONCE, 1, &INPUT, &mut computed);
        for i in 0..32 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }
    
}
