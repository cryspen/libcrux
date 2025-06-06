use super::AesCtrContext;
use crate::{
    aes_ctr::{
        aes_ctr_key_block, aes_ctr_set_nonce, aes_ctr_update, aes_ctr_xor_block, aes_ctr_xor_blocks,
    },
    aes_generic::*,
    platform::AESState,
};

pub type Aes256CtrContext<T> = AesCtrContext<T, 15>;

pub fn aes256_ctr_init<T: AESState>(key: &[u8], nonce: &[u8]) -> Aes256CtrContext<T> {
    debug_assert!(nonce.len() == 12);
    debug_assert!(key.len() == 32);
    let mut ctr_nonce = [0u8; 16];
    ctr_nonce[0..12].copy_from_slice(nonce);
    Aes256CtrContext {
        keyex: aes256_key_expansion(key),
        ctr_nonce,
    }
}

pub fn aes256_ctr_key_block<T: AESState>(ctx: &Aes256CtrContext<T>, ctr: u32, out: &mut [u8]) {
    debug_assert!(out.len() == 16);
    aes_ctr_key_block(ctx, ctr, out);
}

pub fn aes256_ctr_set_nonce<T: AESState>(ctx: &mut Aes256CtrContext<T>, nonce: &[u8]) {
    debug_assert!(nonce.len() == 12);
    aes_ctr_set_nonce(ctx, nonce);
}

pub fn aes256_ctr_xor_block<T: AESState>(
    ctx: &Aes256CtrContext<T>,
    ctr: u32,
    inp: &[u8],
    out: &mut [u8],
) {
    debug_assert!(inp.len() == out.len() && inp.len() <= 16);
    aes_ctr_xor_block(ctx, ctr, inp, out);
}

pub fn aes256_ctr_xor_blocks<T: AESState>(
    ctx: &Aes256CtrContext<T>,
    ctr: u32,
    inp: &[u8],
    out: &mut [u8],
) {
    debug_assert!(inp.len() == out.len() && inp.len() % 16 == 0);
    aes_ctr_xor_blocks(ctx, ctr, inp, out);
}

pub fn aes256_ctr_update<T: AESState>(
    ctx: &Aes256CtrContext<T>,
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
