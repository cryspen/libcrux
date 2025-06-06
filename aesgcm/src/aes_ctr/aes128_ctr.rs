use super::AesCtrContext;
use crate::{
    aes_ctr::{aes_ctr_key_block, aes_ctr_set_nonce, aes_ctr_update},
    aes_generic::*,
    platform::AESState,
};

/// Type alias for the AES 128 ctr context
pub(crate) type Aes128CtrContext<T> = AesCtrContext<T, 11>;

pub fn aes128_ctr_init<T: AESState>(key: &[u8], nonce: &[u8]) -> Aes128CtrContext<T> {
    debug_assert!(nonce.len() == 12);
    debug_assert!(key.len() == 16);

    let mut ctr_nonce = [0u8; 16];
    ctr_nonce[0..12].copy_from_slice(nonce);

    Aes128CtrContext {
        keyex: aes128_key_expansion(key),
        ctr_nonce,
    }
}

pub fn aes128_ctr_set_nonce<T: AESState>(ctx: &mut Aes128CtrContext<T>, nonce: &[u8]) {
    debug_assert!(nonce.len() == 12);

    aes_ctr_set_nonce(ctx, nonce);
}

pub fn aes128_ctr_key_block<T: AESState>(ctx: &Aes128CtrContext<T>, ctr: u32, out: &mut [u8]) {
    debug_assert!(out.len() == 16);

    aes_ctr_key_block(ctx, ctr, out);
}

pub fn aes128_ctr_update<T: AESState>(
    ctx: &Aes128CtrContext<T>,
    ctr: u32,
    inp: &[u8],
    out: &mut [u8],
) {
    debug_assert!(inp.len() == out.len());

    aes_ctr_update(ctx, ctr, inp, out);
}

#[cfg(test)]
pub(crate) mod test_utils {
    use super::*;
    use crate::aes_ctr::aes_ctr_xor_block;

    pub fn aes128_ctr_xor_block<T: AESState>(
        ctx: &Aes128CtrContext<T>,
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(inp.len() == out.len() && inp.len() <= 16);
        aes_ctr_xor_block(ctx, ctr, inp, out);
    }

    // pub fn aes128_ctr_xor_blocks<T: AESState>(
    //     ctx: &Aes128CtrContext<T>,
    //     ctr: u32,
    //     inp: &[u8],
    //     out: &mut [u8],
    // ) {
    //     debug_assert!(inp.len() == out.len() && inp.len() % 16 == 0);
    //     aes_ctr_xor_blocks(ctx, ctr, inp, out);
    // }

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
