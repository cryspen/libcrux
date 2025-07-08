use core::array::from_fn;

use super::AesCtrContext;
use crate::{aes_gcm_128::KEY_LEN, aes_generic::*, platform::AESState, NONCE_LEN};

pub(super) const NUM_KEYS: usize = 11;

/// Type alias for the AES 128 ctr context.
pub(crate) type Aes128CtrContext<T> = AesCtrContext<T, NUM_KEYS>;

impl<T: AESState> Aes128CtrContext<T> {
    pub(crate) fn init(key: &[u8], nonce: &[u8]) -> Self {
        debug_assert!(nonce.len() == NONCE_LEN);
        debug_assert!(key.len() == KEY_LEN);

        let mut ctr_nonce = [0u8; 16];
        ctr_nonce[0..12].copy_from_slice(nonce);

        Self {
            extended_key: key_expansion(key),
            ctr_nonce,
        }
    }

    pub(crate) fn set_nonce(&mut self, nonce: &[u8]) {
        debug_assert!(nonce.len() == NONCE_LEN);

        self.aes_ctr_set_nonce(nonce);
    }

    pub(crate) fn key_block(&self, ctr: u32, out: &mut [u8]) {
        debug_assert!(out.len() == KEY_LEN);

        self.aes_ctr_key_block(ctr, out);
    }

    pub(crate) fn update(&self, ctr: u32, inp: &[u8], out: &mut [u8]) {
        debug_assert!(inp.len() == out.len());

        self.aes_ctr_update(ctr, inp, out);
    }
}

/// 128 - Key expansion
fn key_expansion<T: AESState>(key: &[u8]) -> ExtendedKey<T, NUM_KEYS> {
    debug_assert!(key.len() == KEY_LEN);

    let mut keyex = from_fn(|_| T::new());
    keyex[0].load_block(key);

    macro_rules! expansion_step128 {
        ($i:expr,$rcon:expr) => {
            let prev = keyex[$i - 1].clone();
            keyex[$i].aes_keygen_assist0::<$rcon>(&prev);
            keyex[$i].key_expansion_step(&prev);
        };
    }

    expansion_step128!(1, 0x01);
    expansion_step128!(2, 0x02);
    expansion_step128!(3, 0x04);
    expansion_step128!(4, 0x08);
    expansion_step128!(5, 0x10);
    expansion_step128!(6, 0x20);
    expansion_step128!(7, 0x40);
    expansion_step128!(8, 0x80);
    expansion_step128!(9, 0x1b);
    expansion_step128!(10, 0x36);

    keyex
}

#[cfg(test)]
pub(crate) mod test_utils {
    use super::*;

    pub(crate) fn aes128_ctr_xor_block<T: AESState>(
        ctx: &Aes128CtrContext<T>,
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(inp.len() == out.len() && inp.len() <= 16);
        ctx.aes_ctr_xor_block(ctr, inp, out);
    }

    pub(crate) fn aes128_ctr_encrypt<T: AESState>(
        key: &[u8],
        nonce: &[u8],
        ctr: u32,
        inp: &[u8],
        out: &mut [u8],
    ) {
        debug_assert!(nonce.len() == NONCE_LEN);
        debug_assert!(key.len() == KEY_LEN);
        debug_assert!(inp.len() == out.len());
        let ctx = Aes128CtrContext::<T>::init(key, nonce);
        ctx.update(ctr, inp, out);
    }
}
