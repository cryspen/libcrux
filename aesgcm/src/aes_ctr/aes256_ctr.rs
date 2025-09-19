use core::array::from_fn;

use super::AesCtrContext;
use crate::{aes_gcm_256::KEY_LEN, aes_generic::*, platform::AESState, NONCE_LEN};

pub(crate) const NUM_KEYS: usize = 15;

/// Type alias for the AES 256 ctr context.
pub(crate) type Aes256CtrContext<T> = AesCtrContext<T, NUM_KEYS>;

impl<T: AESState> Aes256CtrContext<T> {
    pub(crate) fn init(key: &[u8], nonce: &[u8]) -> Self {
        debug_assert!(nonce.len() == NONCE_LEN);
        debug_assert!(key.len() == KEY_LEN);

        let mut ctr_nonce = [0u8; 16];
        ctr_nonce[0..NONCE_LEN].copy_from_slice(nonce);

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
        debug_assert!(out.len() == AES_BLOCK_LEN, "out.len() = {}", out.len());
        self.aes_ctr_key_block(ctr, out);
    }

    pub(crate) fn update(&self, ctr: u32, input: &[u8], out: &mut [u8]) {
        debug_assert!(input.len() == out.len());
        self.aes_ctr_update(ctr, input, out);
    }
}

/// 256 - Key expansion
fn key_expansion<T: AESState>(key: &[u8]) -> ExtendedKey<T, NUM_KEYS> {
    debug_assert!(key.len() == KEY_LEN);

    let mut keyex = from_fn(|_| T::new());
    keyex[0].load_block(&key[0..16]);
    keyex[1].load_block(&key[16..32]);

    macro_rules! expansion_step256 {
        ($i:expr,$rcon:expr) => {
            let prev0 = keyex[$i - 2].clone();
            let prev1 = keyex[$i - 1].clone();

            keyex[$i].aes_keygen_assist0::<$rcon>(&prev1);
            keyex[$i].key_expansion_step(&prev0);

            // XXX: avoid clone
            let next0 = keyex[$i].clone();
            keyex[$i + 1].aes_keygen_assist1(&next0);
            keyex[$i + 1].key_expansion_step(&prev1);
        };
    }

    expansion_step256!(2, 0x01);
    expansion_step256!(4, 0x02);
    expansion_step256!(6, 0x04);
    expansion_step256!(8, 0x08);
    expansion_step256!(10, 0x10);
    expansion_step256!(12, 0x20);

    let prev0 = keyex[12].clone();
    let prev1 = keyex[13].clone();
    keyex[14].aes_keygen_assist0::<0x40>(&prev1);
    keyex[14].key_expansion_step(&prev0);

    keyex
}
