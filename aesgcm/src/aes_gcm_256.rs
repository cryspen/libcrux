#![allow(clippy::needless_range_loop)]

use crate::{
    aes::AES_BLOCK_LEN,
    ctr::Aes256CtrContext,
    gf128::GF128State,
    platform::{AESState, GF128FieldElement},
    DecryptError, NONCE_LEN, TAG_LEN,
};

/// Key length.
pub(crate) const KEY_LEN: usize = 32;
pub(crate) const GCM_KEY_LEN: usize = 16;

/// The AES-GCM 256 state
pub(crate) struct State<T: AESState, U: GF128FieldElement> {
    pub(crate) aes_state: Aes256CtrContext<T>,
    pub(crate) gcm_state: GF128State<U>,
    pub(crate) tag_mix: [u8; TAG_LEN],
}

impl<T: AESState, U: GF128FieldElement> super::State for State<T, U> {
    /// Initialize the state
    fn init(key: &[u8]) -> Self {
        debug_assert!(key.len() == KEY_LEN);

        let nonce = [0u8; NONCE_LEN];
        let mut gcm_key = [0u8; GCM_KEY_LEN];
        let tag_mix = [0u8; TAG_LEN];

        let aes_state = Aes256CtrContext::<T>::init(key, &nonce);
        aes_state.key_block(0, &mut gcm_key);
        let gcm_state = GF128State::init(&gcm_key);

        Self {
            aes_state,
            gcm_state,
            tag_mix,
        }
    }

    fn set_nonce(&mut self, nonce: &[u8]) {
        debug_assert!(nonce.len() == NONCE_LEN);

        self.aes_state.set_nonce(nonce);
        self.aes_state.key_block(1, &mut self.tag_mix);
    }

    fn encrypt(&mut self, aad: &[u8], plaintext: &[u8], ciphertext: &mut [u8], tag: &mut [u8]) {
        debug_assert!(ciphertext.len() == plaintext.len());
        debug_assert!(plaintext.len() / 16 <= u32::MAX as usize);
        debug_assert!(tag.len() == TAG_LEN);

        self.aes_state.update(2, plaintext, ciphertext);

        self.gcm_state.update_padded(aad);
        self.gcm_state.update_padded(ciphertext);

        let mut last_block = [0u8; AES_BLOCK_LEN];
        last_block[0..8].copy_from_slice(&((aad.len() as u64) * 8).to_be_bytes());
        last_block[8..16].copy_from_slice(&((plaintext.len() as u64) * 8).to_be_bytes());

        self.gcm_state.update(&last_block);
        self.gcm_state.emit(tag);

        for i in 0..16 {
            tag[i] ^= self.tag_mix[i];
        }
    }

    fn decrypt(
        &mut self,
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8],
        plaintext: &mut [u8],
    ) -> Result<(), DecryptError> {
        debug_assert!(plaintext.len() == ciphertext.len());
        debug_assert!(ciphertext.len() / AES_BLOCK_LEN <= u32::MAX as usize);
        debug_assert!(tag.len() == TAG_LEN);

        self.gcm_state.update_padded(aad);
        self.gcm_state.update_padded(ciphertext);

        let mut last_block = [0u8; AES_BLOCK_LEN];
        last_block[0..8].copy_from_slice(&((aad.len() as u64) * 8).to_be_bytes());
        last_block[8..16].copy_from_slice(&((plaintext.len() as u64) * 8).to_be_bytes());

        self.gcm_state.update(&last_block);

        let mut computed_tag = [0u8; TAG_LEN];
        self.gcm_state.emit(&mut computed_tag);

        for i in 0..16 {
            computed_tag[i] ^= self.tag_mix[i];
        }

        let mut eq_mask = 0u8;
        for i in 0..16 {
            eq_mask |= computed_tag[i] ^ tag[i];
        }

        if eq_mask == 0 {
            self.aes_state.update(2, ciphertext, plaintext);
            Ok(())
        } else {
            Err(DecryptError())
        }
    }
}
