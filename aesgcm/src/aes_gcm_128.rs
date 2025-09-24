//! AES-GCM 128

use crate::{
    aes::AES_BLOCK_LEN,
    aes_gcm::aesgcm,
    ctr::Aes128CtrContext,
    gf128::GF128State,
    platform::{AESState, GF128FieldElement},
    DecryptError, NONCE_LEN, TAG_LEN,
};

/// Key length.
pub const KEY_LEN: usize = 16;
pub(crate) const GCM_KEY_LEN: usize = 16;

/// The AES-GCM 128 state
pub(crate) struct State<T: AESState, U: GF128FieldElement> {
    pub(crate) aes_state: Aes128CtrContext<T>,
    pub(crate) gcm_state: GF128State<U>,
    pub(crate) tag_mix: [u8; TAG_LEN],
}

aesgcm!(State<T, U>, Aes128CtrContext);
