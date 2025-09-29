//! AES-GCM 256

use crate::{
    aes::AES_BLOCK_LEN,
    aes_gcm::aesgcm,
    ctr::Aes256CtrContext,
    gf128::GF128State,
    platform::{AESState, GF128FieldElement},
    DecryptError, NONCE_LEN, TAG_LEN,
};

// NOTE: hidden here in favor of being re-exported at crate root
#[doc(hidden)]
/// AES-GCM 256 key length.
pub const KEY_LEN: usize = 32;
pub(crate) const GCM_KEY_LEN: usize = 16;

/// The AES-GCM 256 state
pub(crate) struct State<T: AESState, U: GF128FieldElement> {
    pub(crate) aes_state: Aes256CtrContext<T>,
    pub(crate) gcm_state: GF128State<U>,
    pub(crate) tag_mix: [u8; TAG_LEN],
}

aesgcm!(State<T, U>, Aes256CtrContext);

use super::aes_gcm::platform_mod;

platform_mod!(AesGcm256, "AES-GCM 256");

pub mod portable {
    use super::*;
    platform_mod!(PortableAesGcm256, "portable AES-GCM 256");
}
pub mod neon {
    use super::*;
    platform_mod!(NeonAesGcm256, "neon AES-GCM 256");
}

pub mod x64 {
    use super::*;
    platform_mod!(X64AesGcm256, "x64 AES-GCM 256");
}
