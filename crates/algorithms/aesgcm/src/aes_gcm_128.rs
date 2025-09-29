//! AES-GCM 128

use crate::{
    aes::AES_BLOCK_LEN,
    aes_gcm::aesgcm,
    ctr::Aes128CtrContext,
    gf128::GF128State,
    platform::{AESState, GF128FieldElement},
    DecryptError, NONCE_LEN, TAG_LEN,
};

// NOTE: hidden here in favor of being re-exported at crate root
#[doc(hidden)]
/// AES-GCM 128 key length.
pub const KEY_LEN: usize = 16;
pub(crate) const GCM_KEY_LEN: usize = 16;

/// The AES-GCM 128 state
pub(crate) struct State<T: AESState, U: GF128FieldElement> {
    pub(crate) aes_state: Aes128CtrContext<T>,
    pub(crate) gcm_state: GF128State<U>,
    pub(crate) tag_mix: [u8; TAG_LEN],
}

aesgcm!(State<T, U>, Aes128CtrContext);

use super::aes_gcm::platform_mod;

platform_mod!(AesGcm128, "AES-GCM 128");

pub mod portable {
    use super::*;
    platform_mod!(PortableAesGcm128, "portable AES-GCM 128");
}
pub mod neon {
    use super::*;
    platform_mod!(NeonAesGcm128, "neon AES-GCM 128");
}

pub mod x64 {
    use super::*;
    platform_mod!(X64AesGcm128, "x64 AES-GCM 128");
}
