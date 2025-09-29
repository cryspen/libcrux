//! AES-GCM 256
//!
//! ```rust
//! use libcrux_aesgcm::traits::AeadConsts as _;
//! // multiplexed API
//! use libcrux_aesgcm::aes_gcm_256::{AesGcm256, Key, Tag, Nonce};
//! // or:
//! // use libcrux_aesgcm::aes_gcm_256::portable::{Key, Tag, Nonce};
//! // use libcrux_aesgcm::aes_gcm_256::neon::{Key, Tag, Nonce};
//! // use libcrux_aesgcm::aes_gcm_256::x64::{Key, Tag, Nonce};
//!
//! let k: Key = [0; AesGcm256::KEY_LEN].into();
//! let nonce: Nonce = [0; AesGcm256::NONCE_LEN].into();
//! let mut tag: Tag = [0; AesGcm256::TAG_LEN].into();
//!
//! let pt = b"the quick brown fox jumps over the lazy dog";
//! let mut ct = [0; 43];
//! let mut pt_out = [0; 43];
//!
//! k.encrypt(&mut ct, &mut tag, &nonce, b"", pt).unwrap();
//! k.decrypt(&mut pt_out, &nonce, b"", &ct, &tag).unwrap();
//! assert_eq!(pt, &pt_out);
//! ```
//!
//! ```rust
//! use libcrux_aesgcm::traits::{AeadConsts as _, Aead as _};
//! // multiplexed API
//! use libcrux_aesgcm::aes_gcm_256::AesGcm256;
//! // or:
//! // use libcrux_aesgcm::aes_gcm_256::portable::PortableAesGcm256;
//! // use libcrux_aesgcm::aes_gcm_256::neon::NeonAesGcm256;
//! // use libcrux_aesgcm::aes_gcm_256::x64::X64AesGcm256;
//!
//! let algo = AesGcm256;
//!
//! let mut tag_bytes = [0; AesGcm256::TAG_LEN];
//! let key = algo.new_key(&[0; AesGcm256::KEY_LEN]).unwrap();
//! let tag = algo.new_tag_mut(&mut tag_bytes).unwrap();
//! let nonce = algo.new_nonce(&[0; AesGcm256::NONCE_LEN]).unwrap();
//!
//! let pt = b"the quick brown fox jumps over the lazy dog";
//! let mut ct = [0; 43];
//! let mut pt_out = [0; 43];
//!
//! key.encrypt(&mut ct, tag, nonce, b"", pt).unwrap();
//! let tag = algo.new_tag(&tag_bytes).unwrap();
//! key.decrypt(&mut pt_out, nonce, b"", &ct, tag).unwrap();
//! assert_eq!(pt, &pt_out);
//! ```

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
