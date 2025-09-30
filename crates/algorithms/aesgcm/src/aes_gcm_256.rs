//! AES-GCM 256
//!
//! Multiplexed AES-GCM.
//! The implementation used is determined automatically at runtime.
//! - `x64`
//! - `neon`
//! - `portable`
//!
//! ## Owned key-centric API
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
//! ## Refs key-centric API
//! ```rust
//! use libcrux_aesgcm::traits::{AeadConsts as _, Aead as _};
//! // multiplexed API
//! use libcrux_aesgcm::aes_gcm_256::AesGcm256;
//! // or:
//! // use libcrux_aesgcm::aes_gcm_256::portable::PortableAesGcm256 as AesGcm256;
//! // use libcrux_aesgcm::aes_gcm_256::neon::NeonAesGcm256 as AesGcm256;
//! // use libcrux_aesgcm::aes_gcm_256::x64::X64AesGcm256 as AesGcm256;
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
    //! Portable implementation of AES-GCM 256.
    //!
    //! For usage examples see [`aes_gcm_256`].
    use super::*;
    #[cfg(doc)]
    use crate::aes_gcm_256;
    platform_mod!(PortableAesGcm256, "AES-GCM 256 (portable)");
}
pub mod neon {
    //! Neon implementation of AES-GCM 256.
    //!
    //! This module must only be used when ARM AES instructions are available.
    //!
    //! For usage examples see [`aes_gcm_256`].
    use super::*;
    #[cfg(doc)]
    use crate::aes_gcm_256;
    platform_mod!(NeonAesGcm256, "AES-GCM 256 (neon)");
}

pub mod x64 {
    //! x64 implementation of AES-GCM 256.
    //!
    //! This module must only be used when AES-NI instructions are available.
    //!
    //! For usage examples see [`aes_gcm_256`].
    use super::*;
    #[cfg(doc)]
    use crate::aes_gcm_256;
    platform_mod!(X64AesGcm256, "AES-GCM 256 (x64)");
}
