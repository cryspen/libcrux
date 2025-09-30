//! AES-GCM 128
//!
//! Multiplexed AES-GCM.
//! The implementation used is determined automatically at runtime.
//! - `x64`
//! - `neon`
//! - `portable`
//!
//! ## Owned key-centric API
//! ```rust
//! // multiplexed API
//! use libcrux_aesgcm::AeadConsts as _;
//! use libcrux_aesgcm::aes_gcm_128::{AesGcm128, Key, Tag, Nonce};
//! // or:
//! // use libcrux_aesgcm::aes_gcm_128::portable::{Key, Tag, Nonce};
//! // use libcrux_aesgcm::aes_gcm_128::neon::{Key, Tag, Nonce};
//! // use libcrux_aesgcm::aes_gcm_128::x64::{Key, Tag, Nonce};
//!
//! let k: Key = [0; AesGcm128::KEY_LEN].into();
//! let nonce: Nonce = [0; AesGcm128::NONCE_LEN].into();
//! let mut tag: Tag = [0; AesGcm128::TAG_LEN].into();
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
//! use libcrux_aesgcm::{AeadConsts as _, Aead as _};
//! // multiplexed API
//! use libcrux_aesgcm::aes_gcm_128::AesGcm128;
//! // or:
//! // use libcrux_aesgcm::aes_gcm_128::portable::PortableAesGcm128 as AesGcm128;
//! // use libcrux_aesgcm::aes_gcm_128::neon::NeonAesGcm128 as AesGcm128;
//! // use libcrux_aesgcm::aes_gcm_128::x64::X64AesGcm128 as AesGcm128;
//!
//! let algo = AesGcm128;
//!
//! let mut tag_bytes = [0; AesGcm128::TAG_LEN];
//! let key = algo.new_key(&[0; AesGcm128::KEY_LEN]).unwrap();
//! let tag = algo.new_tag_mut(&mut tag_bytes).unwrap();
//! let nonce = algo.new_nonce(&[0; AesGcm128::NONCE_LEN]).unwrap();
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
    //! Portable implementation of AES-GCM 128.
    //!
    //! For usage examples see [`aes_gcm_128`].
    use super::*;
    #[cfg(doc)]
    use crate::aes_gcm_128;
    platform_mod!(PortableAesGcm128, "AES-GCM 128 (portable)");
}
pub mod neon {
    //! Neon implementation of AES-GCM 128.
    //!
    //! This module must only be used when ARM AES instructions are available.
    //!
    //! For usage examples see [`aes_gcm_128`].
    use super::*;
    #[cfg(doc)]
    use crate::aes_gcm_128;
    platform_mod!(NeonAesGcm128, "AES-GCM 128 (neon)");
}

pub mod x64 {
    //! x64 implementation of AES-GCM 128.
    //!
    //! This module must only be used when AES-NI instructions are available.
    //!
    //! For usage examples see [`aes_gcm_128`].
    use super::*;
    #[cfg(doc)]
    use crate::aes_gcm_128;
    platform_mod!(X64AesGcm128, "AES-GCM 128 (x64)");
}
