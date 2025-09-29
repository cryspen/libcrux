#![no_std]
#![deny(unsafe_code)]
//! Encrypting:
//! ```rust
//! let key_bytes = [0u8; 16];
//! const MSG_LEN: usize = 19;
//!
//! use libcrux_aesgcm::{NONCE_LEN, TAG_LEN, aes_gcm_128::{Key, Tag, Nonce}};
//!
//! let msg: &[u8; MSG_LEN] = b"squeamish ossifrage";
//! let mut ciphertext = [0u8; MSG_LEN];
//! let mut tag = Tag::from([0u8; TAG_LEN]);
//!
//! let key = Key::from(key_bytes);
//! let nonce = Nonce::from([123u8; NONCE_LEN]);
//!
//! key.encrypt(&mut ciphertext, &mut tag, &nonce, &[/* no aad */], msg)
//!     .expect("Encryption error");
//!
//! // Ciphertext and tag contain encrypted data
//! assert_eq!(
//!     ciphertext,
//!     [ 148, 21, 176, 171, 116, 92, 185, 194,
//!       20, 107, 190, 106, 221, 127, 17, 61,
//!       209, 13, 108]
//! );
//!  assert_eq!(
//!     tag.as_ref(),
//!     &[18, 229, 81, 170, 108, 76, 43, 130, 90,
//!       229, 213, 74, 112, 243, 44, 221],
//! );
//! ```
//! Decrypting:
//! ```rust
//! let key_bytes  = [0u8; 16];
//! let ciphertext = [148, 21, 176, 171, 116, 92, 185, 194, 20, 107, 190, 106, 221, 127, 17, 61, 209, 13, 108];
//! let tag_bytes = [18, 229, 81, 170, 108, 76, 43, 130, 90, 229, 213, 74, 112, 243, 44, 221];
//! const MSG_LEN: usize = 19;
//!
//! use libcrux_aesgcm::{NONCE_LEN, TAG_LEN, aes_gcm_128::{Key, Tag, Nonce}};
//!
//! let mut plaintext = [0u8; MSG_LEN];
//! let mut tag = Tag::from(tag_bytes);
//!
//! let key = Key::from(key_bytes);
//! let nonce = Nonce::from([123u8; NONCE_LEN]);
//!
//! key.decrypt(&mut plaintext, &nonce,  &[/* no aad */], &ciphertext, &tag)
//!     .expect("Decryption error");
//!
//! assert_eq!(&plaintext, b"squeamish ossifrage");
//!
//! ```

#[cfg(feature = "std")]
extern crate std;

mod aes;
mod ctr;
mod gf128;
mod platform;

mod traits_api;

mod aes_gcm;
pub mod aes_gcm_128;
pub mod aes_gcm_256;

use libcrux_traits::aead::{arrayref, consts, slice, typed_owned};

/// Trait for an AES State.
/// Implemented for 128 and 256.
pub(crate) trait State {
    fn init(key: &[u8]) -> Self;
    fn set_nonce(&mut self, nonce: &[u8]);
    fn encrypt(&mut self, aad: &[u8], plaintext: &[u8], ciphertext: &mut [u8], tag: &mut [u8]);
    fn decrypt(
        &mut self,
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8],
        plaintext: &mut [u8],
    ) -> Result<(), DecryptError>;
}

/// AES-GCM decryption error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecryptError();

pub(crate) mod implementations {

    #[cfg(doc)]
    use super::{aes_gcm_128, aes_gcm_256};

    /// AES-GCM 128.
    ///
    /// For details on usage, see [`aes_gcm_128`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct AesGcm128;

    /// Portable AES-GCM 128.
    ///
    /// For details on usage, see [`aes_gcm_128`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct PortableAesGcm128;

    #[cfg(feature = "simd128")]
    #[derive(Clone, Copy, PartialEq, Eq)]
    /// Neon AES-GCM 128.
    ///
    /// For details on usage, see [`aes_gcm_128`].
    pub struct NeonAesGcm128;
    #[cfg(not(feature = "simd128"))]
    /// Neon AES-GCM 128.
    ///
    /// For details on usage, see [`aes_gcm_128`].
    pub type NeonAesGcm128 = PortableAesGcm128;

    /// AES-NI AES-GCM 128.
    ///
    /// For details on usage, see [`aes_gcm_128`].
    #[cfg(feature = "simd256")]
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct X64AesGcm128;
    #[cfg(not(feature = "simd256"))]
    /// AES-NI AES-GCM 128.
    ///
    /// For details on usage, see [`aes_gcm_128`].
    pub type X64AesGcm128 = PortableAesGcm128;

    /// AES-GCM 256.
    ///
    /// For details on usage, see [`aes_gcm_256`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct AesGcm256;

    /// Portable AES-GCM 256.
    ///
    /// For details on usage, see [`aes_gcm_256`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct PortableAesGcm256;

    /// Neon AES-GCM 256.
    ///
    /// For details on usage, see [`aes_gcm_256`].
    #[cfg(feature = "simd128")]
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct NeonAesGcm256;

    /// Neon AES-GCM 256.
    ///
    /// For details on usage, see [`aes_gcm_256`].
    #[cfg(not(feature = "simd128"))]
    pub type NeonAesGcm256 = PortableAesGcm256;

    /// AES-NI AES-GCM 256.
    ///
    /// For details on usage, see [`aes_gcm_256`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    #[cfg(feature = "simd256")]
    pub struct X64AesGcm256;

    /// AES-NI AES-GCM 256.
    ///
    /// For details on usage, see [`aes_gcm_256`].
    #[cfg(not(feature = "simd256"))]
    pub type X64AesGcm256 = PortableAesGcm256;
}
pub use implementations::*;

/// Tag length.
pub const TAG_LEN: usize = 16;

/// Nonce length.
pub const NONCE_LEN: usize = 12;

/// Generic AES-GCM encrypt.
pub(crate) fn encrypt<S: State>(
    key: &[u8],
    nonce: &[u8],
    aad: &[u8],
    plaintext: &[u8],
    ciphertext: &mut [u8],
    tag: &mut [u8],
) {
    debug_assert!(nonce.len() == NONCE_LEN);
    debug_assert!(tag.len() == TAG_LEN);

    let mut st = S::init(key);
    st.set_nonce(nonce);
    st.encrypt(aad, plaintext, ciphertext, tag);
}

/// Generic AES-GCM decrypt.
pub(crate) fn decrypt<S: State>(
    key: &[u8],
    nonce: &[u8],
    aad: &[u8],
    ciphertext: &[u8],
    tag: &[u8],
    plaintext: &mut [u8],
) -> Result<(), DecryptError> {
    debug_assert!(nonce.len() == NONCE_LEN);
    debug_assert!(tag.len() == TAG_LEN);

    let mut st = S::init(key);
    st.set_nonce(nonce);
    st.decrypt(aad, ciphertext, tag, plaintext)
}

/// Macro to instantiate the different variants, both 128/256 and platforms.
macro_rules! pub_crate_mod {
    ($variant_comment:literal, $mod_name:ident, $state:ty) => {
        #[doc = $variant_comment]
        pub mod $mod_name {
            use crate::$mod_name::KEY_LEN;
            use crate::{platform, DecryptError};

            type State = $state;

            #[doc = $variant_comment]
            /// encrypt.
            pub fn encrypt(
                key: &[u8],
                nonce: &[u8],
                aad: &[u8],
                plaintext: &[u8],
                ciphertext: &mut [u8],
                tag: &mut [u8],
            ) {
                debug_assert!(key.len() == KEY_LEN);
                crate::encrypt::<State>(key, nonce, aad, plaintext, ciphertext, tag);
            }

            #[doc = $variant_comment]
            /// decrypt.
            pub fn decrypt(
                key: &[u8],
                nonce: &[u8],
                aad: &[u8],
                ciphertext: &[u8],
                tag: &[u8],
                plaintext: &mut [u8],
            ) -> Result<(), DecryptError> {
                debug_assert!(key.len() == KEY_LEN);
                crate::decrypt::<State>(key, nonce, aad, ciphertext, tag, plaintext)
            }
        }
    };
}

pub(crate) mod portable {
    pub_crate_mod!(r"AES-GCM 128 ", aes_gcm_128, crate::aes_gcm_128::State<platform::portable::State, platform::portable::FieldElement>);
    pub_crate_mod!(r"AES-GCM 256 ", aes_gcm_256, crate::aes_gcm_256::State<platform::portable::State, platform::portable::FieldElement>);
}

#[cfg(feature = "simd128")]
pub(crate) mod neon {
    pub_crate_mod!(r"AES-GCM 128 ", aes_gcm_128, crate::aes_gcm_128::State<platform::neon::State, platform::neon::FieldElement>);
    pub_crate_mod!(r"AES-GCM 256 ", aes_gcm_256, crate::aes_gcm_256::State<platform::neon::State, platform::neon::FieldElement>);
}

#[cfg(feature = "simd256")]
pub(crate) mod x64 {
    // Here we don't use the `pub_crate_mod` macro because we need to add target features
    // onto the functions.
    macro_rules! x64_pub_crate_mod {
        ($variant_comment:literal, $mod_name:ident, $state:ty) => {
            #[doc = $variant_comment]
            pub mod $mod_name {
                use crate::$mod_name::KEY_LEN;
                use crate::{platform, DecryptError};

                type State = $state;

                #[doc = $variant_comment]
                /// encrypt.
                pub fn encrypt(
                    key: &[u8],
                    nonce: &[u8],
                    aad: &[u8],
                    plaintext: &[u8],
                    ciphertext: &mut [u8],
                    tag: &mut [u8],
                ) {
                    debug_assert!(key.len() == KEY_LEN);

                    #[inline]
                    #[target_feature(enable = "avx2", enable = "aes")]
                    #[allow(unsafe_code)]
                    unsafe fn inner(
                        key: &[u8],
                        nonce: &[u8],
                        aad: &[u8],
                        plaintext: &[u8],
                        ciphertext: &mut [u8],
                        tag: &mut [u8],
                    ) {
                        crate::encrypt::<State>(key, nonce, aad, plaintext, ciphertext, tag);
                    }

                    #[allow(unsafe_code)]
                    unsafe {
                        inner(key, nonce, aad, plaintext, ciphertext, tag)
                    };
                }

                #[doc = $variant_comment]
                /// decrypt.
                pub fn decrypt(
                    key: &[u8],
                    nonce: &[u8],
                    aad: &[u8],
                    ciphertext: &[u8],
                    tag: &[u8],
                    plaintext: &mut [u8],
                ) -> Result<(), DecryptError> {
                    debug_assert!(key.len() == KEY_LEN);

                    #[inline]
                    #[target_feature(enable = "avx2", enable = "aes")]
                    #[allow(unsafe_code)]
                    unsafe fn inner(
                        key: &[u8],
                        nonce: &[u8],
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &[u8],
                        plaintext: &mut [u8],
                    ) -> Result<(), DecryptError> {
                        crate::decrypt::<State>(key, nonce, aad, ciphertext, tag, plaintext)
                    }

                    #[allow(unsafe_code)]
                    unsafe {
                        inner(key, nonce, aad, ciphertext, tag, plaintext)
                    }
                }
            }
        };
    }

    x64_pub_crate_mod!(r"AES-GCM 128 ", aes_gcm_128, crate::aes_gcm_128::State<platform::x64::State, platform::x64::FieldElement>);
    x64_pub_crate_mod!(r"AES-GCM 256 ", aes_gcm_256, crate::aes_gcm_256::State<platform::x64::State, platform::x64::FieldElement>);
}

#[doc(inline)]
pub use aes_gcm_128::KEY_LEN as AES_GCM_128_KEY_LEN;
#[doc(inline)]
pub use aes_gcm_256::KEY_LEN as AES_GCM_256_KEY_LEN;
