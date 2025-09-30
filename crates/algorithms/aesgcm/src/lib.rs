//! AES-GCM.
//!
//! This crate provides separate modules for neon and x64.
//!  - Neon: [`aes_gcm_128::neon`], [`aes_gcm_256::neon`]
//!  - x64: [`aes_gcm_128::x64`], [`aes_gcm_128::x64`]
//!
#![no_std]
#![deny(unsafe_code)]
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
    /// For more information on usage, see [`aes_gcm_128`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct AesGcm128;

    /// Portable AES-GCM 128.
    ///
    /// For more information on usage, see [`aes_gcm_128::portable`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct PortableAesGcm128;

    #[cfg(feature = "simd128")]
    #[derive(Clone, Copy, PartialEq, Eq)]
    /// Neon AES-GCM 128.
    ///
    /// For more information on usage, see [`aes_gcm_128::neon`].
    pub struct NeonAesGcm128;
    #[cfg(not(feature = "simd128"))]
    /// Neon AES-GCM 128.
    ///
    /// For more information on usage, see [`aes_gcm_128::neon`].
    pub type NeonAesGcm128 = PortableAesGcm128;

    /// AES-NI AES-GCM 128.
    ///
    /// For more information on usage, see [`aes_gcm_128::x64`].
    #[cfg(feature = "simd256")]
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct X64AesGcm128;
    #[cfg(not(feature = "simd256"))]
    /// AES-NI AES-GCM 128.
    ///
    /// For more information on usage, see [`aes_gcm_128::x64`].
    pub type X64AesGcm128 = PortableAesGcm128;

    /// AES-GCM 256.
    ///
    /// For more information on usage, see [`aes_gcm_256`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct AesGcm256;

    /// Portable AES-GCM 256.
    ///
    /// For more information on usage, see [`aes_gcm_256::portable`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct PortableAesGcm256;

    /// Neon AES-GCM 256.
    ///
    /// For more information on usage, see [`aes_gcm_256::neon`].
    #[cfg(feature = "simd128")]
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct NeonAesGcm256;

    /// Neon AES-GCM 256.
    ///
    /// For more information on usage, see [`aes_gcm_256::neon`].
    #[cfg(not(feature = "simd128"))]
    pub type NeonAesGcm256 = PortableAesGcm256;

    /// AES-NI AES-GCM 256.
    ///
    /// For more information on usage, see [`aes_gcm_256::x64`].
    #[derive(Clone, Copy, PartialEq, Eq)]
    #[cfg(feature = "simd256")]
    pub struct X64AesGcm256;

    /// AES-NI AES-GCM 256.
    ///
    /// For more information on usage, see [`aes_gcm_256::x64`].
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

// traits re-exports
pub use libcrux_traits::aead::consts::AeadConsts;
pub use libcrux_traits::aead::typed_refs::Aead;
