use crate::{
    aes_gcm_128, aes_gcm_256,
    implementations::{AesGcm128, AesGcm256, PortableAesGcm128, PortableAesGcm256},
    NONCE_LEN, TAG_LEN,
};

use libcrux_traits::aead::{arrayref, consts, slice, typed_owned};

/// Macro to implement the libcrux_traits public API traits
///
/// For the blanket impl of `typed_refs::Aead` to take place,
/// the `$type` must implement `Copy` and `PartialEq`.
macro_rules! impl_traits_public_api {
    ($type:ty, $keylen:expr, $taglen:expr, $noncelen:expr ) => {
        // prerequisite for typed_owned::Aead
        impl consts::AeadConsts for $type {
            const KEY_LEN: usize = $keylen;
            const TAG_LEN: usize = $taglen;
            const NONCE_LEN: usize = $noncelen;
        }
        // implement typed_owned::Aead
        typed_owned::impl_aead_typed_owned!($type, $keylen, $taglen, $noncelen);
    };
}

/// Macro to implement the different structs and multiplexing.
macro_rules! api {
    ($mod_name:ident, $variant:ident, $multiplexing:ty, $portable:ident, $neon:ident, $x64:ident) => {
        mod $mod_name {
            use super::*;
            use libcrux_secrets::U8;

            use libcrux_traits::aead::arrayref::{DecryptError, EncryptError, KeyGenError};
            use $variant::KEY_LEN;

            pub type Key = [u8; KEY_LEN];
            pub type Tag = [u8; TAG_LEN];
            pub type Nonce = [u8; NONCE_LEN];

            mod _libcrux_traits_apis_multiplex {
                use super::*;

                // implement `libcrux_traits` slice trait
                slice::impl_aead_slice_trait!($multiplexing => KEY_LEN, TAG_LEN, NONCE_LEN);

                // implement `libcrux_traits` public API traits
                impl_traits_public_api!($multiplexing, KEY_LEN, TAG_LEN, NONCE_LEN);

                /// The plaintext length must be equal to the ciphertext length.
                impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $multiplexing {
                    fn keygen(key: &mut [u8; KEY_LEN], rand: &[u8; KEY_LEN]) -> Result<(), KeyGenError> {
                        *key = *rand;
                        Ok(())
                    }

                    fn encrypt(
                        ciphertext: &mut [u8],
                        tag: &mut Tag,
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        plaintext: &[u8],
                    ) -> Result<(), EncryptError> {
                        // SIMD256 needs to come first because SIMD128 is true for
                        // x64 as well, but we don't actually implement it.
                        if libcrux_platform::simd256_support() && libcrux_platform::aes_ni_support() {
                            $x64::encrypt(ciphertext, tag, key, nonce, aad, plaintext)
                        } else if libcrux_platform::simd128_support()
                            && libcrux_platform::aes_ni_support()
                        {
                            $neon::encrypt(ciphertext, tag, key, nonce, aad, plaintext)
                        } else {
                            $portable::encrypt(ciphertext, tag, key, nonce, aad, plaintext)
                        }
                    }

                    fn decrypt(
                        plaintext: &mut [u8],
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &Tag,
                    ) -> Result<(), DecryptError> {
                        // SIMD256 needs to come first because SIMD128 is true for
                        // x64 as well, but we don't actually implement it.
                        if libcrux_platform::simd256_support() && libcrux_platform::aes_ni_support() {
                            $x64::decrypt(plaintext, key, nonce, aad, ciphertext, tag)
                        } else if libcrux_platform::simd128_support()
                            && libcrux_platform::aes_ni_support()
                        {
                            $neon::decrypt(plaintext, key, nonce, aad, ciphertext, tag)
                        } else {
                            $portable::decrypt(plaintext, key, nonce, aad, ciphertext, tag)
                        }
                    }
                }
            }

            mod _libcrux_traits_apis_portable {
                use super::*;

                // implement `libcrux_traits` slice trait
                slice::impl_aead_slice_trait!($portable => KEY_LEN, TAG_LEN, NONCE_LEN);

                // implement `libcrux_traits` public API traits
                impl_traits_public_api!($portable, KEY_LEN, TAG_LEN, NONCE_LEN);

                /// The plaintext length must be equal to the ciphertext length.
                impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $portable {
                    fn keygen(key: &mut [u8; KEY_LEN], rand: &[u8; KEY_LEN]) -> Result<(), KeyGenError> {
                        *key = *rand;
                        Ok(())
                    }

                    fn encrypt(
                        ciphertext: &mut [u8],
                        tag: &mut Tag,
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        plaintext: &[u8],
                    ) -> Result<(), EncryptError> {
                        crate::portable::$variant::encrypt(key, nonce, aad, plaintext, ciphertext, tag)
                    }

                    fn decrypt(
                        plaintext: &mut [u8],
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &Tag,
                    ) -> Result<(), DecryptError> {
                        crate::portable::$variant::decrypt(key, nonce, aad, ciphertext, tag, plaintext)
                    }
                }
            }

            #[cfg(feature = "simd128")]
            mod _libcrux_traits_apis_neon {
                use super::*;

                // implement `libcrux_traits` slice trait
                slice::impl_aead_slice_trait!($neon => KEY_LEN, TAG_LEN, NONCE_LEN);

                // implement `libcrux_traits` public API traits
                impl_traits_public_api!($neon, KEY_LEN, TAG_LEN, NONCE_LEN);

                /// The plaintext length must be equal to the ciphertext length.
                impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $neon {
                    fn keygen(key: &mut [u8; KEY_LEN], rand: &[u8; KEY_LEN]) -> Result<(), KeyGenError> {
                        *key = *rand;
                        Ok(())
                    }

                    fn encrypt(
                        ciphertext: &mut [u8],
                        tag: &mut Tag,
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        plaintext: &[u8],
                    ) -> Result<(), EncryptError> {
                        crate::neon::$variant::encrypt(key, nonce, aad, plaintext, ciphertext, tag)
                    }

                    fn decrypt(
                        plaintext: &mut [u8],
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &Tag,
                    ) -> Result<(), DecryptError> {
                        crate::neon::$variant::decrypt(key, nonce, aad, ciphertext, tag, plaintext)
                    }
                }
            }

            #[cfg(feature = "simd256")]
            mod _libcrux_traits_api_x64 {
                use super::*;

                // implement `libcrux_traits` slice trait
                slice::impl_aead_slice_trait!($x64 => KEY_LEN, TAG_LEN, NONCE_LEN);

                // implement `libcrux_traits` public API traits
                impl_traits_public_api!($x64, KEY_LEN, TAG_LEN, NONCE_LEN);

                /// The plaintext length must be equal to the ciphertext length.
                impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $x64 {
                    fn keygen(key: &mut [u8; KEY_LEN], rand: &[u8; KEY_LEN]) -> Result<(), KeyGenError> {
                        *key = *rand;
                        Ok(())
                    }

                    fn encrypt(
                        ciphertext: &mut [u8],
                        tag: &mut Tag,
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        plaintext: &[u8],
                    ) -> Result<(), EncryptError> {
                        crate::x64::$variant::encrypt(key, nonce, aad, plaintext, ciphertext, tag)
                    }

                    fn decrypt(
                        plaintext: &mut [u8],
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &Tag,
                    ) -> Result<(), DecryptError> {
                        crate::x64::$variant::decrypt(key, nonce, aad, ciphertext, tag, plaintext)
                    }
                }
            }
        }
    };
}

#[cfg(feature = "simd128")]
use crate::implementations::NeonAesGcm128;
#[cfg(not(feature = "simd128"))]
use crate::implementations::PortableAesGcm128 as NeonAesGcm128;

#[cfg(not(feature = "simd256"))]
use crate::implementations::PortableAesGcm128 as X64AesGcm128;
#[cfg(feature = "simd256")]
use crate::implementations::X64AesGcm128;

#[cfg(feature = "simd128")]
use crate::implementations::NeonAesGcm256;
#[cfg(not(feature = "simd128"))]
use crate::implementations::PortableAesGcm256 as NeonAesGcm256;

#[cfg(not(feature = "simd256"))]
use crate::implementations::PortableAesGcm256 as X64AesGcm256;
#[cfg(feature = "simd256")]
use crate::implementations::X64AesGcm256;

api!(
    aes128,
    aes_gcm_128,
    AesGcm128,
    PortableAesGcm128,
    NeonAesGcm128,
    X64AesGcm128
);

api!(
    aes256,
    aes_gcm_256,
    AesGcm256,
    PortableAesGcm256,
    NeonAesGcm256,
    X64AesGcm256
);
