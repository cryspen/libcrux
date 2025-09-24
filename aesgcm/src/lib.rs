#![no_std]
#![deny(unsafe_code)]

#[cfg(feature = "std")]
extern crate std;

mod aes;
mod ctr;
mod gf128;
mod platform;

mod aes_gcm;
mod aes_gcm_128;
mod aes_gcm_256;

use libcrux_traits::aead::{arrayref, consts, slice, typed_owned};

// TODO: should this trait be re-exported here?
pub use libcrux_traits::aead::arrayref::Aead;

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

/// AES-GCM 128.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AesGcm128;

/// Portable AES-GCM 128.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PortableAesGcm128;

/// Neon AES-GCM 128.
#[cfg(feature = "simd128")]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NeonAesGcm128;
#[cfg(not(feature = "simd128"))]
pub type NeonAesGcm128 = PortableAesGcm128;

/// AES-NI AES-GCM 128.
#[cfg(feature = "simd256")]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct X64AesGcm128;
#[cfg(not(feature = "simd256"))]
pub type X64AesGcm128 = PortableAesGcm128;

/// AES-GCM 256.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AesGcm256;

/// Portable AES-GCM 256.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PortableAesGcm256;

/// Neon AES-GCM 256.
#[cfg(feature = "simd128")]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NeonAesGcm256;

/// Neon AES-GCM 256.
#[cfg(not(feature = "simd128"))]
pub type NeonAesGcm256 = PortableAesGcm256;

/// AES-NI AES-GCM 256.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg(feature = "simd256")]
pub struct X64AesGcm256;

/// AES-NI AES-GCM 256.
#[cfg(not(feature = "simd256"))]
pub type X64AesGcm256 = PortableAesGcm256;

/// Tag length.
pub(crate) const TAG_LEN: usize = 16;

/// Nonce length.
pub(crate) const NONCE_LEN: usize = 12;

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
macro_rules! pub_mod {
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

pub mod portable {
    pub_mod!(r"AES-GCM 128 ", aes_gcm_128, crate::aes_gcm_128::State<platform::portable::State, platform::portable::FieldElement>);
    pub_mod!(r"AES-GCM 256 ", aes_gcm_256, crate::aes_gcm_256::State<platform::portable::State, platform::portable::FieldElement>);
}

#[cfg(feature = "simd128")]
pub mod neon {
    pub_mod!(r"AES-GCM 128 ", aes_gcm_128, crate::aes_gcm_128::State<platform::neon::State, platform::neon::FieldElement>);
    pub_mod!(r"AES-GCM 256 ", aes_gcm_256, crate::aes_gcm_256::State<platform::neon::State, platform::neon::FieldElement>);
}

#[cfg(feature = "simd256")]
pub mod x64 {
    // Here we don't use the `pub_mod` macro because we need to add target features
    // onto the functions.
    macro_rules! x64_pub_mod {
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

    x64_pub_mod!(r"AES-GCM 128 ", aes_gcm_128, crate::aes_gcm_128::State<platform::x64::State, platform::x64::FieldElement>);
    x64_pub_mod!(r"AES-GCM 256 ", aes_gcm_256, crate::aes_gcm_256::State<platform::x64::State, platform::x64::FieldElement>);
}

/// Macro to implement the libcrux_traits public API traits
///
/// For the blanket impl of `typed_refs::Aead` to take place,
/// the `$type` must implement `Copy` and `PartialEq`.
macro_rules! impl_traits_public_api {
    ($type:ty, $keylen:expr, $taglen:expr, $noncelen:expr ) => {
        // prerequisite for typed_owned::Aead
        impl consts::AeadConsts for $type {
            const KEY_LEN: usize = KEY_LEN;
            const TAG_LEN: usize = TAG_LEN;
            const NONCE_LEN: usize = NONCE_LEN;
        }
        // implement typed_owned::Aead
        typed_owned::impl_aead_typed_owned!($type, KEY_LEN, TAG_LEN, NONCE_LEN);
    };
}

/// Macro to implement the different structs and multiplexing.
macro_rules! api {
    ($mod_name:ident, $variant:ident, $multiplexing:ty, $portable:ident, $neon:ident, $x64:ident) => {
        mod $mod_name {
            use super::*;
            use libcrux_traits::aead::arrayref::{DecryptError, EncryptError};
            use $variant::KEY_LEN;

            pub type Key = [u8; KEY_LEN];
            pub type Tag = [u8; TAG_LEN];
            pub type Nonce = [u8; NONCE_LEN];

            // implement `libcrux_traits` slice trait
            slice::impl_aead_slice_trait!($multiplexing => KEY_LEN, TAG_LEN, NONCE_LEN);

            // implement `libcrux_traits` public API traits
            impl_traits_public_api!($multiplexing, KEY_LEN, TAG_LEN, NONCE_LEN);

            impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $multiplexing {
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

            // implement `libcrux_traits` slice trait
            slice::impl_aead_slice_trait!($portable => KEY_LEN, TAG_LEN, NONCE_LEN);

            // implement `libcrux_traits` public API traits
            impl_traits_public_api!($portable, KEY_LEN, TAG_LEN, NONCE_LEN);

            impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $portable {
                fn encrypt(
                    ciphertext: &mut [u8],
                    tag: &mut Tag,
                    key: &Key,
                    nonce: &Nonce,
                    aad: &[u8],
                    plaintext: &[u8],
                ) -> Result<(), EncryptError> {
                    portable::$variant::encrypt(key, nonce, aad, plaintext, ciphertext, tag);
                    Ok(())
                }

                fn decrypt(
                    plaintext: &mut [u8],
                    key: &Key,
                    nonce: &Nonce,
                    aad: &[u8],
                    ciphertext: &[u8],
                    tag: &Tag,
                ) -> Result<(), DecryptError> {
                    portable::$variant::decrypt(key, nonce, aad, ciphertext, tag, plaintext)
                        .map_err(|_| DecryptError::InvalidTag)
                }
            }

            // implement `libcrux_traits` slice trait
            #[cfg(feature = "simd128")]
            slice::impl_aead_slice_trait!($neon => KEY_LEN, TAG_LEN, NONCE_LEN);

            // implement `libcrux_traits` public API traits
            #[cfg(feature = "simd128")]
            impl_traits_public_api!($neon, KEY_LEN, TAG_LEN, NONCE_LEN);

            #[cfg(feature = "simd128")]
            impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $neon {
                fn encrypt(
                    ciphertext: &mut [u8],
                    tag: &mut Tag,
                    key: &Key,
                    nonce: &Nonce,
                    aad: &[u8],
                    plaintext: &[u8],
                ) -> Result<(), EncryptError> {
                    neon::$variant::encrypt(key, nonce, aad, plaintext, ciphertext, tag);
                    Ok(())
                }

                fn decrypt(
                    plaintext: &mut [u8],
                    key: &Key,
                    nonce: &Nonce,
                    aad: &[u8],
                    ciphertext: &[u8],
                    tag: &Tag,
                ) -> Result<(), DecryptError> {
                    neon::$variant::decrypt(key, nonce, aad, ciphertext, tag, plaintext)
                        .map_err(|_| DecryptError::InvalidTag)
                }
            }

            // implement `libcrux_traits` slice trait
            #[cfg(feature = "simd256")]
            slice::impl_aead_slice_trait!($x64 => KEY_LEN, TAG_LEN, NONCE_LEN);

            // implement `libcrux_traits` public API traits
            #[cfg(feature = "simd256")]
            impl_traits_public_api!($x64, KEY_LEN, TAG_LEN, NONCE_LEN);

            #[cfg(feature = "simd256")]
            impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $x64 {
                fn encrypt(
                    ciphertext: &mut [u8],
                    tag: &mut Tag,
                    key: &Key,
                    nonce: &Nonce,
                    aad: &[u8],
                    plaintext: &[u8],
                ) -> Result<(), EncryptError> {
                    x64::$variant::encrypt(key, nonce, aad, plaintext, ciphertext, tag);
                    Ok(())
                }

                fn decrypt(
                    plaintext: &mut [u8],
                    key: &Key,
                    nonce: &Nonce,
                    aad: &[u8],
                    ciphertext: &[u8],
                    tag: &Tag,
                ) -> Result<(), DecryptError> {
                    x64::$variant::decrypt(key, nonce, aad, ciphertext, tag, plaintext)
                        .map_err(|_| DecryptError::InvalidTag)
                }
            }
        }
    };
}

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

#[cfg(test)]
mod tests {
    use libcrux_traits::aead::consts;
    use libcrux_traits::aead::typed_owned;
    use libcrux_traits::aead::typed_refs;

    type Key = typed_owned::Key<super::AesGcm128>;
    type Nonce = typed_owned::Nonce<super::AesGcm128>;
    type Tag = typed_owned::Tag<super::AesGcm128>;

    #[test]
    fn test_key_centric_owned() {
        use consts::AeadConsts as _;

        use super::AesGcm128;

        let k: Key = [0; AesGcm128::KEY_LEN].into();
        let nonce: Nonce = [0; AesGcm128::NONCE_LEN].into();
        let mut tag: Tag = [0; AesGcm128::TAG_LEN].into();

        let pt = b"the quick brown fox jumps over the lazy dog";
        let mut ct = [0; 43];
        let mut pt_out = [0; 43];

        k.encrypt(&mut ct, &mut tag, &nonce, b"", pt).unwrap();
        k.decrypt(&mut pt_out, &nonce, b"", &ct, &tag).unwrap();
        assert_eq!(pt, &pt_out);
    }

    #[test]
    fn test_key_centric_refs() {
        use consts::AeadConsts as _;
        use typed_refs::Aead as _;

        use super::AesGcm128;

        let algo = AesGcm128;

        let mut tag_bytes = [0; AesGcm128::TAG_LEN];
        let key = algo.new_key(&[0; AesGcm128::KEY_LEN]).unwrap();
        let tag = algo.new_tag_mut(&mut tag_bytes).unwrap();
        let nonce = algo.new_nonce(&[0; AesGcm128::NONCE_LEN]).unwrap();

        let pt = b"the quick brown fox jumps over the lazy dog";
        let mut ct = [0; 43];
        let mut pt_out = [0; 43];

        key.encrypt(&mut ct, tag, nonce, b"", pt).unwrap();
        let tag = algo.new_tag(&tag_bytes).unwrap();
        key.decrypt(&mut pt_out, nonce, b"", &ct, tag).unwrap();
        assert_eq!(pt, &pt_out);
    }
}
