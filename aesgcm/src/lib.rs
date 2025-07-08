mod aes_ctr;
mod aes_generic;
mod gf128_generic;
mod platform;

mod aes_gcm_128;
mod aes_gcm_256;

pub use libcrux_traits::aead::arrayref::Aead;

/// AES-GCM decryption error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecryptError();

/// AES-GCM 128.
pub struct AesGcm128 {}

/// Portable AES-GCM 128.
pub struct PortableAesGcm128 {}

/// Neon AES-GCM 128.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub struct NeonAesGcm128 {}
#[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
pub type NeonAesGcm128 = PortableAesGcm128;

/// AES-NI AES-GCM 128.
#[cfg(target_arch = "x86_64")]
pub struct X64AesGcm128 {}
#[cfg(not(target_arch = "x86_64"))]
pub type X64AesGcm128 = PortableAesGcm128;

/// Tag length.
pub(crate) const TAG_LEN: usize = 16;

/// Nonce length.
pub(crate) const NONCE_LEN: usize = 12;

mod aes128 {
    use super::*;
    use aes_gcm_128::KEY_LEN;
    use libcrux_traits::aead::arrayref::{DecryptError, EncryptError};

    pub type Key = [u8; KEY_LEN];
    pub type Tag = [u8; TAG_LEN];
    pub type Nonce = [u8; NONCE_LEN];

    impl Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for AesGcm128 {
        fn encrypt(
            ciphertext: &mut [u8],
            tag: &mut Tag,
            key: &Key,
            nonce: &Nonce,
            aad: &[u8],
            plaintext: &[u8],
        ) -> Result<(), EncryptError> {
            if libcrux_platform::simd128_support() && libcrux_platform::aes_ni_support() {
                NeonAesGcm128::encrypt(ciphertext, tag, key, nonce, aad, plaintext)
            } else if libcrux_platform::simd256_support() && libcrux_platform::aes_ni_support() {
                X64AesGcm128::encrypt(ciphertext, tag, key, nonce, aad, plaintext)
            } else {
                PortableAesGcm128::encrypt(ciphertext, tag, key, nonce, aad, plaintext)
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
            if libcrux_platform::simd128_support() && libcrux_platform::aes_ni_support() {
                NeonAesGcm128::decrypt(plaintext, key, nonce, aad, ciphertext, tag)
            } else if libcrux_platform::simd256_support() && libcrux_platform::aes_ni_support() {
                X64AesGcm128::decrypt(plaintext, key, nonce, aad, ciphertext, tag)
            } else {
                PortableAesGcm128::decrypt(plaintext, key, nonce, aad, ciphertext, tag)
            }
        }
    }

    impl Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for PortableAesGcm128 {
        fn encrypt(
            ciphertext: &mut [u8],
            tag: &mut Tag,
            key: &Key,
            nonce: &Nonce,
            aad: &[u8],
            plaintext: &[u8],
        ) -> Result<(), EncryptError> {
            portable::aes128_gcm_encrypt(key, nonce, aad, plaintext, ciphertext, tag);
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
            portable::aes128_gcm_decrypt(key, nonce, aad, ciphertext, tag, plaintext)
                .map_err(|_| DecryptError::InvalidTag)
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    impl Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for NeonAesGcm128 {
        fn encrypt(
            ciphertext: &mut [u8],
            tag: &mut Tag,
            key: &Key,
            nonce: &Nonce,
            aad: &[u8],
            plaintext: &[u8],
        ) -> Result<(), EncryptError> {
            neon::aes128_gcm_encrypt(key, nonce, aad, plaintext, ciphertext, tag);
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
            neon::aes128_gcm_decrypt(key, nonce, aad, ciphertext, tag, plaintext)
                .map_err(|_| DecryptError::InvalidTag)
        }
    }
}

pub mod portable {
    use crate::{
        aes_gcm_128::{self},
        aes_gcm_256::{self},
        platform, DecryptError, NONCE_LEN, TAG_LEN,
    };

    // XXX: It doesn't really make sense to have these states. We should abstract
    // this differently

    type Aes128State =
        aes_gcm_128::State<platform::portable::State, platform::portable::FieldElement>;

    type Aes256State =
        aes_gcm_256::State<platform::portable::State, platform::portable::FieldElement>;

    pub fn aes128_gcm_encrypt(
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[u8],
        ciphertext: &mut [u8],
        tag: &mut [u8],
    ) {
        debug_assert!(key.len() == aes_gcm_128::KEY_LEN);
        debug_assert!(nonce.len() == NONCE_LEN);
        debug_assert!(tag.len() == TAG_LEN);

        let mut st = Aes128State::init(key);
        st.set_nonce(nonce);
        st.encrypt(aad, plaintext, ciphertext, tag);
    }

    pub fn aes128_gcm_decrypt(
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8],
        plaintext: &mut [u8],
    ) -> Result<(), DecryptError> {
        debug_assert!(key.len() == aes_gcm_128::KEY_LEN);
        debug_assert!(nonce.len() == NONCE_LEN);
        debug_assert!(tag.len() == TAG_LEN);

        let mut st = Aes128State::init(key);
        st.set_nonce(nonce);
        st.decrypt(aad, ciphertext, tag, plaintext)
    }

    pub fn aes256_gcm_encrypt(
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[u8],
        ciphertext: &mut [u8],
        tag: &mut [u8],
    ) {
        debug_assert!(key.len() == aes_gcm_256::KEY_LEN);
        debug_assert!(nonce.len() == NONCE_LEN);
        debug_assert!(tag.len() == TAG_LEN);

        let mut st = Aes256State::init(key);
        st.set_nonce(nonce);
        st.encrypt(aad, plaintext, ciphertext, tag);
    }

    pub fn aes256_gcm_decrypt(
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8],
        plaintext: &mut [u8],
    ) -> Result<(), DecryptError> {
        debug_assert!(key.len() == aes_gcm_256::KEY_LEN);
        debug_assert!(nonce.len() == NONCE_LEN);
        debug_assert!(tag.len() == TAG_LEN);

        let mut st = Aes256State::init(key);
        st.set_nonce(nonce);
        st.decrypt(aad, ciphertext, tag, plaintext)
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod neon {
    use crate::{platform, DecryptError};

    type State = crate::aes_gcm_128::State<platform::neon::State, platform::neon::FieldElement>;

    pub fn aes128_gcm_encrypt(
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[u8],
        ciphertext: &mut [u8],
        tag: &mut [u8],
    ) {
        let mut st = State::init(key);
        st.set_nonce(nonce);
        st.encrypt(aad, plaintext, ciphertext, tag);
    }

    pub fn aes128_gcm_decrypt(
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8],
        plaintext: &mut [u8],
    ) -> Result<(), DecryptError> {
        let mut st = State::init(key);
        st.set_nonce(nonce);
        st.decrypt(aad, ciphertext, tag, plaintext)
    }
}

#[cfg(target_arch = "x86_64")] // REENABLE target_feature="aes"
pub mod intel_ni {
    use crate::{
        aes_gcm::{self, DecryptError},
        platform,
    };

    pub fn aes128_gcm_encrypt(
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[u8],
        ciphertext: &mut [u8],
        tag: &mut [u8],
    ) {
        let mut st = aes_gcm::aes128_gcm_init::<
            platform::intel_ni::State,
            platform::intel_ni::FieldElement,
        >(key);
        aes_gcm::aes128_gcm_set_nonce(&mut st, nonce);
        aes_gcm::aes128_gcm_encrypt(&mut st, aad, plaintext, ciphertext, tag);
    }

    pub fn aes128_gcm_decrypt(
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8],
        plaintext: &mut [u8],
    ) -> Result<(), DecryptError> {
        let mut st = aes_gcm::aes128_gcm_init::<
            platform::intel_ni::State,
            platform::intel_ni::FieldElement,
        >(key);
        aes_gcm::aes128_gcm_set_nonce(&mut st, nonce);
        aes_gcm::aes_gcm_128::aes128_gcm_decrypt(&mut st, aad, ciphertext, tag, plaintext)
    }
}
