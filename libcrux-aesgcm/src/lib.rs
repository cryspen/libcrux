pub mod aes_ctr;
mod aes_gcm;
mod aes_generic;
mod gf128_generic;
pub mod platform;

pub use aes_gcm::DecryptError;

pub mod portable{
    use crate::{aes_gcm::{self, DecryptError}, platform};

    pub fn aes128_gcm_encrypt(key: &[u8], nonce: &[u8], aad: &[u8], plaintext: &[u8], ciphertext: &mut [u8], tag: &mut [u8]){
        let mut st = aes_gcm::aes128_gcm_init::<platform::portable::State,platform::portable::FieldElement>(key);
        aes_gcm::aes128_gcm_set_nonce(&mut st, nonce);
        aes_gcm::aes128_gcm_encrypt(&mut st, aad, plaintext, ciphertext, tag);
    }

    pub fn aes128_gcm_decrypt(key: &[u8], nonce: &[u8], aad: &[u8], ciphertext: &[u8], tag: &[u8], plaintext: &mut [u8]) -> Result<(), DecryptError>{
        let mut st = aes_gcm::aes128_gcm_init::<platform::portable::State,platform::portable::FieldElement>(key);
        aes_gcm::aes128_gcm_set_nonce(&mut st, nonce);
        aes_gcm::aes128_gcm_decrypt(&mut st, aad, ciphertext, tag, plaintext)
    }
}

#[cfg(all(target_arch = "aarch64", target_feature="aes"))]
pub mod neon{
    use crate::{aes_gcm::{self, DecryptError}, platform};

    pub fn aes128_gcm_encrypt(key: &[u8], nonce: &[u8], aad: &[u8], plaintext: &[u8], ciphertext: &mut [u8], tag: &mut [u8]){
        let mut st = aes_gcm::aes128_gcm_init::<platform::neon::State,platform::neon::FieldElement>(key);
        aes_gcm::aes128_gcm_set_nonce(&mut st, nonce);
        aes_gcm::aes128_gcm_encrypt(&mut st, aad, plaintext, ciphertext, tag);
    }

    pub fn aes128_gcm_decrypt(key: &[u8], nonce: &[u8], aad: &[u8], ciphertext: &[u8], tag: &[u8], plaintext: &mut [u8]) -> Result<(), DecryptError>{
        let mut st = aes_gcm::aes128_gcm_init::<platform::neon::State,platform::neon::FieldElement>(key);
        aes_gcm::aes128_gcm_set_nonce(&mut st, nonce);
        aes_gcm::aes128_gcm_decrypt(&mut st, aad, ciphertext, tag, plaintext)
    }
}