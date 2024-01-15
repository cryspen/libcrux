//! # WASM API

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn sha256(s: &[u8]) -> Vec<u8> {
    crate::digest::sha2_256(s).to_vec()
}

use crate::hpke::{aead::*, kdf::*, kem::*, *};

pub const X25519_SHA2_256_CHACHA: (Mode, KEM, KDF, AEAD) = (
    Mode::mode_base,
    KEM::DHKEM_X25519_HKDF_SHA256,
    KDF::HKDF_SHA256,
    AEAD::ChaCha20Poly1305,
);

pub const KYBER768_X25519_SHA2_256_CHACHA: (Mode, KEM, KDF, AEAD) = (
    Mode::mode_base,
    KEM::X25519Kyber768Draft00,
    KDF::HKDF_SHA256,
    AEAD::ChaCha20Poly1305,
);

/// ## WASM key gen API.
///
/// This function exposes a simplified API to be called from WASM and panics on
/// any error.
///
/// It generates keys sk||pk.
#[wasm_bindgen]
pub fn hpke_key_gen(randomness: &[u8]) -> Vec<u8> {
    let (mut sk, mut pk) =
        GenerateKeyPair(KEM::X25519Kyber768Draft00, randomness.to_vec()).unwrap();
    sk.append(&mut pk);
    sk
}

/// ## WASM single-shot HPKE seal.
///
/// This function exposes a simplified API to be called from WASM and panics on
/// any error.
///
/// It uses x25519kyber768 as KEM, SHA256 as hash function and Chacha20Poly1305 as AEAD.
#[wasm_bindgen]
pub fn hpke_seal_base(
    pk_r: &[u8],
    info: &[u8],
    aad: &[u8],
    pt: &[u8],
    randomness: &[u8],
) -> Vec<u8> {
    let HPKECiphertext(mut enc, mut ct) = HpkeSeal(
        HPKEConfig(
            Mode::mode_base,
            KEM::X25519Kyber768Draft00,
            KDF::HKDF_SHA256,
            AEAD::ChaCha20Poly1305,
        ),
        pk_r,
        info,
        aad,
        pt,
        None,
        None,
        None,
        randomness.to_vec(),
    )
    .unwrap();
    enc.append(&mut ct);
    enc
}

/// ## WASM single-shot HPKE open.
///
/// This function exposes a simplified API to be called from WASM and panics on
/// any error.
///
/// It uses x25519 as KEM, SHA256 as hash function and Chacha20Poly1305 as AEAD.
#[wasm_bindgen]
pub fn hpke_open_base(ctxt: &[u8], enc: &[u8], sk_r: &[u8], info: &[u8], aad: &[u8]) -> Vec<u8> {
    let ct = HPKECiphertext(enc.to_vec(), ctxt.to_vec());
    let pt = HpkeOpen(
        HPKEConfig(
            Mode::mode_base,
            KEM::X25519Kyber768Draft00,
            KDF::HKDF_SHA256,
            AEAD::ChaCha20Poly1305,
        ),
        &ct,
        sk_r,
        info,
        aad,
        None,
        None,
        None,
    )
    .unwrap();
    pt
}
