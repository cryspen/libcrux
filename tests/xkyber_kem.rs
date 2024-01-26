mod test_util;

use libcrux::{
    hpke::{
        self,
        aead::AEAD,
        kdf::KDF,
        kem::{GenerateKeyPair, KEM},
        HPKECiphertext, HPKEConfig, HpkeOpen, HpkeSeal,
    },
    kem::{self, Algorithm},
};

#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg;
#[cfg(target_arch = "wasm32")]
use rand_core::OsRng;
use rand_core::RngCore;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn xkyber_selftest() {
    let _ = pretty_env_logger::try_init();

    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let (skr, pkr) = kem::key_gen(Algorithm::X25519MlKem768Draft00, &mut rng).unwrap();

    let (ss, ct) = pkr.encapsulate(&mut rng).unwrap();
    let rss = ct.decapsulate(&skr).unwrap();

    assert_eq!(rss.encode(), ss.encode());
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn xkyber_hpke_selftest() {
    let _ = pretty_env_logger::try_init();

    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let config = HPKEConfig(
        hpke::Mode::mode_base,
        KEM::X25519Kyber768Draft00,
        KDF::HKDF_SHA256,
        AEAD::ChaCha20Poly1305,
    );

    let mut randomness = vec![0u8; 64];
    rng.fill_bytes(&mut randomness);
    let (sk_r, pk_r) = GenerateKeyPair(KEM::X25519Kyber768Draft00, randomness).unwrap();

    let info = b"xkyber hpke selftest info";
    let aad = b"xkyber hpke selftest aad";
    let ptxt = b"xkyber hpke selftest plaintext";

    let mut randomness = vec![0u8; 64];
    rng.fill_bytes(&mut randomness);

    let HPKECiphertext(enc, ct) =
        HpkeSeal(config, &pk_r, info, aad, ptxt, None, None, None, randomness)
            .expect("Error in hpke seal");

    let decrypted_ptxt = HpkeOpen(
        config,
        &HPKECiphertext(enc, ct),
        &sk_r,
        info,
        aad,
        None,
        None,
        None,
    )
    .expect("Error opening hpke ciphertext");

    assert_eq!(ptxt, decrypted_ptxt.as_slice());
}
