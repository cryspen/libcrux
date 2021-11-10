#![allow(non_snake_case)]

extern crate hpke_rs as hpke;

use hpke::prelude::*;
use hpke_rs_crypto::{
    types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm},
    HpkeCrypto, RngCore,
};
use hpke_rs_evercrypt::HpkeEvercrypt;
use hpke_rs_rust_crypto::HpkeRustCrypto;
use lazy_static::lazy_static;

lazy_static! {
    static ref TEST_CASES: Vec<(Mode, KemAlgorithm, KdfAlgorithm, AeadAlgorithm)> = {
        let mut tests = Vec::new();
        for mode in 0u8..4 {
            let hpke_mode = Mode::try_from(mode).unwrap();
            for aead_mode in 1u16..4 {
                let aead_mode = AeadAlgorithm::try_from(aead_mode).unwrap();
                for kdf_mode in 1u16..4 {
                    let kdf_mode = KdfAlgorithm::try_from(kdf_mode).unwrap();
                    for &kem_mode in &[0x10u16, 0x20] {
                        let kem_mode = KemAlgorithm::try_from(kem_mode).unwrap();
                        tests.push((hpke_mode, kem_mode, kdf_mode, aead_mode));
                        println!(
                            "generate_test_case!({}, HpkeMode::{:?}, KemAlgorithm::{:?}, KdfAlgorithm::{:?}, AeadAlgorithm::{:?});",
                            Hpke::<HpkeRustCrypto>::new(hpke_mode, kem_mode, kdf_mode, aead_mode),
                            hpke_mode,
                            kem_mode,
                            kdf_mode,
                            aead_mode
                        );
                    }
                }
            }
        }
        tests
    };
}

macro_rules! generate_test_case {
    ($name:ident, $hpke_mode:expr, $kem_mode:expr, $kdf_mode:expr, $aead_mode:expr, $provider:ident) => {
        #[test]
        fn $name() {
            let hpke = Hpke::<$provider>::new($hpke_mode, $kem_mode, $kdf_mode, $aead_mode);
            println!("Self test {}", hpke);

            // Self test seal and open with random keys.
            let (sk_r, pk_r) = hpke.generate_key_pair().unwrap().into_keys();
            let (sk_s, pk_s) = hpke.generate_key_pair().unwrap().into_keys();
            let info = b"HPKE self test info";
            let aad = b"HPKE self test aad";
            let plain_txt = b"HPKE self test plain text";
            let exporter_context = b"HPKE self test exporter context";
            let mut psk = [0u8; 32];
            $provider::prng().fill_bytes(&mut psk);
            let mut psk_id = [0u8; 32];
            $provider::prng().fill_bytes(&mut psk_id);
            let (psk, psk_id): (Option<&[u8]>, Option<&[u8]>) = match $hpke_mode {
                Mode::Base | Mode::Auth => (None, None),
                Mode::Psk | Mode::AuthPsk => (Some(&psk), Some(&psk_id)),
            };
            let (sk_s_option, pk_s_option) = match $hpke_mode {
                Mode::Auth | Mode::AuthPsk => (Some(&sk_s), Some(&pk_s)),
                Mode::Psk | Mode::Base => (None, None),
            };
            let (enc, ctxt) = hpke
                .seal(&pk_r, info, aad, plain_txt, psk, psk_id, sk_s_option)
                .unwrap();
            let ptxt = hpke
                .open(&enc, &sk_r, info, aad, &ctxt, psk, psk_id, pk_s_option)
                .unwrap();
            assert_eq!(ptxt, plain_txt);

            // Exporter test
            let (enc, sender_exporter) = hpke
                .send_export(&pk_r, info, psk, psk_id, sk_s_option, exporter_context, 64)
                .unwrap();
            let receiver_exporter = hpke
                .receiver_export(
                    &enc,
                    &sk_r,
                    info,
                    psk,
                    psk_id,
                    pk_s_option,
                    exporter_context,
                    64,
                )
                .unwrap();
            assert_eq!(sender_exporter, receiver_exporter);

            // Self test with context
            let (enc, mut sender_context) = hpke
                .setup_sender(&pk_r, info, psk, psk_id, sk_s_option)
                .unwrap();
            let mut receiver_context = hpke
                .setup_receiver(&enc, &sk_r, info, psk, psk_id, pk_s_option)
                .unwrap();

            for _ in 0..17 {
                let ctxt = sender_context.seal(aad, plain_txt).unwrap();
                let ptxt = receiver_context.open(aad, &ctxt).unwrap();
                assert_eq!(ptxt, plain_txt);
            }

            // Exporter test
            let sender_exporter = sender_context.export(exporter_context, 64);
            let receiver_exporter = receiver_context.export(exporter_context, 64);
            assert_eq!(sender_exporter, receiver_exporter);
        }
    };
}

generate_test_case!(
    base_dhkemp256_hkdfsha256_Aes128Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha256_Aes128Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkemp256_hkdfsha384_Aes128Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha384_Aes128Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkemp256_hkdfsha512_Aes128Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha512_Aes128Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkemp256_hkdfsha256_Aes256Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha256_Aes256Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkemp256_hkdfsha384_Aes256Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha384_Aes256Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkemp256_hkdfsha512_Aes256Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha512_Aes256Gcm,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkemp256_hkdfsha256_chacha20poly1305,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkemp256_hkdfsha256_chacha20poly1305_evercrypt,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeEvercrypt
);
generate_test_case!(
    base_dhkem25519_hkdfsha256_chacha20poly1305,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha256_chacha20poly1305_evercrypt,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeEvercrypt
);
generate_test_case!(
    base_dhkemp256_hkdfsha384_chacha20poly1305,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha384_chacha20poly1305,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkemp256_hkdfsha512_chacha20poly1305,
    HpkeMode::Base,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    base_dhkem25519_hkdfsha512_chacha20poly1305,
    HpkeMode::Base,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha256_Aes128Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha256_Aes128Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha384_Aes128Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha384_Aes128Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha512_Aes128Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha512_Aes128Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha256_Aes256Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha256_Aes256Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha384_Aes256Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha384_Aes256Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha512_Aes256Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha512_Aes256Gcm,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha256_chacha20poly1305,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha256_chacha20poly1305,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha384_chacha20poly1305,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha384_chacha20poly1305,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkemp256_hkdfsha512_chacha20poly1305,
    HpkeMode::Psk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    psk_dhkem25519_hkdfsha512_chacha20poly1305,
    HpkeMode::Psk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha256_Aes128Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha256_Aes128Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha384_Aes128Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha384_Aes128Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha512_Aes128Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha512_Aes128Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha256_Aes256Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha256_Aes256Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha384_Aes256Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha384_Aes256Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha512_Aes256Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha512_Aes256Gcm,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha256_chacha20poly1305,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha256_chacha20poly1305,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha384_chacha20poly1305,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha384_chacha20poly1305,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkemp256_hkdfsha512_chacha20poly1305,
    HpkeMode::Auth,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    auth_dhkem25519_hkdfsha512_chacha20poly1305,
    HpkeMode::Auth,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha256_Aes128Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha256_Aes128Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha384_Aes128Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha384_Aes128Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha512_Aes128Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha512_Aes128Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes128Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha256_Aes256Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha256_Aes256Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha384_Aes256Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha384_Aes256Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha512_Aes256Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha512_Aes256Gcm,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::Aes256Gcm,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha256_chacha20poly1305,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha256_chacha20poly1305,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha256,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha384_chacha20poly1305,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha384_chacha20poly1305,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha384,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkemp256_hkdfsha512_chacha20poly1305,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKemP256,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
generate_test_case!(
    authpsk_dhkem25519_hkdfsha512_chacha20poly1305,
    HpkeMode::AuthPsk,
    KemAlgorithm::DhKem25519,
    KdfAlgorithm::HkdfSha512,
    AeadAlgorithm::ChaCha20Poly1305,
    HpkeRustCrypto
);
