extern crate hpke_rs as hpke;

use hpke_rs_evercrypt::HpkeEvercrypt;
use hpke_rs_rust_crypto::HpkeRustCrypto;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use serde::{self, Deserialize, Serialize};
use std::convert::TryInto;
use std::fs::File;
use std::io::BufReader;
use std::time::Instant;

use hpke::prelude::*;
use hpke::test_util::{hex_to_bytes, hex_to_bytes_option, vec_to_option_slice};
use hpke_rs_crypto::{types::*, HpkeCrypto};

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct HpkeTestVector {
    mode: u8,
    kem_id: u16,
    kdf_id: u16,
    aead_id: u16,
    info: String,
    ikmR: String,
    ikmS: Option<String>,
    ikmE: String,
    skRm: String,
    skSm: Option<String>,
    skEm: String,
    psk: Option<String>,
    psk_id: Option<String>,
    pkRm: String,
    pkSm: Option<String>,
    pkEm: String,
    enc: String,
    shared_secret: String,
    key_schedule_context: String,
    secret: String,
    key: String,
    base_nonce: String,
    exporter_secret: String,
    encryptions: Vec<CiphertextKAT>,
    exports: Vec<ExportsKAT>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct CiphertextKAT {
    aad: String,
    ct: String,
    nonce: String,
    pt: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct ExportsKAT {
    exporter_context: String,
    L: usize,
    exported_value: String,
}

fn kat<Crypto: HpkeCrypto + 'static>(tests: Vec<HpkeTestVector>) {
    tests.into_par_iter().for_each(|test| {
        let mode: HpkeMode = test.mode.try_into().unwrap();
        let kem_id: KemAlgorithm = test.kem_id.try_into().unwrap();
        let kdf_id: KdfAlgorithm = test.kdf_id.try_into().unwrap();
        let aead_id: AeadAlgorithm = test.aead_id.try_into().unwrap();

        if Crypto::supports_kem(kem_id).is_err() {
            log::trace!(
                " > KEM {:?} not implemented yet for {}",
                kem_id,
                Crypto::name()
            );
            return;
        }

        if Crypto::supports_aead(aead_id).is_err() {
            log::trace!(
                " > AEAD {:?} not implemented yet for {}",
                aead_id,
                Crypto::name()
            );
            return;
        }

        if Crypto::supports_kdf(kdf_id).is_err() {
            log::trace!(
                " > KDF {:?} not implemented yet for {}",
                kdf_id,
                Crypto::name()
            );
            return;
        }

        log::trace!(
            "Testing mode {:?} with ciphersuite {:?}_{:?}_{:?}",
            mode,
            kem_id,
            kdf_id,
            aead_id
        );

        // Init HPKE with the given mode and ciphersuite.
        let mut hpke = Hpke::<Crypto>::new(mode, kem_id, kdf_id, aead_id);

        // Set up sender and receiver.
        let pk_rm = HpkePublicKey::new(hex_to_bytes(&test.pkRm));
        let sk_rm = HpkePrivateKey::new(hex_to_bytes(&test.skRm));
        let pk_em = HpkePublicKey::new(hex_to_bytes(&test.pkEm));
        let sk_em = HpkePrivateKey::new(hex_to_bytes(&test.skEm));
        let pk_sm = hex_to_bytes_option(test.pkSm);
        let pk_sm = if pk_sm.is_empty() {
            None
        } else {
            Some(HpkePublicKey::new(pk_sm))
        };
        let pk_sm = pk_sm.as_ref();
        let sk_sm = hex_to_bytes_option(test.skSm);
        let sk_sm = if sk_sm.is_empty() {
            None
        } else {
            Some(HpkePrivateKey::new(sk_sm))
        };
        let sk_sm = sk_sm.as_ref();
        let info = hex_to_bytes(&test.info);
        let psk = hex_to_bytes_option(test.psk);
        let psk = vec_to_option_slice(&psk);
        let psk_id = hex_to_bytes_option(test.psk_id);
        let psk_id = vec_to_option_slice(&psk_id);
        let shared_secret = hex_to_bytes(&test.shared_secret);
        let key = hex_to_bytes(&test.key);
        let nonce = hex_to_bytes(&test.base_nonce);
        let exporter_secret = hex_to_bytes(&test.exporter_secret);

        // Input key material.
        let ikm_r = hex_to_bytes(&test.ikmR);
        let ikm_e = hex_to_bytes(&test.ikmE);
        let ikm_s = hex_to_bytes_option(test.ikmS);

        // Use internal `key_schedule` function for KAT.
        let mut direct_ctx = hpke
            .key_schedule(
                &shared_secret,
                &info,
                psk.unwrap_or_default(),
                psk_id.unwrap_or_default(),
            )
            .unwrap();

        // Check setup info
        // Note that key and nonce are empty for exporter only key derivation.
        assert_eq!(direct_ctx.key(), key);
        assert_eq!(direct_ctx.nonce(), nonce);
        assert_eq!(direct_ctx.exporter_secret(), exporter_secret);
        assert_eq!(direct_ctx.sequence_number(), 0);

        // Test key pair derivation.
        let (my_sk_r, my_pk_r) = hpke.derive_key_pair(&ikm_r).unwrap().into_keys();
        assert_eq!(sk_rm, my_sk_r);
        assert_eq!(pk_rm, my_pk_r);
        let (my_sk_e, my_pk_e) = hpke.derive_key_pair(&ikm_e).unwrap().into_keys();
        assert_eq!(sk_em, my_sk_e);
        assert_eq!(pk_em, my_pk_e);
        if let (Some(sk_sm), Some(pk_sm)) = (sk_sm, pk_sm) {
            let (my_sk_s, my_pk_s) = hpke.derive_key_pair(&ikm_s).unwrap().into_keys();
            assert_eq!(sk_sm, &my_sk_s);
            assert_eq!(pk_sm, &my_pk_s);
        }

        // Setup KAT receiver.
        let kat_enc = hex_to_bytes(&test.enc);
        let mut receiver_context_kat = hpke
            .setup_receiver(&kat_enc, &sk_rm, &info, psk, psk_id, pk_sm)
            .unwrap();

        // Setup sender and receiver with KAT randomness.
        // We first have to inject the randomness (ikmE).

        #[cfg(feature = "hpke-test-prng")]
        {
            log::trace!("Testing with known ikmE ...");
            let hpke_sender = Hpke::<Crypto>::new(mode, kem_id, kdf_id, aead_id);
            // This only works when seeding the PRNG with ikmE.
            hpke_sender.seed(&ikm_e).expect("Error injecting ikm_e");
            let (enc, _sender_context_kat) = hpke_sender
                .setup_sender(&pk_rm, &info, psk, psk_id, sk_sm)
                .unwrap();
            let receiver_context = hpke
                .setup_receiver(&enc, &sk_rm, &info, psk, psk_id, pk_sm)
                .unwrap();
            assert_eq!(enc, kat_enc);
            assert_eq!(receiver_context.key(), receiver_context_kat.key());
            assert_eq!(receiver_context.nonce(), receiver_context_kat.nonce());
            assert_eq!(
                receiver_context.exporter_secret(),
                receiver_context_kat.exporter_secret()
            );
            receiver_context_kat = receiver_context;
            assert_eq!(receiver_context_kat.key(), key);
            assert_eq!(receiver_context_kat.nonce(), nonce);
            assert_eq!(receiver_context_kat.exporter_secret(), exporter_secret);
            assert_eq!(receiver_context_kat.sequence_number(), 0);
        }

        // Setup sender and receiver for self tests.
        let (enc, mut sender_context) = hpke
            .setup_sender(&pk_rm, &info, psk, psk_id, sk_sm)
            .unwrap();
        let mut receiver_context = hpke
            .setup_receiver(&enc, &sk_rm, &info, psk, psk_id, pk_sm)
            .unwrap();

        // Encrypt
        for (_i, encryption) in test.encryptions.iter().enumerate() {
            // Cloning the Hpke object renews the test PRNG.
            hpke = hpke.clone();
            println!("Test encryption {} ...", _i);
            let aad = hex_to_bytes(&encryption.aad);
            let ptxt = hex_to_bytes(&encryption.pt);
            let ctxt_kat = hex_to_bytes(&encryption.ct);

            // Test context API self-test
            let ctxt_out = sender_context.seal(&aad, &ptxt).unwrap();
            let ptxt_out = receiver_context.open(&aad, &ctxt_out).unwrap();
            assert_eq!(ptxt_out, ptxt);

            // Test single-shot API self-test
            let (enc, ct) = hpke
                .seal(&pk_rm, &info, &aad, &ptxt, psk, psk_id, sk_sm)
                .unwrap();
            let ptxt_out = hpke
                .open(&enc, &sk_rm, &info, &aad, &ct, psk, psk_id, pk_sm)
                .unwrap();
            assert_eq!(ptxt_out, ptxt);

            // Test KAT receiver context open
            let ptxt_out = receiver_context_kat.open(&aad, &ctxt_kat).unwrap();
            assert_eq!(ptxt_out, ptxt);

            // Test KAT seal on direct_ctx
            let ct = direct_ctx.seal(&aad, &ptxt).unwrap();
            assert_eq!(ctxt_kat, ct);
        }

        // Test KAT on direct_ctx for exporters
        for (_i, export) in test.exports.iter().enumerate() {
            println!("Test exporter {} ...", _i);
            let export_context = hex_to_bytes(&export.exporter_context);
            let export_value = hex_to_bytes(&export.exported_value);
            let length = export.L;

            let exported_secret = direct_ctx.export(&export_context, length).unwrap();
            assert_eq!(export_value, exported_secret);
        }
    });
}

#[test]
fn test_kat() {
    let _ = pretty_env_logger::try_init();
    let file = "tests/test_vectors.json";
    let file = match File::open(file) {
        Ok(f) => f,
        Err(_) => panic!("Couldn't open file {}.", file),
    };
    let reader = BufReader::new(file);
    let tests: Vec<HpkeTestVector> = match serde_json::from_reader(reader) {
        Ok(r) => r,
        Err(e) => panic!("Error reading file.\n{:?}", e),
    };

    let now = Instant::now();
    kat::<HpkeRustCrypto>(tests.clone());
    let time = now.elapsed();
    log::info!("Test vectors with Rust Crypto took: {}s", time.as_secs());

    let now = Instant::now();
    kat::<HpkeEvercrypt>(tests);
    let time = now.elapsed();
    log::info!("Test vectors with Evercrypt took: {}s", time.as_secs());
}

#[cfg(feature = "serialization")]
#[cfg(feature = "hazmat")]
#[test]
fn test_serialization() {
    use hpke::HpkeKeyPair;

    // XXX: Make these individual tests.
    for mode in 0u8..4 {
        let hpke_mode = HpkeMode::try_from(mode).unwrap();
        for aead_mode in 1u16..4 {
            let aead_mode = AeadAlgorithm::try_from(aead_mode).unwrap();
            for kdf_mode in 1u16..4 {
                let kdf_mode = KdfAlgorithm::try_from(kdf_mode).unwrap();
                for &kem_mode in &[0x10u16, 0x20] {
                    let kem_mode = KemAlgorithm::try_from(kem_mode).unwrap();

                    let hpke =
                        Hpke::<HpkeRustCrypto>::new(hpke_mode, kem_mode, kdf_mode, aead_mode);

                    // JSON: Public, Private, KeyPair
                    let key_pair = hpke.generate_key_pair().unwrap();

                    let serialized_key_pair = serde_json::to_string(&key_pair).unwrap();
                    let deserialized_key_pair: HpkeKeyPair =
                        serde_json::from_str(&serialized_key_pair).unwrap();

                    let (sk, pk) = key_pair.into_keys();

                    let serialized_sk = serde_json::to_string(&sk).unwrap();
                    let deserialized_sk: HpkePrivateKey =
                        serde_json::from_str(&serialized_sk).unwrap();
                    let serialized_pk = serde_json::to_string(&pk).unwrap();
                    let deserialized_pk: HpkePublicKey =
                        serde_json::from_str(&serialized_pk).unwrap();

                    let (des_sk, des_pk) = deserialized_key_pair.into_keys();

                    assert_eq!(pk, des_pk);
                    assert_eq!(pk, deserialized_pk);
                    assert_eq!(sk.as_slice(), des_sk.as_slice());
                    assert_eq!(sk.as_slice(), deserialized_sk.as_slice());
                }
            }
        }
    }

    // let mode: Mode = Mode::Base;
    // let kem_id: kem::Mode = kem::Mode::DhKemP256;
    // let kdf_id: kdf::Mode = kdf::Mode::HkdfSha256;
    // let aead_id: aead::Mode = aead::Mode::AesGcm128;
    // let hpke = Hpke::new(mode, kem_id, kdf_id, aead_id);
}
