extern crate hpke_rs as hpke;

use hpke_rs_rust_crypto::HpkeRustCrypto;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use serde::{self, Deserialize, Serialize};
use std::convert::TryInto;
use std::fs::File;
use std::io::BufReader;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use hpke::prelude::*;
use hpke::test_util::{hex_to_bytes, hex_to_bytes_option, vec_to_option_slice};
use hpke_rs_crypto::{types::*, HpkeCrypto};
use hpke_rs_libcrux::HpkeLibcrux;

/// A single HPKE known-answer test vector.
///
/// Some fields are optional to accommodate the different test vector formats we
/// consume: the newer vectors (e.g. `test_vectors2.json`) omit the ephemeral key
/// pair (`skEm`/`pkEm`) and the intermediate `key_schedule_context`/`secret`
/// values, and add a `suite_id`.
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
    skEm: Option<String>,
    psk: Option<String>,
    psk_id: Option<String>,
    pkRm: String,
    pkSm: Option<String>,
    pkEm: Option<String>,
    enc: String,
    shared_secret: String,
    suite_id: Option<String>,
    key_schedule_context: Option<String>,
    secret: Option<String>,
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

/// Run the known-answer tests for all `tests` supported by the `Crypto` backend,
/// and return the number of test vectors that were actually executed
/// (i.e. not skipped because the backend doesn't support the ciphersuite).
fn kat<Crypto: HpkeCrypto + 'static>(tests: Vec<HpkeTestVector>) -> usize {
    let executed = AtomicUsize::new(0);
    // Replace into_par_iter() with into_iter() to run tests sequentially.
    tests.into_par_iter().for_each(|test| {
        println!(
            "Testing mode {:?} with ciphersuite {:?}_{:?}_{:?}",
            test.mode, test.kem_id, test.kdf_id, test.aead_id
        );
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

        // This vector is supported and will run all its assertions below.
        executed.fetch_add(1, Ordering::Relaxed);

        // Init HPKE with the given mode and ciphersuite.
        let mut hpke = Hpke::<Crypto>::new(mode, kem_id, kdf_id, aead_id);

        // Set up sender and receiver.
        let pk_rm = HpkePublicKey::new(hex_to_bytes(&test.pkRm));
        let sk_rm = HpkePrivateKey::new(hex_to_bytes(&test.skRm));
        let pk_em = hex_to_bytes_option(test.pkEm);
        let pk_em = if pk_em.is_empty() {
            None
        } else {
            Some(HpkePublicKey::new(pk_em))
        };
        let sk_em = hex_to_bytes_option(test.skEm);
        let sk_em = if sk_em.is_empty() {
            None
        } else {
            Some(HpkePrivateKey::new(sk_em))
        };
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
        if let (Some(sk_em), Some(pk_em)) = (&sk_em, &pk_em) {
            assert_eq!(sk_em, &my_sk_e);
            assert_eq!(pk_em, &my_pk_e);
        }
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
            let mut hpke_sender = Hpke::<Crypto>::new(mode, kem_id, kdf_id, aead_id);
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
        log::trace!(
            "Testing encryptions for mode {:?} with ciphersuite {:?}_{:?}_{:?}",
            mode,
            kem_id,
            kdf_id,
            aead_id
        );
        for encryption in test.encryptions.iter() {
            // Cloning the Hpke object renews the test PRNG.
            hpke = hpke.clone();
            let aad = hex_to_bytes(&encryption.aad);
            let ptxt = hex_to_bytes(&encryption.pt);
            let ctxt_kat = hex_to_bytes(&encryption.ct);

            // Test context API self-test
            let ctxt_out = sender_context.seal(&aad, &ptxt).unwrap();
            let ptxt_out = receiver_context.open(&aad, &ctxt_out).unwrap();
            assert_eq!(ptxt_out, ptxt);

            // Test KAT receiver context open
            let ptxt_out = receiver_context_kat.open(&aad, &ctxt_kat).unwrap();
            assert_eq!(ptxt_out, ptxt);

            // Test KAT seal on direct_ctx
            let ct = direct_ctx.seal(&aad, &ptxt).unwrap();
            assert_eq!(ctxt_kat, ct);
        }

        // Test single-shot API self-test
        if let Some(encryption) = test.encryptions.first() {
            let aad = hex_to_bytes(&encryption.aad);
            let ptxt = hex_to_bytes(&encryption.pt);
            // Cloning the Hpke object renews the test PRNG.
            let mut hpke = hpke.clone();
            let (enc, ct) = hpke
                .seal(&pk_rm, &info, &aad, &ptxt, psk, psk_id, sk_sm)
                .unwrap();
            let ptxt_out = hpke
                .open(&enc, &sk_rm, &info, &aad, &ct, psk, psk_id, pk_sm)
                .unwrap();
            assert_eq!(ptxt_out, ptxt);
        }

        // Test KAT on direct_ctx for exporters
        log::trace!(
            "Testing exporter for mode {:?} with ciphersuite {:?}_{:?}_{:?}",
            mode,
            kem_id,
            kdf_id,
            aead_id
        );
        for export in test.exports.iter() {
            let export_context = hex_to_bytes(&export.exporter_context);
            let export_value = hex_to_bytes(&export.exported_value);
            let length = export.L;

            let exported_secret = direct_ctx.export(&export_context, length).unwrap();
            assert_eq!(export_value, exported_secret);
        }
    });
    executed.into_inner()
}

#[test]
fn kats_rust_crypto() {
    // The KEMs the RustCrypto backend is expected to run KATs for. All AEADs and
    // KDFs present in the test vectors are supported by both backends, so the
    // KEM is the only thing that determines whether a vector is exercised.
    #[allow(unused_mut)]
    let mut kems = vec![
        KemAlgorithm::DhKem25519,
        KemAlgorithm::DhKemP256,
        KemAlgorithm::DhKemK256,
        KemAlgorithm::DhKemP384,
    ];
    #[cfg(feature = "experimental")]
    kems.extend([
        KemAlgorithm::XWingDraft06,
        KemAlgorithm::MlKem768,
        KemAlgorithm::MlKem1024,
    ]);
    run::<HpkeRustCrypto>(&kems);
}

#[test]
fn kats_libcrux() {
    // The KEMs the libcrux backend is expected to run KATs for. See the note in
    // `kats_rust_crypto` on why only the KEM matters.
    #[allow(unused_mut)]
    let mut kems = vec![
        KemAlgorithm::DhKem25519,
        KemAlgorithm::DhKemP256,
        KemAlgorithm::XWingDraft06,
    ];
    #[cfg(feature = "libcrux-rustcrypto-p-curves")]
    kems.extend([KemAlgorithm::DhKemP384, KemAlgorithm::DhKemP521]);
    #[cfg(feature = "draft-connolly-cfrg-hpke-mlkem")]
    kems.extend([KemAlgorithm::MlKem768, KemAlgorithm::MlKem1024]);
    run::<HpkeLibcrux>(&kems);
}

fn run<Crypto: HpkeCrypto + 'static>(supported_kems: &[KemAlgorithm]) {
    let _ = pretty_env_logger::try_init();
    let files = vec![
        "tests/test_vectors.json",
        "tests/test_vectors2.json",
        "tests/test_vectors_k256.json",
    ];
    let mut total_executed = 0;
    for path in files {
        let file = match File::open(path) {
            Ok(f) => f,
            Err(_) => panic!("Couldn't open file {}.", path),
        };
        let reader = BufReader::new(file);
        let tests: Vec<HpkeTestVector> = match serde_json::from_reader(reader) {
            Ok(r) => r,
            Err(e) => panic!("Error reading file.\n{:?}", e),
        };

        // We know upfront exactly which vectors this backend should run: those
        // whose KEM it supports. Anything else is skipped.
        let expected = tests
            .iter()
            .filter(|t| {
                KemAlgorithm::try_from(t.kem_id)
                    .map(|kem| supported_kems.contains(&kem))
                    .unwrap_or(false)
            })
            .count();

        // Run the actual KAT.
        let now = Instant::now();
        let executed = kat::<Crypto>(tests.clone());
        let time = now.elapsed();

        assert_eq!(
            executed,
            expected,
            "{}: expected {} KAT vectors to run for {}, but {} ran",
            path,
            expected,
            Crypto::name(),
            executed
        );
        total_executed += executed;

        log::info!(
            "Test vectors with {} took: {}s",
            Crypto::name(),
            time.as_secs()
        );
    }

    // Guard against all files silently loading nothing / every vector being
    // skipped, which would make the test pass without checking anything.
    assert!(
        total_executed > 0,
        "No KAT vectors ran at all for {}",
        Crypto::name()
    );
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

                    let mut hpke =
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
}
