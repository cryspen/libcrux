#![allow(non_snake_case)]

use libcrux::aes_ni_support;
use serde::{Deserialize, Serialize};
use std::{fs::File, io::BufReader, time::Instant};

mod test_util;
use test_util::*;

use libcrux::hpke::aead::AEAD::{self};
use libcrux::hpke::kdf::KDF::{self};
use libcrux::hpke::kem::{DeriveKeyPair, DeserializePublicKey, SerializePublicKey, KEM};
use libcrux::hpke::{Mode::*, *};

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

fn mode(val: u8) -> Mode {
    match val {
        0 => Mode::mode_base,
        1 => Mode::mode_psk,
        2 => Mode::mode_auth,
        3 => Mode::mode_auth_psk,
        _ => panic!("Invalid mode"),
    }
}

fn kem(val: u16) -> KEM {
    match val {
        0x0010 => KEM::DHKEM_P256_HKDF_SHA256,
        0x0011 => KEM::DHKEM_P384_HKDF_SHA384,
        0x0012 => KEM::DHKEM_P521_HKDF_SHA512,
        0x0020 => KEM::DHKEM_X25519_HKDF_SHA256,
        0x0021 => KEM::DHKEM_X448_HKDF_SHA512,
        _ => panic!("Invalid KEM"),
    }
}

fn kdf(val: u16) -> KDF {
    match val {
        0x0001 => KDF::HKDF_SHA256,
        0x0002 => KDF::HKDF_SHA384,
        0x0003 => KDF::HKDF_SHA512,
        _ => panic!("Invalid KDF"),
    }
}

fn aead(val: u16) -> AEAD {
    match val {
        0x0001 => AEAD::AES_128_GCM,
        0x0002 => AEAD::AES_256_GCM,
        0x0003 => AEAD::ChaCha20Poly1305,
        0xFFFF => AEAD::Export_only,
        _ => panic!("Invalid AEAD"),
    }
}

pub fn hex_to_bytes_option(hex: Option<String>) -> Option<Vec<u8>> {
    hex.map(|s| hex_str_to_bytes(&s))
}

fn setup_r(
    mode: Mode,
    config: HPKEConfig,
    kat_enc: &Vec<u8>,
    sk_rm: &Vec<u8>,
    info: &Vec<u8>,
    psk: Option<&Vec<u8>>,
    psk_id: Option<&Vec<u8>>,
    pk_sm: Option<&Vec<u8>>,
) -> (Vec<u8>, Vec<u8>, u32, Vec<u8>) {
    match mode {
        mode_base => SetupBaseR(config, &kat_enc, &sk_rm, &info),
        mode_psk => SetupPSKR(
            config,
            &kat_enc,
            &sk_rm,
            &info,
            psk.unwrap(),
            psk_id.unwrap(),
        ),
        mode_auth => SetupAuthR(
            config,
            &kat_enc,
            &sk_rm,
            &info,
            &DeserializePublicKey(config.1, pk_sm.unwrap()).unwrap(),
        ),
        mode_auth_psk => SetupAuthPSKR(
            config,
            &kat_enc,
            &sk_rm,
            &info,
            psk.unwrap(),
            psk_id.unwrap(),
            &DeserializePublicKey(config.1, pk_sm.unwrap()).unwrap(),
        ),
    }
    .unwrap()
}

fn setup_s(
    mode: Mode,
    config: HPKEConfig,
    ikm_e: Vec<u8>,
    pkR: &Vec<u8>,
    info: &Vec<u8>,
    psk: Option<&Vec<u8>>,
    psk_id: Option<&Vec<u8>>,
    sk_sm: Option<&Vec<u8>>,
) -> (Vec<u8>, (Vec<u8>, Vec<u8>, u32, Vec<u8>)) {
    match mode {
        mode_base => SetupBaseS(config, pkR, info, ikm_e),
        mode_psk => SetupPSKS(config, pkR, &info, psk.unwrap(), psk_id.unwrap(), ikm_e),
        mode_auth => SetupAuthS(config, pkR, &info, sk_sm.unwrap(), ikm_e),
        mode_auth_psk => SetupAuthPSKS(
            config,
            pkR,
            &info,
            psk.unwrap(),
            psk_id.unwrap(),
            sk_sm.unwrap(),
            ikm_e,
        ),
    }
    .unwrap()
}

fn kat(tests: Vec<HpkeTestVector>) {
    tests.iter().for_each(|test| {
        let mode = mode(test.mode);
        let kem_id = kem(test.kem_id);
        let kdf_id = kdf(test.kdf_id);
        let aead_id = aead(test.aead_id);
        let config = HPKEConfig(mode, kem_id, kdf_id, aead_id);

        if !(kem_id == KEM::DHKEM_X25519_HKDF_SHA256 || kem_id == KEM::DHKEM_P256_HKDF_SHA256) {
            println!(
                " > Only DHKEM_X25519_HKDF_SHA256 and DHKEM_P256_HKDF_SHA256 implemented ({:?})",
                kem_id
            );
            return;
        }

        if !(aead_id == AEAD::ChaCha20Poly1305 || aead_id == AEAD::AES_128_GCM) {
            println!(
                " > Only ChaCha20Poly1305 and Aes128Gcm implemented ({:?})",
                aead_id
            );
            return;
        }
        if !aes_ni_support() || cfg!(not(target_arch = "x86_64")) {
            // libcrux AES only works on x64 (and there only with the necessary extensions)
            eprintln!("skipping AES because we're missing features.");
            return;
        }

        if kdf_id != KDF::HKDF_SHA256 {
            println!(" > Only HKDF_SHA256 implemented ({:?})", kdf_id);
            return;
        }

        println!(
            "Testing mode {:?} with ciphersuite {:?}_{:?}_{:?}",
            mode, kem_id, kdf_id, aead_id
        );

        // Set up sender and receiver.
        let pk_rm = hex_str_to_bytes(&test.pkRm);
        let sk_rm = hex_str_to_bytes(&test.skRm);
        let pk_em = hex_str_to_bytes(&test.pkEm);
        let sk_em = hex_str_to_bytes(&test.skEm);
        let pk_sm = hex_to_bytes_option(test.pkSm.clone());
        let pk_sm = pk_sm.as_ref();
        let sk_sm = hex_to_bytes_option(test.skSm.clone());
        let sk_sm = sk_sm.as_ref();
        let info = hex_str_to_bytes(&test.info);
        let psk = hex_to_bytes_option(test.psk.clone());
        let psk = psk.as_ref();
        let psk_id = hex_to_bytes_option(test.psk_id.clone());
        let psk_id = psk_id.as_ref();
        let shared_secret = hex_str_to_bytes(&test.shared_secret);
        let key = hex_str_to_bytes(&test.key);
        let nonce = hex_str_to_bytes(&test.base_nonce);
        let exporter_secret = hex_str_to_bytes(&test.exporter_secret);

        // Input key material.
        let ikm_r = hex_str_to_bytes(&test.ikmR);
        let ikm_e = hex_str_to_bytes(&test.ikmE);
        let ikm_s = hex_to_bytes_option(test.ikmS.clone());

        let empty = vec![];

        // Use internal `key_schedule` function for KAT.
        let direct_ctx = KeySchedule(
            config,
            &shared_secret,
            &info,
            match psk {
                Some(psk) => psk,
                None => &empty,
            },
            match psk_id {
                Some(psk_id) => psk_id,
                None => &empty,
            },
        )
        .unwrap();

        // Check setup info
        // Note that key and nonce are empty for exporter only key derivation.
        assert_eq!(direct_ctx.0, key);
        assert_eq!(direct_ctx.1, nonce);
        assert_eq!(direct_ctx.2, 0);
        assert_eq!(direct_ctx.3, exporter_secret);

        // Test key pair derivation.
        let (my_sk_r, my_pk_r) = DeriveKeyPair(kem_id, &ikm_r).unwrap();
        let my_pk_rm = SerializePublicKey(kem_id, my_pk_r);
        assert_eq!(sk_rm, my_sk_r);
        assert_eq!(pk_rm, my_pk_rm);
        let (my_sk_e, my_pk_e) = DeriveKeyPair(kem_id, &ikm_e).unwrap();
        let my_pk_em = SerializePublicKey(kem_id, my_pk_e);
        assert_eq!(sk_em, my_sk_e);
        assert_eq!(pk_em, my_pk_em);
        if let (Some(sk_sm), Some(pk_sm)) = (sk_sm, pk_sm) {
            let (my_sk_s, my_pk_s) = DeriveKeyPair(kem_id, &ikm_s.unwrap()).unwrap();
            let my_pk_sm = SerializePublicKey(kem_id, my_pk_s);
            assert_eq!(sk_sm, &my_sk_s);
            assert_eq!(pk_sm, &my_pk_sm);
        }

        // Setup sender and receiver.
        let kat_enc = hex_str_to_bytes(&test.enc);
        let pk_r = DeserializePublicKey(kem_id, &pk_rm).unwrap();
        // use kat enc
        let mut receiver_context_kat =
            setup_r(mode, config, &kat_enc, &sk_rm, &info, psk, psk_id, pk_sm);
        let (enc, _sender_context_kat) = setup_s(
            mode,
            config,
            ikm_e.clone(),
            &pk_r,
            &info,
            psk,
            psk_id,
            sk_sm,
        );
        // use generated enc
        let receiver_context = setup_r(mode, config, &enc, &sk_rm, &info, psk, psk_id, pk_sm);

        assert_eq!(enc, kat_enc);
        assert_eq!(receiver_context.0, receiver_context_kat.0);
        assert_eq!(receiver_context.1, receiver_context_kat.1);
        assert_eq!(receiver_context.3, receiver_context_kat.3);

        receiver_context_kat = receiver_context;
        assert_eq!(receiver_context_kat.0, key);
        assert_eq!(receiver_context_kat.1, nonce);
        assert_eq!(receiver_context_kat.2, 0);
        assert_eq!(receiver_context_kat.3, exporter_secret);

        // Setup sender and receiver for self tests.
        let mut receiver_context =
            setup_r(mode, config, &kat_enc, &sk_rm, &info, psk, psk_id, pk_sm);
        let (_enc, mut sender_context) = setup_s(
            mode,
            config,
            ikm_e.clone(),
            &pk_r,
            &info,
            psk,
            psk_id,
            sk_sm,
        );

        // Encrypt
        for (_i, encryption) in test.encryptions.iter().enumerate() {
            println!("Test encryption {} ...", _i);
            let aad = hex_str_to_bytes(&encryption.aad);
            let ptxt = hex_str_to_bytes(&encryption.pt);
            let ctxt_kat = hex_str_to_bytes(&encryption.ct);

            // Test context API self-test
            let (ctxt_out, new_sender_context) =
                ContextS_Seal(aead_id, sender_context, &aad, &ptxt).unwrap();
            sender_context = new_sender_context;
            assert_eq!(ctxt_kat, ctxt_out);
            let (ptxt_out, new_receiver_context) =
                ContextR_Open(aead_id, receiver_context, &aad, &ctxt_out).unwrap();
            receiver_context = new_receiver_context;
            assert_eq!(ptxt_out, ptxt);

            // Test KAT receiver context open
            let (ptxt_out, new_receiver_context_kat) =
                ContextR_Open(aead_id, receiver_context_kat, &aad, &ctxt_out).unwrap();
            receiver_context_kat = new_receiver_context_kat;
            assert_eq!(ptxt_out, ptxt);
        }

        // Test KAT on direct_ctx for exporters
        for (_i, export) in test.exports.iter().enumerate() {
            println!("Test exporter {} ...", _i);
            let export_context = hex_str_to_bytes(&export.exporter_context);
            let export_value = hex_str_to_bytes(&export.exported_value);
            let length = export.L;

            let exported_secret =
                Context_Export(config, &direct_ctx, export_context, length).unwrap();
            assert_eq!(export_value, exported_secret);
        }
    });
}

#[test]
fn test_kat() {
    let file = "tests/hpke_test_vectors.json";
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
    kat(tests.clone());
    let time = now.elapsed();
    println!("Test vectors with Rust Crypto took: {}s", time.as_secs());
}
