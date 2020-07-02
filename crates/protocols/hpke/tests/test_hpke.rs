use serde::{self, Deserialize, Serialize};
use std::fs::File;
use std::io::BufReader;

use hpke::*;

mod test_util;
use test_util::*;

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct HpkeTestVecor {
    mode: u16,
    kemID: u16,
    kdfID: u16,
    aeadID: u16,
    info: String,
    seedR: String,
    seedS: Option<String>,
    seedE: String,
    skRm: String,
    skSm: Option<String>,
    skEm: String,
    psk: Option<String>,
    pskID: Option<String>,
    pkRm: String,
    pkSm: Option<String>,
    pkEm: String,
    enc: String,
    zz: String,
    keyScheduleContext: String,
    secret: String,
    key: String,
    nonce: String,
    exporterSecret: String,
    encryptions: Vec<CiphertextKAT>,
    exports: Vec<ExportsKAT>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct CiphertextKAT {
    aad: String,
    ciphertext: String,
    nonce: String,
    plaintext: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct ExportsKAT {
    exportContext: String,
    exportLength: usize,
    exportValue: String,
}

#[test]
fn test_kat() {
    let file = "tests/test_vectors.json";
    let file = match File::open(file) {
        Ok(f) => f,
        Err(_) => panic!("Couldn't open file {}.", file),
    };
    let reader = BufReader::new(file);
    let tests: Vec<HpkeTestVecor> = match serde_json::from_reader(reader) {
        Ok(r) => r,
        Err(e) => panic!("Error reading file.\n{:?}", e),
    };

    for test in tests {
        let mode: Mode = test.mode.into();
        let kem_id: kem::Mode = test.kemID.into();
        let kdf_id: kdf::Mode = test.kdfID.into();
        let aead_id: aead::Mode = test.aeadID.into();

        if kem_id != kem::Mode::DhKem25519 {
            println!(" > KEM {:?} not implemented yet", kem_id);
            continue;
        }

        println!(
            "Testing mode {:?} with ciphersuite {:?}_{:?}_{:?}",
            mode, kem_id, kdf_id, aead_id
        );

        // Init HPKE with the given mode and ciphersuite.
        let hpke = Hpke::new(mode, kem_id, kdf_id, aead_id);

        // Set up sender and receiver.
        let pk_rm = hex_to_bytes(&test.pkRm);
        let sk_rm = hex_to_bytes(&test.skRm);
        let pk_sm = hex_to_bytes_option(test.pkSm);
        let pk_sm = vec_to_option_slice(&pk_sm);
        let sk_sm = hex_to_bytes_option(test.skSm);
        let sk_sm = vec_to_option_slice(&sk_sm);
        let info = hex_to_bytes(&test.info);
        let psk = hex_to_bytes_option(test.psk);
        let psk = vec_to_option_slice(&psk);
        let psk_id = hex_to_bytes_option(test.pskID);
        let psk_id = vec_to_option_slice(&psk_id);
        let zz = hex_to_bytes(&test.zz);
        // let key_schedule_context = hex_to_bytes(&test.keyScheduleContext);
        // let secret = hex_to_bytes(&test.secret);
        let key = hex_to_bytes(&test.key);
        let nonce = hex_to_bytes(&test.nonce);
        let exporter_secret = hex_to_bytes(&test.exporterSecret);

        // Use internal `key_schedule` function for KAT.
        let mut direct_ctx = hpke.key_schedule(
            &zz,
            &info,
            psk.unwrap_or_default(),
            psk_id.unwrap_or_default(),
        );

        // Check setup info
        assert_eq!(direct_ctx.key, key);
        assert_eq!(direct_ctx.nonce, nonce);
        assert_eq!(direct_ctx.exporter_secret, exporter_secret);
        assert_eq!(direct_ctx.sequence_number, 0);

        // Setup sender and receiver.
        // These use randomness and hence can't be fully checked against the test vectors.
        let (enc, mut sender_context) = hpke.setup_sender(&pk_rm, &info, psk, psk_id, sk_sm);
        let mut receiver_context = hpke.setup_receiver(&enc, &sk_rm, &info, psk, psk_id, pk_sm);

        // Encrypt
        for encryption in test.encryptions {
            let aad = hex_to_bytes(&encryption.aad);
            let ptxt = hex_to_bytes(&encryption.plaintext);
            let ctxt_out = sender_context.seal(&aad, &ptxt);
            let ptxt_out = receiver_context.open(&aad, &ctxt_out);
            assert_eq!(ptxt_out, ptxt);

            // Test single-shot API
            let (enc, ct) = hpke.seal(&pk_rm, &info, &aad, &ptxt, psk, psk_id, sk_sm);
            let ptxt_out = hpke.open(&enc, &sk_rm, &info, &aad, &ct, psk, psk_id, pk_sm);
            assert_eq!(ptxt_out, ptxt);

            // Test KAT on direct_ctx
            let ct = direct_ctx.seal(&aad, &ptxt);
            assert_eq!(hex_to_bytes(&encryption.ciphertext), ct);
        }

        // Test KAT on direct_ctx for exporters
        for export in test.exports {
            println!(" > > SKIPPING EXPORTERS :(");
            let export_context = hex_to_bytes(&export.exportContext);
            let export_value = hex_to_bytes(&export.exportValue);
            let length = export.exportLength;

            let exported_secret = direct_ctx.export(&export_context, length);
            assert_eq!(export_value, exported_secret);
        }
    }
}
