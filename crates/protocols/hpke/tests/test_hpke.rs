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
    key_schedule_context: String,
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

        if mode != Mode::Base {
            println!(" > Mode {:?} not implemented yet", mode);
            continue;
        }

        if kem_id != kem::Mode::DhKem25519 {
            println!(" > KEM {:?} not implemented yet", kem_id);
            continue;
        }

        if aead_id != aead::Mode::AesGcm128 {
            println!(" > AEAD {:?} not implemented yet", aead_id);
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
        let info = hex_to_bytes(&test.info);
        let (enc, mut sender_context) = hpke.setup_sender(&pk_rm, &info);
        let mut receiver_context = hpke.setup_receiver(&enc, &sk_rm, &info);

        // Encrypt
        for encryption in test.encryptions {
            let aad = hex_to_bytes(&encryption.aad);
            let ptxt = hex_to_bytes(&encryption.plaintext);
            let ctxt_out = sender_context.seal(&aad, &ptxt);
            let ptxt_out = receiver_context.open(&aad, &ctxt_out);
            assert_eq!(ptxt_out, ptxt);
        }

        // TODO: test exports
        for export in test.exports {
            println!(" > Exports not implemented yet.");
        }
    }
}
