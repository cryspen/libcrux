mod test_util;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use test_util::*;

#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg;
#[cfg(target_arch = "wasm32")]
use rand_core::OsRng;

use libcrux::{
    aead::{
        self, decrypt, encrypt,
        Algorithm::{self, Chacha20Poly1305},
        Chacha20Key, EncryptError, InvalidArgumentError, Iv, Key, Tag,
    },
    aes_ni_support,
};

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn chachapoly_self_test() {
    let _ = pretty_env_logger::try_init();

    let orig_msg = b"hacspec rulez";
    let mut msg = orig_msg.clone();
    let aad = b"associated data" as &[u8];
    let raw_key = Chacha20Key([
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32,
    ]);
    let key = Key::Chacha20Poly1305(raw_key);
    let iv = Iv([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);

    let tag = encrypt(&key, &mut msg, iv, aad).unwrap();

    let iv = Iv([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
    assert!(decrypt(&key, &mut msg, iv, aad, &tag).is_ok());
    assert_eq!(orig_msg, &msg);
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn chachapoly_self_test_rand() {
    let _ = pretty_env_logger::try_init();

    let orig_msg = b"hacspec rulez";
    let mut msg = orig_msg.clone();
    let aad = b"associated data" as &[u8];

    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let key = Key::generate(Chacha20Poly1305, &mut rng);
    let iv = Iv::generate(&mut rng);
    let iv2 = Iv(iv.0);

    let tag = encrypt(&key, &mut msg, iv, aad).unwrap();
    assert!(decrypt(&key, &mut msg, iv2, aad, &tag).is_ok());

    assert_eq!(orig_msg, &msg);
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct AeadTestVector {
    algorithm: String,
    generatorVersion: String,
    numberOfTests: usize,
    notes: Option<Value>, // text notes (might not be present), keys correspond to flags
    header: Vec<Value>,   // not used
    testGroups: Vec<TestGroup>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct TestGroup {
    ivSize: usize,
    keySize: usize,
    tagSize: usize,
    r#type: String,
    tests: Vec<Test>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct Test {
    tcId: usize,
    comment: String,
    key: String,
    iv: String,
    aad: String,
    msg: String,
    ct: String,
    tag: String,
    result: String,
    flags: Vec<String>,
}

impl ReadFromFile for AeadTestVector {}

#[allow(non_snake_case)]
#[test]
fn wycheproof() {
    let aes_gcm_tests: AeadTestVector =
        AeadTestVector::from_file("tests/wycheproof/aes_gcm_test.json");
    let chacha_poly_tests: AeadTestVector =
        AeadTestVector::from_file("tests/wycheproof/chacha20_poly1305_test.json");

    let num_tests = aes_gcm_tests.numberOfTests + chacha_poly_tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    assert_eq!(aes_gcm_tests.algorithm, "AES-GCM");
    assert_eq!(chacha_poly_tests.algorithm, "CHACHA20-POLY1305");

    test_group(aes_gcm_tests, &mut skipped_tests, &mut tests_run);
    test_group(chacha_poly_tests, &mut skipped_tests, &mut tests_run);

    fn test_group(test_vec: AeadTestVector, skipped_tests: &mut usize, tests_run: &mut usize) {
        for testGroup in test_vec.testGroups.iter() {
            assert_eq!(testGroup.r#type, "AeadTest");
            let algorithm = match test_vec.algorithm.as_str() {
                "AES-GCM" => match testGroup.keySize {
                    128 => Algorithm::Aes128Gcm,
                    256 => Algorithm::Aes256Gcm,
                    _ => {
                        // not implemented
                        println!("Only AES 128 and 256 are implemented.");
                        *skipped_tests += testGroup.tests.len();
                        continue;
                    }
                },
                "CHACHA20-POLY1305" => {
                    assert_eq!(testGroup.keySize, 256);
                    Algorithm::Chacha20Poly1305
                }
                _ => panic!("Unknown algorithm {:?}", test_vec.algorithm),
            };
            if !aes_ni_support()
                && (algorithm == Algorithm::Aes128Gcm || algorithm == Algorithm::Aes256Gcm)
            {
                println!("⚠️  AES NOT AVAILABLE ON THIS PLATFORM!");
                *skipped_tests += testGroup.tests.len();
                continue;
            }
            let invalid_iv = if testGroup.ivSize != 96 { true } else { false };

            for test in testGroup.tests.iter() {
                let valid = test.result.eq("valid");
                if invalid_iv {
                    // AEAD requires input of a 12-byte nonce.
                    let nonce = hex_str_to_bytes(&test.iv);
                    assert!(nonce.len() != 12);
                    *skipped_tests += 1;
                    continue;
                }
                println!("Test {:?}: {:?}", test.tcId, test.comment);
                let nonce = hex_str_to_array(&test.iv);
                let msg = hex_str_to_bytes(&test.msg);
                let aad = hex_str_to_bytes(&test.aad);
                let exp_cipher = hex_str_to_bytes(&test.ct);
                let exp_tag: Tag = hex_str_to_array(&test.tag);
                let key = hex_str_to_bytes(&test.key);

                let aead_key = match Key::from_bytes(algorithm, key) {
                    Ok(c) => c,
                    Err(_) => {
                        println!("⚠️  Skipping {:?} because it's not available.", algorithm);
                        *skipped_tests += 1;
                        continue;
                    }
                };
                let mut msg_ctxt = msg.clone();
                let tag = match aead::encrypt(&aead_key, &mut msg_ctxt, Iv(nonce), &aad) {
                    Ok(v) => v,
                    Err(e) => {
                        if matches!(
                            e,
                            EncryptError::InvalidArgument(
                                InvalidArgumentError::UnsupportedAlgorithm
                            )
                        ) {
                            eprintln!("AES not supported on this architecture.");
                            *skipped_tests += 1;
                            continue;
                        } else {
                            println!("Encrypt failed unexpectedly {:?}", e);
                            assert!(false);
                        }
                        *tests_run += 1;
                        continue;
                    }
                };
                if valid {
                    assert_eq!(tag, exp_tag);
                } else {
                    assert_ne!(tag, exp_tag);
                }
                assert_eq!(msg_ctxt, exp_cipher);

                match aead::decrypt(&aead_key, &mut msg_ctxt, Iv(nonce), &aad, &tag) {
                    Ok(()) => {
                        assert_eq!(msg, msg_ctxt);
                    }
                    Err(_) => {
                        assert!(!valid);
                    }
                };

                *tests_run += 1;
            }
        }
    }
    // Check that we ran all tests.
    println!(
        "Ran {} out of {} tests and skipped {}.",
        tests_run, num_tests, skipped_tests
    );
    assert_eq!(num_tests - skipped_tests, tests_run);
}
