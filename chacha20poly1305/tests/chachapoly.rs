use std::{fs::File, io::BufReader};

use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::Value;

pub(crate) trait ReadFromFile {
    fn from_file<T: DeserializeOwned>(file_str: &'static str) -> T {
        let file = match File::open(file_str) {
            Ok(f) => f,
            Err(_) => panic!("Couldn't open file {file_str}."),
        };
        let reader = BufReader::new(file);
        match serde_json::from_reader(reader) {
            Ok(r) => r,
            Err(e) => {
                println!("{:?}", e);
                panic!("Error reading file {file_str}.")
            }
        }
    }
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
    #[serde(with = "hex::serde")]
    key: Vec<u8>,
    #[serde(with = "hex::serde")]
    iv: Vec<u8>,
    #[serde(with = "hex::serde")]
    aad: Vec<u8>,
    #[serde(with = "hex::serde")]
    msg: Vec<u8>,
    #[serde(with = "hex::serde")]
    ct: Vec<u8>,
    #[serde(with = "hex::serde")]
    tag: Vec<u8>,
    result: String,
    flags: Vec<String>,
}

impl ReadFromFile for AeadTestVector {}

#[allow(non_snake_case)]
#[test]
fn wycheproof() {
    let chacha_poly_tests: AeadTestVector =
        AeadTestVector::from_file("../tests/wycheproof/chacha20_poly1305_test.json");

    let num_tests = chacha_poly_tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    assert_eq!(chacha_poly_tests.algorithm, "CHACHA20-POLY1305");

    test_group(chacha_poly_tests, &mut skipped_tests, &mut tests_run);

    fn test_group(test_vec: AeadTestVector, skipped_tests: &mut usize, tests_run: &mut usize) {
        for testGroup in test_vec.testGroups.iter() {
            assert_eq!(testGroup.r#type, "AeadTest");
            assert_eq!(testGroup.keySize, 256);

            let invalid_iv = testGroup.ivSize != 96;

            for test in testGroup.tests.iter() {
                let valid = test.result.eq("valid");
                if invalid_iv {
                    // AEAD requires input of a 12-byte nonce.
                    let nonce = &test.iv;
                    assert!(nonce.len() != 12);
                    *skipped_tests += 1;
                    continue;
                }
                println!("Test {:?}: {:?}", test.tcId, test.comment);
                let nonce = <&[u8; 12]>::try_from(&test.iv[..]).unwrap();
                let msg = &test.msg;
                let aad = &test.aad;
                let exp_cipher = &test.ct;
                let exp_tag = &test.tag;
                let key = <&[u8; 32]>::try_from(&test.key[..]).unwrap();

                let mut ctxt = msg.clone();
                let tag = match libcrux_chacha20poly1305::encrypt(key, msg, &mut ctxt, aad, nonce)
                {
                    Ok((_v, t)) => t,
                    Err(_) => {
                        *tests_run += 1;
                        continue;
                    }
                };
                if valid {
                    assert_eq!(tag, exp_tag.as_slice());
                } else {
                    assert_ne!(tag, exp_tag.as_slice());
                }
                assert_eq!(ctxt, exp_cipher.as_slice());

                let mut decrypted = vec![0; msg.len()];
                match libcrux_chacha20poly1305::decrypt(key, &mut decrypted, &ctxt, aad, nonce) {
                    Ok(m) => {
                        assert_eq!(m, msg);
                        assert_eq!(&decrypted, msg);
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
