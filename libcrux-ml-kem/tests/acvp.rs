#![cfg(all(
    feature = "pre-verification",
    any(feature = "mlkem512", feature = "mlkem768", feature = "mlkem1024",)
))]

use serde::{de::DeserializeOwned, Deserialize};
use std::{fs::File, io::BufReader, path::Path};

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct KeyGenPrompt {
    tcId: usize,

    #[serde(with = "hex::serde")]
    z: [u8; 32],

    #[serde(with = "hex::serde")]
    d: [u8; 32],
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct KeyGenPromptTestGroup {
    tgId: usize,
    testType: String,
    parameterSet: String,
    tests: Vec<KeyGenPrompt>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct Prompts<TG> {
    vsId: usize,
    algorithm: String,
    mode: String,
    revision: String,
    isSample: bool,
    testGroups: Vec<TG>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct KeyGenResult {
    tcId: usize,

    #[serde(with = "hex::serde")]
    ek: Vec<u8>,

    #[serde(with = "hex::serde")]
    dk: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct ResultPromptTestGroup {
    tgId: usize,
    tests: Vec<KeyGenResult>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct Results<TG> {
    vsId: usize,
    algorithm: String,
    mode: String,
    revision: String,
    isSample: bool,
    testGroups: Vec<TG>,
}

#[test]
fn keygen() {
    use libcrux_ml_kem::*;

    let prompts: Prompts<KeyGenPromptTestGroup> = read("keygen", "prompt.json");
    assert!(prompts.algorithm == "ML-KEM");
    assert!(prompts.revision == "FIPS203");

    let results: Results<ResultPromptTestGroup> = read("keygen", "expectedResults.json");
    assert!(results.algorithm == "ML-KEM");
    assert!(results.revision == "FIPS203");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-KEM-512"
                || parameter_set == "ML-KEM-768"
                || parameter_set == "ML-KEM-1024"
        );
        eprintln!("{parameter_set}");

        for test in kat.tests {
            eprintln!("  {}", test.tcId);
            let mut seed = [0u8; 64];
            seed[..32].copy_from_slice(&test.d);
            seed[32..].copy_from_slice(&test.z);

            fn check<const EK_LEN: usize, const DK_LEN: usize>(
                keys: MlKemKeyPair<DK_LEN, EK_LEN>,
                result: &KeyGenResult,
            ) {
                assert_eq!(result.ek, keys.pk());
                assert_eq!(result.dk, keys.sk());
            }

            let expected_result = results
                .testGroups
                .iter()
                .find(|tg| tg.tgId == kat.tgId)
                .unwrap()
                .tests
                .iter()
                .find(|t| t.tcId == test.tcId)
                .unwrap();

            match parameter_set.as_str() {
                #[cfg(feature = "mlkem512")]
                "ML-KEM-512" => check(mlkem512::generate_key_pair(seed), expected_result),
                #[cfg(feature = "mlkem768")]
                "ML-KEM-768" => check(mlkem768::generate_key_pair(seed), expected_result),
                #[cfg(feature = "mlkem1024")]
                "ML-KEM-1024" => check(mlkem1024::generate_key_pair(seed), expected_result),
                _ => unimplemented!(),
            }
        }
    }
}

fn read<T: DeserializeOwned>(variant: &str, file: &str) -> T {
    let katfile_path = Path::new("tests")
        .join("kats")
        .join("acvp-1_1_0_35")
        .join(variant)
        .join(file);
    let katfile = File::open(katfile_path).expect("Could not open KAT file.");
    let reader = BufReader::new(katfile);

    serde_json::from_reader(reader).expect("Could not deserialize KAT file.")
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct EncapPrompt {
    tcId: usize,

    #[serde(with = "hex::serde")]
    ek: Vec<u8>,

    #[serde(with = "hex::serde")]
    m: [u8; 32],
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct DecapPrompt {
    tcId: usize,

    #[serde(with = "hex::serde")]
    c: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct EncapDecapPromptTestGroup {
    tgId: usize,
    testType: String,
    parameterSet: String,
    #[serde(flatten)]
    tests: EncapDecapTests,
}

#[allow(non_snake_case, dead_code)]
#[derive(Deserialize)]
#[serde(tag = "function")]
enum EncapDecapTests {
    #[serde(rename(deserialize = "encapsulation"))]
    EncapTests { tests: Vec<EncapPrompt> },
    #[serde(rename(deserialize = "decapsulation"))]
    DecapTests {
        #[serde(with = "hex::serde")]
        dk: Vec<u8>,
        tests: Vec<DecapPrompt>,
    },
}

#[derive(Deserialize)]
#[serde(untagged)]
#[allow(non_snake_case, dead_code)]
enum EncapDecapResult {
    EncapResult {
        tcId: usize,
        #[serde(with = "hex::serde")]
        c: Vec<u8>,
        #[serde(with = "hex::serde")]
        k: Vec<u8>,
    },
    DecapResult {
        tcId: usize,
        #[serde(with = "hex::serde")]
        k: Vec<u8>,
    },
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct ResultEncapDecapTestGroup {
    tgId: usize,
    tests: Vec<EncapDecapResult>,
}

#[test]
fn encap_decap() {
    use libcrux_ml_kem::*;

    let prompts: Prompts<EncapDecapPromptTestGroup> = read("encap-decap", "prompt.json");
    assert!(prompts.algorithm == "ML-KEM");
    assert!(prompts.revision == "FIPS203");

    let results: Results<ResultEncapDecapTestGroup> = read("encap-decap", "expectedResults.json");
    assert!(results.algorithm == "ML-KEM");
    assert!(results.revision == "FIPS203");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-KEM-512"
                || parameter_set == "ML-KEM-768"
                || parameter_set == "ML-KEM-1024"
        );
        eprintln!("{parameter_set}");

        match kat.tests {
            EncapDecapTests::EncapTests { tests } => {
                for test in tests {
                    let expected_result = results
                        .testGroups
                        .iter()
                        .find(|tg| tg.tgId == kat.tgId)
                        .unwrap()
                        .tests
                        .iter()
                        .find(|t| {
                            if let EncapDecapResult::EncapResult { tcId, .. } = t {
                                *tcId == test.tcId
                            } else {
                                false
                            }
                        })
                        .unwrap();

                    let EncapDecapResult::EncapResult { c, k, .. } = expected_result else {
                        unreachable!()
                    };

                    let ek = test.ek;
                    let randomness = test.m;
                    match parameter_set.as_str() {
                        #[cfg(feature = "mlkem512")]
                        "ML-KEM-512" => {
                            let (actual_ct, actual_k) = mlkem512::encapsulate(
                                &mlkem512::MlKem512PublicKey::try_from(ek.as_slice()).unwrap(),
                                randomness,
                            );
                            assert_eq!(actual_ct.as_ref(), c);
                            assert_eq!(actual_k.as_ref(), k);
                        }
                        #[cfg(feature = "mlkem768")]
                        "ML-KEM-768" => {
                            let (actual_ct, actual_k) = mlkem768::encapsulate(
                                &mlkem768::MlKem768PublicKey::try_from(ek.as_slice()).unwrap(),
                                randomness,
                            );
                            assert_eq!(actual_ct.as_ref(), c);
                            assert_eq!(actual_k.as_ref(), k);
                        }
                        #[cfg(feature = "mlkem1024")]
                        "ML-KEM-1024" => {
                            let (actual_ct, actual_k) = mlkem1024::encapsulate(
                                &mlkem1024::MlKem1024PublicKey::try_from(ek.as_slice()).unwrap(),
                                randomness,
                            );
                            assert_eq!(actual_ct.as_ref(), c);
                            assert_eq!(actual_k.as_ref(), k);
                        }
                        _ => unimplemented!(),
                    }
                }
            }
            EncapDecapTests::DecapTests { dk, tests } => {
                for test in tests {
                    let expected_result = results
                        .testGroups
                        .iter()
                        .find(|tg| tg.tgId == kat.tgId)
                        .unwrap()
                        .tests
                        .iter()
                        .find(|t| {
                            if let EncapDecapResult::DecapResult { tcId, .. } = t {
                                *tcId == test.tcId
                            } else {
                                false
                            }
                        })
                        .unwrap();

                    let EncapDecapResult::DecapResult { k, .. } = expected_result else {
                        unreachable!()
                    };

                    let c = test.c;
                    match parameter_set.as_str() {
                        #[cfg(feature = "mlkem512")]
                        "ML-KEM-512" => {
                            let dk = mlkem512::MlKem512PrivateKey::try_from(dk.as_slice()).unwrap();
                            let c = mlkem512::MlKem512Ciphertext::try_from(c.as_slice()).unwrap();
                            let actual_k = mlkem512::decapsulate(&dk, &c);
                            assert_eq!(actual_k.as_ref(), k);
                        }
                        #[cfg(feature = "mlkem768")]
                        "ML-KEM-768" => {
                            let dk = mlkem768::MlKem768PrivateKey::try_from(dk.as_slice()).unwrap();
                            let c = mlkem768::MlKem768Ciphertext::try_from(c.as_slice()).unwrap();
                            let actual_k = mlkem768::decapsulate(&dk, &c);
                            assert_eq!(actual_k.as_ref(), k);
                        }
                        #[cfg(feature = "mlkem1024")]
                        "ML-KEM-1024" => {
                            let dk =
                                mlkem1024::MlKem1024PrivateKey::try_from(dk.as_slice()).unwrap();
                            let c = mlkem1024::MlKem1024Ciphertext::try_from(c.as_slice()).unwrap();
                            let actual_k = mlkem1024::decapsulate(&dk, &c);
                            assert_eq!(actual_k.as_ref(), k);
                        }

                        _ => unimplemented!(),
                    }
                }
            }
        }
    }
}
