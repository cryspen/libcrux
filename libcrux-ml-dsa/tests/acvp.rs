#![cfg(feature = "acvp")]
use serde::{de::DeserializeOwned, Deserialize};
use std::{fs::File, io::BufReader, path::Path};

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
struct Results<TG> {
    vsId: usize,
    algorithm: String,
    mode: String,
    revision: String,
    isSample: bool,
    testGroups: Vec<TG>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct KeyGenPrompt {
    tcId: usize,

    #[serde(with = "hex::serde")]
    seed: [u8; 32],
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
struct KeyGenResult {
    tcId: usize,

    #[serde(with = "hex::serde")]
    pk: Vec<u8>,

    #[serde(with = "hex::serde")]
    sk: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct ResultPromptTestGroup {
    tgId: usize,
    tests: Vec<KeyGenResult>,
}

#[test]
fn keygen() {
    use libcrux_ml_dsa::*;

    let prompts: Prompts<KeyGenPromptTestGroup> = read("keygen", "prompt.json");
    assert!(prompts.algorithm == "ML-DSA");
    assert!(prompts.revision == "FIPS204");

    let results: Results<ResultPromptTestGroup> = read("keygen", "expectedResults.json");
    assert!(results.algorithm == "ML-DSA");
    assert!(results.revision == "FIPS204");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-DSA-44"
                || parameter_set == "ML-DSA-65"
                || parameter_set == "ML-DSA-87"
        );
        eprintln!("{parameter_set}");

        for test in kat.tests {
            eprintln!("  {}", test.tcId);
            fn check<const VK_LEN: usize, const SK_LEN: usize>(
                keys: MLDSAKeyPair<VK_LEN, SK_LEN>,
                result: &KeyGenResult,
            ) {
                assert_eq!(result.pk, keys.verification_key.as_slice());
                assert_eq!(result.sk, keys.signing_key.as_slice());
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
                "ML-DSA-44" => check(ml_dsa_44::generate_key_pair(test.seed), expected_result),

                "ML-DSA-65" => check(ml_dsa_65::generate_key_pair(test.seed), expected_result),

                "ML-DSA-87" => check(ml_dsa_87::generate_key_pair(test.seed), expected_result),
                _ => unimplemented!(),
            }
        }
    }
}

fn read<T: DeserializeOwned>(variant: &str, file: &str) -> T {
    let katfile_path = Path::new("tests")
        .join("kats")
        .join("acvp-1_1_0_36")
        .join(variant)
        .join(file);
    let katfile = File::open(katfile_path).expect("Could not open KAT file.");
    let reader = BufReader::new(katfile);

    serde_json::from_reader(reader).expect("Could not deserialize KAT file.")
}

#[test]
fn siggen() {
    use libcrux_ml_dsa::*;

    let prompts: Prompts<SigGenPromptTestGroup> = read("siggen", "prompt.json");
    assert!(prompts.algorithm == "ML-DSA");
    assert!(prompts.revision == "FIPS204");

    let results: Results<ResultSigGenTestGroup> = read("siggen", "expectedResults.json");
    assert!(results.algorithm == "ML-DSA");
    assert!(results.revision == "FIPS204");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-DSA-44"
                || parameter_set == "ML-DSA-65"
                || parameter_set == "ML-DSA-87"
        );
        eprintln!("{parameter_set}");

        for test in kat.tests {
            eprintln!("  {}", test.tcId);
            let expected_result = results
                .testGroups
                .iter()
                .find(|tg| tg.tgId == kat.tgId)
                .unwrap()
                .tests
                .iter()
                .find(|t| t.tcId == test.tcId)
                .unwrap();

            let Randomness(rnd) = test.rnd.unwrap_or(Randomness([0u8; 32]));

            match parameter_set.as_str() {
                "ML-DSA-44" => {
                    let signature = ml_dsa_44::sign_internal(
                        &MLDSASigningKey(test.sk.try_into().unwrap()),
                        &test.message,
                        rnd,
                    )
                    .unwrap();
                    assert_eq!(signature.as_slice(), expected_result.signature);
                }

                "ML-DSA-65" => {
                    let signature = ml_dsa_65::sign_internal(
                        &MLDSASigningKey(test.sk.try_into().unwrap()),
                        &test.message,
                        rnd,
                    )
                    .unwrap();
                    assert_eq!(signature.as_slice(), expected_result.signature);
                }

                "ML-DSA-87" => {
                    let signature = ml_dsa_87::sign_internal(
                        &MLDSASigningKey(test.sk.try_into().unwrap()),
                        &test.message,
                        rnd,
                    )
                    .unwrap();
                    assert_eq!(signature.as_slice(), expected_result.signature);
                }
                _ => unimplemented!(),
            }
        }
    }
}

#[test]
fn sigver() {
    use libcrux_ml_dsa::*;

    let prompts: Prompts<SigVerPromptTestGroup> = read("sigver", "prompt.json");
    assert!(prompts.algorithm == "ML-DSA");
    assert!(prompts.revision == "FIPS204");

    let results: Results<ResultSigVerTestGroup> = read("sigver", "expectedResults.json");
    assert!(results.algorithm == "ML-DSA");
    assert!(results.revision == "FIPS204");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-DSA-44"
                || parameter_set == "ML-DSA-65"
                || parameter_set == "ML-DSA-87"
        );
        eprintln!("{parameter_set}");

        for test in kat.tests {
            eprintln!("  {}", test.tcId);
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
                "ML-DSA-44" => {
                    let valid = ml_dsa_44::verify_internal(
                        &MLDSAVerificationKey(kat.pk.clone().try_into().unwrap()),
                        &test.message,
                        &MLDSASignature(test.signature.try_into().unwrap()),
                    );
                    assert_eq!(valid.is_ok(), expected_result.testPassed);
                }

                "ML-DSA-65" => {
                    let valid = ml_dsa_65::verify_internal(
                        &MLDSAVerificationKey(kat.pk.clone().try_into().unwrap()),
                        &test.message,
                        &MLDSASignature(test.signature.try_into().unwrap()),
                    );
                    assert_eq!(valid.is_ok(), expected_result.testPassed);
                }

                "ML-DSA-87" => {
                    let valid = ml_dsa_87::verify_internal(
                        &MLDSAVerificationKey(kat.pk.clone().try_into().unwrap()),
                        &test.message,
                        &MLDSASignature(test.signature.try_into().unwrap()),
                    );
                    assert_eq!(valid.is_ok(), expected_result.testPassed);
                }
                _ => unimplemented!(),
            }
        }
    }
}

#[derive(Deserialize)]
struct Randomness(#[serde(with = "hex::serde")] [u8; 32]);

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct SigGenPromptTestGroup {
    tgId: usize,
    testType: String,
    parameterSet: String,
    deterministic: bool,
    tests: Vec<SigGenTest>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct SigGenTest {
    tcId: usize,
    #[serde(with = "hex::serde")]
    sk: Vec<u8>,
    #[serde(with = "hex::serde")]
    message: Vec<u8>,
    #[serde(default)]
    rnd: Option<Randomness>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct SigGenResult {
    tcId: usize,
    #[serde(with = "hex::serde")]
    signature: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct ResultSigGenTestGroup {
    tgId: usize,
    tests: Vec<SigGenResult>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct SigVerPromptTestGroup {
    tgId: usize,
    testType: String,
    parameterSet: String,
    #[serde(with = "hex::serde")]
    pk: Vec<u8>,
    tests: Vec<SigVerTest>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct SigVerTest {
    tcId: usize,
    #[serde(with = "hex::serde")]
    message: Vec<u8>,
    #[serde(with = "hex::serde")]
    signature: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct ResultSigVerTestGroup {
    tgId: usize,
    tests: Vec<SigVerResult>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
struct SigVerResult {
    tcId: usize,
    testPassed: bool,
}
