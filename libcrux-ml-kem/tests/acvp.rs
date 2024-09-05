#![cfg(feature = "pre-verification")]

use serde::{de::DeserializeOwned, Deserialize};
use serde_json::Value;
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

            let expectred_result = results
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
                "ML-KEM-512" => check(mlkem512::generate_key_pair(seed), expectred_result),
                #[cfg(feature = "mlkem768")]
                "ML-KEM-768" => check(mlkem768::generate_key_pair(seed), expectred_result),
                #[cfg(feature = "mlkem1024")]
                "ML-KEM-1024" => check(mlkem1024::generate_key_pair(seed), expectred_result),
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

// #[derive(Deserialize)]
// #[allow(non_snake_case, dead_code)]
// struct EncapDecapPromptTestGroup {
//     tgId: usize,
//     testType: String,
//     parameterSet: String,
//     function: String,
//     tests: Vec<EncapDecapPrompt>,
// }

// #[derive(Deserialize)]
// #[allow(non_snake_case, dead_code)]
// struct EncapDecapResult {
//     tcId: usize,

//     #[serde(with = "hex::serde")]
//     ek: Vec<u8>,

//     #[serde(with = "hex::serde")]
//     dk: Vec<u8>,
// }

// #[derive(Deserialize)]
// #[allow(non_snake_case, dead_code)]
// struct ResultEncapDedapTestGroup {
//     tgId: usize,
//     tests: Vec<KeyGenResult>,
// }

#[test]
fn encap_decap() {
    use libcrux_ml_kem::*;

    let prompts: Prompts<Value> = read("encap-decap", "prompt.json");
    assert!(prompts.algorithm == "ML-KEM");
    assert!(prompts.revision == "FIPS203");

    let results: Results<Value> = read("encap-decap", "expectedResults.json");
    assert!(results.algorithm == "ML-KEM");
    assert!(results.revision == "FIPS203");

    for kat in prompts.testGroups {
        let parameter_set = kat.get("parameterSet").unwrap().as_str().unwrap();
        assert!(
            parameter_set == "ML-KEM-512"
                || parameter_set == "ML-KEM-768"
                || parameter_set == "ML-KEM-1024"
        );
        eprintln!(
            "{parameter_set} {}",
            kat.get("function").unwrap().as_str().unwrap()
        );

        let mut tests = kat.get("tests").unwrap().as_array().unwrap();
        for test in tests {
            eprintln!("  {}", test.get("tcId").unwrap());
            //             let mut seed = [0u8; 64];
            //             seed[..32].copy_from_slice(&test.d);
            //             seed[32..].copy_from_slice(&test.z);

            //             fn check<const EK_LEN: usize, const DK_LEN: usize>(
            //                 keys: MlKemKeyPair<DK_LEN, EK_LEN>,
            //                 result: &KeyGenResult,
            //             ) {
            //                 assert_eq!(result.ek, keys.pk());
            //                 assert_eq!(result.dk, keys.sk());
            //             }

            //             let expectred_result = results
            //                 .testGroups
            //                 .iter()
            //                 .find(|tg| tg.tgId == kat.tgId)
            //                 .unwrap()
            //                 .tests
            //                 .iter()
            //                 .find(|t| t.tcId == test.tcId)
            //                 .unwrap();

            //             match parameter_set.as_str() {
            //                 #[cfg(feature = "mlkem512")]
            //                 "ML-KEM-512" => check(mlkem512::generate_key_pair(seed), expectred_result),
            //                 #[cfg(feature = "mlkem768")]
            //                 "ML-KEM-768" => check(mlkem768::generate_key_pair(seed), expectred_result),
            //                 #[cfg(feature = "mlkem1024")]
            //                 "ML-KEM-1024" => check(mlkem1024::generate_key_pair(seed), expectred_result),
            //                 _ => unimplemented!(),
            //             }
        }
    }
}
