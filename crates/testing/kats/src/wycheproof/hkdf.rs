use serde::{Deserialize, Serialize};

use super::schema_common::TestResult;

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestSet {
    pub number_of_tests: usize,
    pub test_groups: Vec<TestGroup>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestGroup {
    pub tests: Vec<Test>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test {
    pub tc_id: usize,
    pub flags: Vec<String>,
    #[serde(with = "hex::serde")]
    pub ikm: Vec<u8>,
    #[serde(with = "hex::serde")]
    pub salt: Vec<u8>,
    #[serde(with = "hex::serde")]
    pub info: Vec<u8>,
    pub size: usize,
    #[serde(with = "hex::serde")]
    pub okm: Vec<u8>,
    pub result: TestResult,
}

impl TestSet {
    pub fn load_sha256() -> Self {
        let data = include_str!("../../wycheproof/hkdf_sha256_test.json");
        serde_json::from_str(data).expect("could not deserialize hkdf_sha256 KAT file")
    }

    pub fn load_sha384() -> Self {
        let data = include_str!("../../wycheproof/hkdf_sha384_test.json");
        serde_json::from_str(data).expect("could not deserialize hkdf_sha384 KAT file")
    }

    pub fn load_sha512() -> Self {
        let data = include_str!("../../wycheproof/hkdf_sha512_test.json");
        serde_json::from_str(data).expect("could not deserialize hkdf_sha512 KAT file")
    }
}
