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
    pub key_size: usize,
    pub tag_size: usize,
    pub tests: Vec<Test>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test {
    pub tc_id: usize,
    pub flags: Vec<String>,
    #[serde(with = "hex::serde")]
    pub key: Vec<u8>,
    #[serde(with = "hex::serde")]
    pub msg: Vec<u8>,
    #[serde(with = "hex::serde")]
    pub tag: Vec<u8>,
    pub result: TestResult,
}

impl TestSet {
    pub fn load_hmac_sha1() -> Self {
        let data = include_str!("../../wycheproof/hmac_sha1_test.json");
        serde_json::from_str(data).expect("could not deserialize hmac_sha1 KAT file")
    }

    pub fn load_hmac_sha256() -> Self {
        let data = include_str!("../../wycheproof/hmac_sha256_test.json");
        serde_json::from_str(data).expect("could not deserialize hmac_sha256 KAT file")
    }

    pub fn load_hmac_sha384() -> Self {
        let data = include_str!("../../wycheproof/hmac_sha384_test.json");
        serde_json::from_str(data).expect("could not deserialize hmac_sha384 KAT file")
    }

    pub fn load_hmac_sha512() -> Self {
        let data = include_str!("../../wycheproof/hmac_sha512_test.json");
        serde_json::from_str(data).expect("could not deserialize hmac_sha512 KAT file")
    }
}
