use serde::{Deserialize, Serialize};

use super::schema_common::TestResult;

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestSet {
    pub number_of_tests: usize,
    pub test_groups: Vec<TestGroup>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TestGroup {
    pub tests: Vec<Test>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test {
    pub tc_id: usize,
    pub flags: Vec<String>,
    #[serde(with = "hex::serde")]
    pub public: Vec<u8>,
    #[serde(with = "hex::serde")]
    pub private: Vec<u8>,
    #[serde(with = "hex::serde")]
    pub shared: Vec<u8>,
    pub result: TestResult,
}

impl TestSet {
    pub fn load_x25519() -> Self {
        let data = include_str!("../../wycheproof/x25519_test.json");
        serde_json::from_str(data).expect("could not deserialize x25519 KAT file")
    }
}
