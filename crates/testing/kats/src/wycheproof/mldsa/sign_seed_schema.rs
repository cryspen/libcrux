pub use super::sign_common::*;
use serde::{Deserialize, Serialize};

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
/// Sign tests for ML-DSA (`seed`)
pub struct MlDsaSignTestsWithSeed {
    /// the primitive tested in the test file
    pub algorithm: String,

    /// additional documentation
    pub header: Vec<String>,

    pub notes: Notes,

    /// the number of test vectors in this test
    pub number_of_tests: i64,

    pub schema: String,

    pub test_groups: Vec<TestGroup>,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestGroup {
    #[serde(rename = "type")]
    pub test_group_type: Type,

    /// 32-byte seed that generated the private key
    #[serde(with = "hex::serde")]
    pub private_seed: [u8; 32],

    pub tests: Vec<Test>,

    pub source: Source,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum Type {
    #[serde(rename = "MlDsaSign")]
    MlDsaSign,
}
