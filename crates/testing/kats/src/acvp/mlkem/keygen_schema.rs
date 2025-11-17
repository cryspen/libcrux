use super::super::schema_common::*;
use serde::Deserialize;

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct KeyGenPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub z: [u8; 32],

    #[serde(with = "hex::serde")]
    pub d: [u8; 32],
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct KeyGenPromptTestGroup {
    pub tgId: usize,
    pub testType: String,
    pub parameterSet: String,
    pub tests: Vec<KeyGenPrompt>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct KeyGenResult {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub ek: Vec<u8>,

    #[serde(with = "hex::serde")]
    pub dk: Vec<u8>,
}

pub type ResultKeyGenTestGroup = TestGroupResults<KeyGenResult>;

impl TestResult for KeyGenResult {
    fn tc_id(&self) -> usize {
        self.tcId
    }
}
