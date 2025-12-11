use serde::Deserialize;

use super::super::schema_common::*;

#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct KeyGenPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub seed: [u8; 32],
}

#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct KeyGenPromptTestGroup {
    pub tgId: usize,
    pub testType: String,
    pub parameterSet: String,
    pub tests: Vec<KeyGenPrompt>,
}

#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct KeyGenResult {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub pk: Vec<u8>,

    #[serde(with = "hex::serde")]
    pub sk: Vec<u8>,
}

pub type ResultKeyGenTestGroup = TestGroupResults<KeyGenResult>;

impl TestResult for KeyGenResult {
    fn tc_id(&self) -> usize {
        self.tcId
    }
}
