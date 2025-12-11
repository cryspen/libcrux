use super::super::schema_common::*;
use serde::Deserialize;

#[derive(Deserialize)]
pub struct Randomness(#[serde(with = "hex::serde")] pub [u8; 32]);

#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct SigGenPromptTestGroup {
    pub tgId: usize,
    pub testType: String,
    pub parameterSet: String,
    pub deterministic: bool,
    pub signatureInterface: String,
    pub preHash: Option<String>,
    #[serde(default)]
    pub externalMu: bool,
    pub tests: Vec<SigGenTest>,
}
#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct SigGenTest {
    pub tcId: usize,
    #[serde(with = "hex::serde")]
    pub sk: Vec<u8>,
    #[serde(default)]
    pub rnd: Option<Randomness>,
    #[serde(default, with = "hex::serde")]
    pub message: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    pub mu: Vec<u8>,
    #[serde(with = "hex::serde", default)]
    pub context: Vec<u8>,
    #[serde(default)]
    pub hashAlg: Option<String>,
}

#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct SigGenResult {
    pub tcId: usize,
    #[serde(with = "hex::serde")]
    pub signature: Vec<u8>,
}

pub type ResultSigGenTestGroup = TestGroupResults<SigGenResult>;

impl TestResult for SigGenResult {
    fn tc_id(&self) -> usize {
        self.tcId
    }
}
