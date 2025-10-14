use super::common::*;
use serde::Deserialize;

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct SigVerPromptTestGroup {
    pub tgId: usize,
    pub testType: String,
    pub parameterSet: String,
    pub preHash: Option<String>,
    pub signatureInterface: String,
    #[serde(default)]
    pub externalMu: bool,
    pub tests: Vec<SigVerTest>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct SigVerTest {
    pub tcId: usize,
    #[serde(default, with = "hex::serde")]
    pub message: Vec<u8>,
    #[serde(default, with = "hex::serde")]
    pub mu: Vec<u8>,
    #[serde(with = "hex::serde")]
    pub signature: Vec<u8>,
    #[serde(with = "hex::serde")]
    pub pk: Vec<u8>,
    #[serde(with = "hex::serde", default)]
    pub context: Vec<u8>,
    #[serde(default)]
    pub hashAlg: Option<String>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct SigVerResult {
    pub tcId: usize,
    pub testPassed: bool,
}

pub type ResultSigVerTestGroup = TestGroupResults<SigVerResult>;
impl TestResult for SigVerResult {
    fn tc_id(&self) -> usize {
        self.tcId
    }
}
