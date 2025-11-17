use super::super::schema_common::*;
use serde::Deserialize;

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct EncapPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub ek: Vec<u8>,

    #[serde(with = "hex::serde")]
    pub m: [u8; 32],
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct DecapPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub c: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct EncapDecapPromptTestGroup {
    pub tgId: usize,
    pub testType: String,
    pub parameterSet: String,
    #[serde(flatten)]
    pub tests: EncapDecapTestPrompts,
}

#[allow(non_snake_case, dead_code)]
#[derive(Deserialize)]
#[serde(tag = "function")]
pub enum EncapDecapTestPrompts {
    #[serde(rename(deserialize = "encapsulation"))]
    EncapTests { tests: Vec<EncapPrompt> },
    #[serde(rename(deserialize = "decapsulation"))]
    DecapTests {
        #[serde(with = "hex::serde")]
        dk: Vec<u8>,
        tests: Vec<DecapPrompt>,
    },
}

#[derive(Deserialize)]
#[serde(untagged)]
#[allow(non_snake_case, dead_code)]
pub enum EncapDecapResult {
    EncapResult {
        tcId: usize,
        #[serde(with = "hex::serde")]
        c: Vec<u8>,
        #[serde(with = "hex::serde")]
        k: Vec<u8>,
    },
    DecapResult {
        tcId: usize,
        #[serde(with = "hex::serde")]
        k: Vec<u8>,
    },
}

impl TestResult for EncapDecapResult {
    fn tc_id(&self) -> usize {
        match self {
            Self::EncapResult { tcId, .. } => *tcId,
            Self::DecapResult { tcId, .. } => *tcId,
        }
    }
}

pub type ResultEncapDecapTestGroup = TestGroupResults<EncapDecapResult>;
