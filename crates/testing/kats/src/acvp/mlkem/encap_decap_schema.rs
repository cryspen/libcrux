use super::super::schema_common::*;
use serde::Deserialize;

#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct EncapPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub ek: Vec<u8>,

    #[serde(with = "hex::serde")]
    pub m: [u8; 32],
}

#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct DecapPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub c: Vec<u8>,

    #[serde(with = "hex::serde")]
    pub dk: Vec<u8>,
}

#[allow(non_snake_case)]
#[derive(Deserialize)]
pub struct EncapKeyCheckPrompt {
    pub tcId: usize,
    #[serde(with = "hex::serde")]
    pub ek: Vec<u8>,
}

#[allow(non_snake_case)]
#[derive(Deserialize)]
pub struct DecapKeyCheckPrompt {
    pub tcId: usize,
    #[serde(with = "hex::serde")]
    pub dk: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case)]
pub struct EncapDecapPromptTestGroup {
    pub tgId: usize,
    pub testType: String,
    pub parameterSet: String,
    #[serde(flatten)]
    pub tests: EncapDecapTestPrompts,
}

#[allow(non_snake_case)]
#[derive(Deserialize)]
#[serde(tag = "function")]
pub enum EncapDecapTestPrompts {
    #[serde(rename(deserialize = "encapsulation"))]
    EncapTests { tests: Vec<EncapPrompt> },
    #[serde(rename(deserialize = "decapsulation"))]
    DecapTests { tests: Vec<DecapPrompt> },
    #[serde(rename(deserialize = "encapsulationKeyCheck"))]
    EncapKeyCheck { tests: Vec<EncapKeyCheckPrompt> },
    #[serde(rename(deserialize = "decapsulationKeyCheck"))]
    DecapKeyCheck { tests: Vec<DecapKeyCheckPrompt> },
}

#[derive(Deserialize)]
#[serde(untagged)]
#[allow(non_snake_case)]
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
    KeyCheckResult {
        tcId: usize,
        testPassed: bool,
    },
}

impl TestResult for EncapDecapResult {
    fn tc_id(&self) -> usize {
        match self {
            Self::EncapResult { tcId, .. } => *tcId,
            Self::DecapResult { tcId, .. } => *tcId,
            Self::KeyCheckResult { tcId, .. } => *tcId,
        }
    }
}

pub type ResultEncapDecapTestGroup = TestGroupResults<EncapDecapResult>;
