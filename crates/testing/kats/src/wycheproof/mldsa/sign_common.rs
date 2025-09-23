pub use super::super::schema_common::*;
use serde::{Deserialize, Serialize};

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test {
    /// Identifier of the test case
    pub tc_id: i64,

    /// A brief description of the test case
    pub comment: String,

    /// The message to sign
    #[serde(with = "hex::serde")]
    pub msg: Vec<u8>,

    /// [optional] The additional context string (empty if not provided)
    #[serde(default)]
    #[serde(with = "hex::serde")]
    pub ctx: Vec<u8>,

    /// The encoded signature (empty in case of expected failure)
    #[serde(with = "hex::serde")]
    pub sig: Vec<u8>,

    /// Test result
    pub result: SignResult,

    /// A list of flags
    pub flags: Vec<String>,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SignResult {
    Invalid,

    Valid,
}
