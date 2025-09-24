use serde::{Deserialize, Serialize};

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct Notes {
    pub boundary_condition: BoundaryCondition,

    pub incorrect_private_key_length: BoundaryCondition,

    pub invalid_private_key: BoundaryCondition,

    pub many_steps: BoundaryCondition,

    pub valid_signature: BoundaryCondition,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Source {
    pub name: String,
    pub version: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BoundaryCondition {
    pub bug_type: String,

    pub description: String,
}

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
    pub flags: Vec<Flag>,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum Flag {
    #[serde(rename = "BoundaryCondition")]
    BoundaryCondition,

    #[serde(rename = "IncorrectPrivateKeyLength")]
    IncorrectPrivateKeyLength,

    #[serde(rename = "InvalidPrivateKey")]
    InvalidPrivateKey,

    #[serde(rename = "InvalidContext")]
    InvalidContext,

    #[serde(rename = "ManySteps")]
    ManySteps,

    #[serde(rename = "ValidSignature")]
    ValidSignature,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SignResult {
    Invalid,

    Valid,
}
