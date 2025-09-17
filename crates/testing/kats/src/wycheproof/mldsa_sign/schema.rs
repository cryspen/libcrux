// Example code that deserializes and serializes the model.
// extern crate serde;
// #[macro_use]
// extern crate serde_derive;
// extern crate serde_json;
//
// use generated_module::sign_schema;
//
// fn main() {
//     let json = r#"{"answer": 42}"#;
//     let model: sign_schema = serde_json::from_str(&json).unwrap();
// }

use serde::{Deserialize, Serialize};

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SignSchema {
    algorithm: String,

    header: Vec<String>,

    notes: Notes,

    number_of_tests: i64,

    schema: String,

    pub test_groups: Vec<TestGroup>,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct Notes {
    boundary_condition: BoundaryCondition,

    incorrect_private_key_length: BoundaryCondition,

    invalid_private_key: BoundaryCondition,

    many_steps: BoundaryCondition,

    valid_signature: BoundaryCondition,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BoundaryCondition {
    bug_type: String,

    description: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Source {
    name: String,
    version: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestGroup {
    #[serde(rename = "type")]
    test_group_type: Type,

    #[serde(with = "hex::serde")]
    pub private_key: Vec<u8>,

    pub tests: Vec<Test>,

    source: Source,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum Type {
    #[serde(rename = "MlDsaSign")]
    MlDsaSign,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test {
    tc_id: i64,

    comment: String,

    #[serde(with = "hex::serde")]
    pub msg: Vec<u8>,

    #[serde(default)]
    #[serde(with = "hex::serde")]
    pub ctx: Vec<u8>,

    #[serde(with = "hex::serde")]
    pub sig: Vec<u8>,

    pub result: SignResult,

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
