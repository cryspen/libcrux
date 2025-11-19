// Example code that deserializes and serializes the model.
// extern crate serde;
// #[macro_use]
// extern crate serde_derive;
// extern crate serde_json;
//
// use generated_module::verify_schema;
//
// fn main() {
//     let json = r#"{"answer": 42}"#;
//     let model: verify_schema = serde_json::from_str(&json).unwrap();
// }

use serde::{Serialize, Deserialize};

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct VerifySchema {
    algorithm: String,

    generator_version: String,

    header: Vec<String>,

    notes: Notes,

    number_of_tests: i64,

    schema: String,

    test_groups: Vec<TestGroup>,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct Notes {
    boundary_condition: BoundaryCondition,

    incorrect_public_key_length: BoundaryCondition,

    incorrect_signature_length: BoundaryCondition,

    invalid_hints_encoding: BoundaryCondition,

    invalid_private_key: BoundaryCondition,

    many_steps: BoundaryCondition,

    modified_signature: BoundaryCondition,

    valid_signature: BoundaryCondition,

    zero_public_key: BoundaryCondition,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BoundaryCondition {
    bug_type: String,

    description: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestGroup {
    #[serde(rename = "type")]
    test_group_type: Type,

    public_key: String,

    tests: Vec<Test>,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum Type {
    #[serde(rename = "MlDsaVerify")]
    MlDsaVerify,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test {
    tc_id: i64,

    comment: String,

    msg: String,

    #[serde(default)]
    ctx: String,

    sig: String,

    result: Result,

    flags: Vec<Flag>,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum Flag {
    #[serde(rename = "BoundaryCondition")]
    BoundaryCondition,

    #[serde(rename = "IncorrectPublicKeyLength")]
    IncorrectPublicKeyLength,

    #[serde(rename = "IncorrectSignatureLength")]
    IncorrectSignatureLength,

    #[serde(rename = "InvalidHintsEncoding")]
    InvalidHintsEncoding,

    #[serde(rename = "InvalidPrivateKey")]
    InvalidPrivateKey,

    #[serde(rename = "InvalidContext")]
    InvalidContext,
    
    #[serde(rename = "ManySteps")]
    ManySteps,

    #[serde(rename = "ModifiedSignature")]
    ModifiedSignature,

    #[serde(rename = "ValidSignature")]
    ValidSignature,

    #[serde(rename = "ZeroPublicKey")]
    ZeroPublicKey,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Result {
    Invalid,

    Valid,
}
