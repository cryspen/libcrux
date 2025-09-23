// Example code that deserializes and serializes the model.
// extern crate serde;
// #[macro_use]
// extern crate serde_derive;
// extern crate serde_json;
//
// use generated_module::mlkem_schema;
//
// fn main() {
//     let json = r#"{"answer": 42}"#;
//     let model: mlkem_schema = serde_json::from_str(&json).unwrap();
// }

use serde::{Deserialize, Serialize};

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MlkemTest {
    pub algorithm: String,

    pub schema: String,

    pub number_of_tests: i64,

    pub notes: Notes,

    pub test_groups: Vec<TestGroup>,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct Notes {
    pub strcmp: ModulusOverflow,

    pub modulus_overflow: ModulusOverflow,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModulusOverflow {
    pub bug_type: String,

    pub description: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum TestGroupType {
    MLKEMTest,
    MLKEMEncapsTest,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum MlKemParameterSet {
    #[serde(rename = "ML-KEM-512")]
    MlKem512,
    #[serde(rename = "ML-KEM-768")]
    MlKem768,
    #[serde(rename = "ML-KEM-1024")]
    MlKem1024,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestGroup {
    #[serde(rename = "type")]
    pub test_group_type: TestGroupType,

    pub source: Source,

    pub parameter_set: MlKemParameterSet,

    pub tests: Vec<Test>,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub struct Source {
    pub name: String,

    pub version: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test {
    pub tc_id: i64,

    pub flags: Vec<Flag>,

    pub seed: Option<String>,

    pub ek: String,

    pub c: String,

    #[serde(rename = "K")]
    #[serde(with = "hex::serde")]
    pub k: Vec<u8>,

    pub result: MlkemResult,

    pub m: Option<String>,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum Flag {
    #[serde(rename = "ModulusOverflow")]
    ModulusOverflow,

    Strcmp,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MlkemResult {
    Invalid,

    Valid,
}
