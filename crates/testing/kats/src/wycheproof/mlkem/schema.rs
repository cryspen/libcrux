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
pub struct MlkemSchema {
    algorithm: String,

    schema: String,

    number_of_tests: i64,

    notes: Notes,

    test_groups: Vec<TestGroup>,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct Notes {
    strcmp: ModulusOverflow,

    modulus_overflow: ModulusOverflow,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModulusOverflow {
    bug_type: String,

    description: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestGroup {
    #[serde(rename = "type")]
    test_group_type: String,

    source: Source,

    parameter_set: String,

    tests: Vec<Test>,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub struct Source {
    name: String,

    version: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test {
    tc_id: i64,

    flags: Vec<Flag>,

    seed: Option<String>,

    ek: String,

    c: String,

    #[serde(rename = "K")]
    k: K,

    result: Result,

    m: Option<String>,
}

#[derive(PartialEq, Serialize, Deserialize)]
pub enum Flag {
    #[serde(rename = "ModulusOverflow")]
    ModulusOverflow,

    Strcmp,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum K {
    C6338Bf92F3930B95F81D87Fe669Fabc42Aaa549E8Fecfbfdbe237D739Fe4D96,

    Cf3Bcfeb2679Cb43658Fcdcd01Aa1505Bcea1E72A165Ccac7Bfb66D9Dc0C0E90,

    #[serde(rename = "")]
    Empty,

    #[serde(rename = "76c10bb1d86d96d7eb18e298363e51f7728e113f455df7d15017940ed3541451")]
    The76C10Bb1D86D96D7Eb18E298363E51F7728E113F455Df7D15017940Ed3541451,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Result {
    Invalid,

    Valid,
}
