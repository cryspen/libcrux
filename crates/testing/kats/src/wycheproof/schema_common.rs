//! Structs based on
//! [`schemas/common.json`](https://github.com/C2SP/wycheproof/blob/cd136e97040de0842c3a198670b1c5e4f423c940/schemas/common.json)

use serde::{Deserialize, Serialize};

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Source {
    pub name: String,
    pub version: String,
}

#[derive(PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NotesEntry {
    /// The type of the bug tested for
    pub bug_type: String,

    /// A description of the flag
    pub description: Option<String>,

    /// The expected effect of failing the test vector
    pub effect: Option<String>,

    /// A list of potentially related references
    #[serde(default)]
    pub links: Vec<String>,

    /// A list of potentially related CVEs
    #[serde(default)]
    pub cves: Vec<String>,
}
