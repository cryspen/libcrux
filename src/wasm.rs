//! # WASM API

use wasm_bindgen::prelude::*;

// #[wasm_bindgen]
// extern "C" {
//     pub fn sha256(s: &str) -> String;
// }

#[wasm_bindgen]
pub fn sha256(s: &[u8]) -> Vec<u8> {
    crate::digest::sha2_256(s).to_vec()
}
