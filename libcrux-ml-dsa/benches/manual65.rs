

use libcrux_ml_dsa::{
    ml_dsa_65::{self, MLDSA65KeyPair, MLDSA65Signature},
    KEY_GENERATION_RANDOMNESS_SIZE, SIGNING_RANDOMNESS_SIZE,
};


#[path = "./bench_utils.rs"]
#[macro_use]
mod bench_utils;

fn main() {
    bench_group!("65", ml_dsa_65, MLDSA65KeyPair, MLDSA65Signature);
}
