

use libcrux_ml_dsa::{
    ml_dsa_87::{self, MLDSA87KeyPair, MLDSA87Signature},
    KEY_GENERATION_RANDOMNESS_SIZE, SIGNING_RANDOMNESS_SIZE,
};


#[path = "./bench_utils.rs"]
#[macro_use]
mod bench_utils;

fn main() {
    bench_group!("87", ml_dsa_87, MLDSA87KeyPair, MLDSA87Signature);
}
