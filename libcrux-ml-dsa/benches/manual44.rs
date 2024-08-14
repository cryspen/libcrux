use libcrux_ml_dsa::{
    ml_dsa_44::{self, MLDSA44KeyPair, MLDSA44Signature},
    KEY_GENERATION_RANDOMNESS_SIZE, SIGNING_RANDOMNESS_SIZE,
};

use pqcrypto_dilithium;

#[path = "./bench_utils.rs"]
#[macro_use]
mod bench_utils;

fn main() {
    bench_group_libcrux!("44", ml_dsa_44, MLDSA44KeyPair, MLDSA44Signature);
    bench_group_pqclean!("44", dilithium2);
}
