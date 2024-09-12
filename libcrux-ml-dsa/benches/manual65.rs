use libcrux_ml_dsa::{
    ml_dsa_65::{self, MLDSA65KeyPair, MLDSA65Signature},
    KEY_GENERATION_RANDOMNESS_SIZE, SIGNING_RANDOMNESS_SIZE,
};

use pqcrypto_dilithium;

mod bench_utils;

fn main() {
    bench_group_libcrux!(
        "65 portable",
        ml_dsa_65::portable,
        MLDSA65KeyPair,
        MLDSA65Signature
    );
    #[cfg(feature = "simd128")]
    bench_group_libcrux!(
        "65 sim1d28",
        ml_dsa_65::neon,
        MLDSA65KeyPair,
        MLDSA65Signature
    );
    #[cfg(feature = "simd256")]
    bench_group_libcrux!(
        "65 simd256",
        ml_dsa_65::avx2,
        MLDSA65KeyPair,
        MLDSA65Signature
    );
    bench_group_pqclean!("65", dilithium3);
}
