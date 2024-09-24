use libcrux_ml_dsa::{
    ml_dsa_44::{self, MLDSA44KeyPair, MLDSA44Signature},
    KEY_GENERATION_RANDOMNESS_SIZE, SIGNING_RANDOMNESS_SIZE,
};

use pqcrypto_dilithium;

mod bench_utils;

fn main() {
    bench_group_libcrux!(
        "44 portable",
        ml_dsa_44::portable,
        MLDSA44KeyPair,
        MLDSA44Signature
    );
    #[cfg(feature = "simd128")]
    bench_group_libcrux!(
        "44 sim1d28",
        ml_dsa_44::neon,
        MLDSA44KeyPair,
        MLDSA44Signature
    );
    #[cfg(feature = "simd256")]
    bench_group_libcrux!(
        "44 simd256",
        ml_dsa_44::avx2,
        MLDSA44KeyPair,
        MLDSA44Signature
    );
    bench_group_pqclean!("44", dilithium2);
}
