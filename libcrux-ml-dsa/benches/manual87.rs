use libcrux_ml_dsa::{
    ml_dsa_87::{self, MLDSA87KeyPair, MLDSA87Signature},
    KEY_GENERATION_RANDOMNESS_SIZE, SIGNING_RANDOMNESS_SIZE,
};

use pqcrypto_dilithium;

mod bench_utils;

fn main() {
    bench_group_libcrux!(
        "87 portable",
        ml_dsa_87::portable,
        MLDSA87KeyPair,
        MLDSA87Signature
    );
    #[cfg(feature = "simd128")]
    bench_group_libcrux!(
        "87 sim1d28",
        ml_dsa_87::neon,
        MLDSA87KeyPair,
        MLDSA87Signature
    );
    #[cfg(feature = "simd256")]
    bench_group_libcrux!(
        "87 simd256",
        ml_dsa_87::avx2,
        MLDSA87KeyPair,
        MLDSA87Signature
    );
    bench_group_pqclean!("87", dilithium5);
}
