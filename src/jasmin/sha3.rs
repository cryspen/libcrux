use crate::digest::{
    digest_size,
    Algorithm::{Sha3_224, Sha3_256, Sha3_384, Sha3_512},
};

#[cfg(simd256)]
macro_rules! sha3_simd256 {
    ($name:ident, $alg:expr, $avx2_fun:expr, $ref_fun:expr) => {
        pub fn $name(input: &[u8]) -> [u8; digest_size($alg)] {
            let mut digest = [0u8; digest_size($alg)];
            let r = if libcrux_platform::simd256_support() {
                unsafe {
                    $avx2_fun(
                        digest.as_mut_ptr(),
                        input.as_ptr() as _,
                        input.len().try_into().unwrap(),
                    )
                }
            } else {
                unsafe {
                    $ref_fun(
                        digest.as_mut_ptr(),
                        input.as_ptr() as _,
                        input.len().try_into().unwrap(),
                    )
                }
            };
            if r != 0 {
                [0u8; digest_size($alg)]
            } else {
                digest
            }
        }
    };
}

#[cfg(simd256)]
sha3_simd256!(
    sha3_224,
    Sha3_224,
    libjade_sys::jade_hash_sha3_224_amd64_avx2,
    libjade_sys::jade_hash_sha3_224_amd64_ref
);

#[cfg(simd256)]
sha3_simd256!(
    sha3_256,
    Sha3_256,
    libjade_sys::jade_hash_sha3_256_amd64_avx2,
    libjade_sys::jade_hash_sha3_256_amd64_ref
);

#[cfg(simd256)]
sha3_simd256!(
    sha3_384,
    Sha3_384,
    libjade_sys::jade_hash_sha3_384_amd64_avx2,
    libjade_sys::jade_hash_sha3_384_amd64_ref
);

#[cfg(simd256)]
sha3_simd256!(
    sha3_512,
    Sha3_512,
    libjade_sys::jade_hash_sha3_512_amd64_avx2,
    libjade_sys::jade_hash_sha3_512_amd64_ref
);

#[cfg(not(simd256))]
macro_rules! sha3_ref {
    ($name:ident, $alg:expr, $ref_fun:expr) => {
        pub fn $name(input: &[u8]) -> [u8; digest_size($alg)] {
            let mut digest = [0u8; digest_size($alg)];
            let r = unsafe {
                $ref_fun(
                    digest.as_mut_ptr(),
                    input.as_ptr() as _,
                    input.len().try_into().unwrap(),
                )
            };
            if r != 0 {
                [0u8; digest_size($alg)]
            } else {
                digest
            }
        }
    };
}

#[cfg(not(simd256))]
sha3_ref!(
    sha3_224,
    Sha3_224,
    libjade_sys::jade_hash_sha3_224_amd64_ref
);

#[cfg(not(simd256))]
sha3_ref!(
    sha3_256,
    Sha3_256,
    libjade_sys::jade_hash_sha3_256_amd64_ref
);

#[cfg(not(simd256))]
sha3_ref!(
    sha3_384,
    Sha3_384,
    libjade_sys::jade_hash_sha3_384_amd64_ref
);

#[cfg(not(simd256))]
sha3_ref!(
    sha3_512,
    Sha3_512,
    libjade_sys::jade_hash_sha3_512_amd64_ref
);
