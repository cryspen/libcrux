#[cfg(not(simd256))]
pub unsafe fn jade_hash_sha3_224_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support comiled. Use --cfg simd256 to enable it.")
}

#[cfg(not(simd256))]
pub unsafe fn jade_hash_sha3_256_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support comiled. Use --cfg simd256 to enable it.")
}

#[cfg(not(simd256))]
pub unsafe fn jade_hash_sha3_384_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support comiled. Use --cfg simd256 to enable it.")
}

#[cfg(not(simd256))]
pub unsafe fn jade_hash_sha3_512_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support comiled. Use --cfg simd256 to enable it.")
}
