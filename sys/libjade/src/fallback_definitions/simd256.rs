pub unsafe fn jade_hash_sha3_224_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support compiled. Use --cfg simd256 to enable it.")
}

pub unsafe fn jade_hash_sha3_256_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support compiled. Use --cfg simd256 to enable it.")
}

pub unsafe fn jade_hash_sha3_384_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support compiled. Use --cfg simd256 to enable it.")
}

pub unsafe fn jade_hash_sha3_512_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support compiled. Use --cfg simd256 to enable it.")
}

pub unsafe fn jade_stream_chacha_chacha20_ietf_amd64_avx2_xor(
    _: *mut u8,
    _: *mut u8,
    _: u64,
    _: *mut u8,
    _: *mut u8,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support compiled. Use --cfg simd256 to enable it.")
}

pub unsafe fn jade_stream_chacha_chacha20_ietf_amd64_avx2(
    _: *mut u8,
    _: u64,
    _: *mut u8,
    _: *mut u8,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support compiled. Use --cfg simd256 to enable it.")
}

pub unsafe fn jade_onetimeauth_poly1305_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
    _: *mut u8,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support compiled. Use --cfg simd256 to enable it.")
}
pub unsafe fn jade_onetimeauth_poly1305_amd64_avx2_verify(
    _: *mut u8,
    _: *mut u8,
    _: u64,
    _: *mut u8,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support compiled. Use --cfg simd256 to enable it.")
}
