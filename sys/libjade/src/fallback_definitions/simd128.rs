pub fn jade_onetimeauth_poly1305_amd64_avx(
    _: *mut u8,
    _: *mut u8,
    _: u64,
    _: *mut u8,
) -> ::std::os::raw::c_int {
    panic!("No AVX support compiled. Use --cfg simd128 to enable it.")
}
pub fn jade_onetimeauth_poly1305_amd64_avx_verify(
    _: *mut u8,
    _: *mut u8,
    _: u64,
    _: *mut u8,
) -> ::std::os::raw::c_int {
    panic!("No AVX support compiled. Use --cfg simd128 to enable it.")
}
pub fn jade_stream_chacha_chacha20_ietf_amd64_avx_xor(
    _: *mut u8,
    _: *mut u8,
    _: u64,
    _: *mut u8,
    _: *mut u8,
) -> ::std::os::raw::c_int {
    panic!("No AVX support compiled. Use --cfg simd128 to enable it.")
}
pub fn jade_stream_chacha_chacha20_ietf_amd64_avx(
    _: *mut u8,
    _: u64,
    _: *mut u8,
    _: *mut u8,
) -> ::std::os::raw::c_int {
    panic!("No AVX support compiled. Use --cfg simd128 to enable it.")
}
