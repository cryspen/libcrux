use core::arch::x86_64::*;

#[allow(dead_code)]
fn print_m256i_as_i16s(a: __m256i, prefix: &'static str) {
    let mut a_bytes = [0i16; 16];
    unsafe { _mm256_store_si256(a_bytes.as_mut_ptr() as *mut __m256i, a) };
    println!("{}: {:04x?}", prefix, a_bytes);
}
#[allow(dead_code)]
fn print_m128i_as_i16s(a: __m128i, prefix: &'static str) {
    let mut a_bytes = [0i16; 8];
    unsafe { _mm_store_si128(a_bytes.as_mut_ptr() as *mut __m128i, a) };
    println!("{}: {:?}", prefix, a_bytes);
}
#[allow(dead_code)]
fn print_m128i_as_i8s(a: __m128i, prefix: &'static str) {
    let mut a_bytes = [0i8; 16];
    unsafe { _mm_store_si128(a_bytes.as_mut_ptr() as *mut __m128i, a) };
    println!("{}: {:?}", prefix, a_bytes);
}
