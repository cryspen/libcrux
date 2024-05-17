//! Test functions for CPU feature detection

use super::*;

#[test]
fn dump_features() {
    eprintln!("simd128\t\t{:?}", simd128_support());
    eprintln!("simd256\t\t{:?}", simd256_support());
    eprintln!("x25519\t\t{:?}", x25519_support());
    eprintln!("bmi2 & adx\t{:?}", bmi2_adx_support());
    eprintln!("aes\t\t{:?}", aes_ni_support());
    eprintln!("advSimd\t\t{:?}", adv_simd_support());
    eprintln!("pmull\t\t{:?}", pmull_support());
    eprintln!("sha256\t\t{:?}", sha256_support());
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[test]
fn dump_raw() {
    use super::x86::{supported, Feature};
    eprintln!("mmx\t\t{:?}", supported(Feature::mmx));
    eprintln!("sse\t\t{:?}", supported(Feature::sse));
    eprintln!("sse2\t\t{:?}", supported(Feature::sse2));
    eprintln!("sse3\t\t{:?}", supported(Feature::sse3));
    eprintln!("pclmulqdq\t{:?}", supported(Feature::pclmulqdq));
    eprintln!("ssse3\t\t{:?}", supported(Feature::ssse3));
    eprintln!("fma\t\t{:?}", supported(Feature::fma));
    eprintln!("movbe\t\t{:?}", supported(Feature::movbe));
    eprintln!("sse4_1\t\t{:?}", supported(Feature::sse4_1));
    eprintln!("sse4_2\t\t{:?}", supported(Feature::sse4_2));
    eprintln!("popcnt\t\t{:?}", supported(Feature::popcnt));
    eprintln!("aes\t\t{:?}", supported(Feature::aes));
    eprintln!("xsave\t\t{:?}", supported(Feature::xsave));
    eprintln!("osxsave\t\t{:?}", supported(Feature::osxsave));
    eprintln!("avx\t\t{:?}", supported(Feature::avx));
    eprintln!("rdrand\t\t{:?}", supported(Feature::rdrand));
    eprintln!("sgx\t\t{:?}", supported(Feature::sgx));
    eprintln!("bmi1\t\t{:?}", supported(Feature::bmi1));
    eprintln!("avx2\t\t{:?}", supported(Feature::avx2));
    eprintln!("bmi2\t\t{:?}", supported(Feature::bmi2));
    eprintln!("avx512f\t\t{:?}", supported(Feature::avx512f));
    eprintln!("avx512dq\t{:?}", supported(Feature::avx512dq));
    eprintln!("rdseed\t\t{:?}", supported(Feature::rdseed));
    eprintln!("adx\t\t{:?}", supported(Feature::adx));
    eprintln!("avx512ifma\t{:?}", supported(Feature::avx512ifma));
    eprintln!("avx512pf\t{:?}", supported(Feature::avx512pf));
    eprintln!("avx512er\t{:?}", supported(Feature::avx512er));
    eprintln!("avx512cd\t{:?}", supported(Feature::avx512cd));
    eprintln!("sha\t\t{:?}", supported(Feature::sha));
    eprintln!("avx512bw\t{:?}", supported(Feature::avx512bw));
    eprintln!("avx512vl\t{:?}", supported(Feature::avx512vl));
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[test]
fn cpuid() {
    use super::x86::supported;
    use std::time::Instant;

    let now = Instant::now();
    let _avx2 = supported(Feature::avx2);
    let elapsed = now.elapsed();
    eprintln!("libcrux init: {elapsed:.2?}");

    let now = Instant::now();
    let _avx2 = supported(Feature::avx2);
    let elapsed = now.elapsed();
    eprintln!("libcrux after: {elapsed:.2?}");

    let now = Instant::now();
    let _avx2 = std::arch::is_x86_feature_detected!("avx2");
    let elapsed = now.elapsed();
    eprintln!("std init: {elapsed:.2?}");

    let now = Instant::now();
    let _avx2 = std::arch::is_x86_feature_detected!("avx2");
    let elapsed = now.elapsed();
    eprintln!("std after: {elapsed:.2?}");
}
