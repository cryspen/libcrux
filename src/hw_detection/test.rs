use super::*;

#[test]
fn dump_features() {
    eprintln!("simd128\t\t{:?}", simd128_support());
    eprintln!("simd256\t\t{:?}", simd256_support());
    eprintln!("x25519\t\t{:?}", x25519_cpu_support());
    eprintln!("bmi2 & adx\t{:?}", bmi2_adx_support());
    eprintln!("aes\t\t{:?}", aes_ni_support());
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[test]
fn dump_raw() {
    use super::cpuid::{supported, CpuId, Feature};
    let id = CpuId::init();
    eprintln!("mmx\t\t{:?}", supported(Feature::mmx, &id));
    eprintln!("sse\t\t{:?}", supported(Feature::sse, &id));
    eprintln!("sse2\t\t{:?}", supported(Feature::sse2, &id));
    eprintln!("sse3\t\t{:?}", supported(Feature::sse3, &id));
    eprintln!("pclmulqdq\t{:?}", supported(Feature::pclmulqdq, &id));
    eprintln!("ssse3\t\t{:?}", supported(Feature::ssse3, &id));
    eprintln!("fma\t\t{:?}", supported(Feature::fma, &id));
    eprintln!("movbe\t\t{:?}", supported(Feature::movbe, &id));
    eprintln!("sse4_1\t\t{:?}", supported(Feature::sse4_1, &id));
    eprintln!("sse4_2\t\t{:?}", supported(Feature::sse4_2, &id));
    eprintln!("popcnt\t\t{:?}", supported(Feature::popcnt, &id));
    eprintln!("aes\t\t{:?}", supported(Feature::aes, &id));
    eprintln!("xsave\t\t{:?}", supported(Feature::xsave, &id));
    eprintln!("osxsave\t\t{:?}", supported(Feature::osxsave, &id));
    eprintln!("avx\t\t{:?}", supported(Feature::avx, &id));
    eprintln!("rdrand\t\t{:?}", supported(Feature::rdrand, &id));
    eprintln!("sgx\t\t{:?}", supported(Feature::sgx, &id));
    eprintln!("bmi1\t\t{:?}", supported(Feature::bmi1, &id));
    eprintln!("avx2\t\t{:?}", supported(Feature::avx2, &id));
    eprintln!("bmi2\t\t{:?}", supported(Feature::bmi2, &id));
    eprintln!("avx512f\t\t{:?}", supported(Feature::avx512f, &id));
    eprintln!("avx512dq\t{:?}", supported(Feature::avx512dq, &id));
    eprintln!("rdseed\t\t{:?}", supported(Feature::rdseed, &id));
    eprintln!("adx\t\t{:?}", supported(Feature::adx, &id));
    eprintln!("avx512ifma\t{:?}", supported(Feature::avx512ifma, &id));
    eprintln!("avx512pf\t{:?}", supported(Feature::avx512pf, &id));
    eprintln!("avx512er\t{:?}", supported(Feature::avx512er, &id));
    eprintln!("avx512cd\t{:?}", supported(Feature::avx512cd, &id));
    eprintln!("sha\t\t{:?}", supported(Feature::sha, &id));
    eprintln!("avx512bw\t{:?}", supported(Feature::avx512bw, &id));
    eprintln!("avx512vl\t{:?}", supported(Feature::avx512vl, &id));
}
