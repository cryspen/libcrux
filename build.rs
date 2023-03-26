#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn simd128_support() -> bool {
    std::arch::is_x86_feature_detected!("sse2")
        && std::arch::is_x86_feature_detected!("sse3")
        && std::arch::is_x86_feature_detected!("sse4.1")
        && std::arch::is_x86_feature_detected!("avx")
}

#[cfg(target_arch = "aarch64")]
fn simd128_support() -> bool {
    true
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
fn simd128_support() -> bool {
    // XXX: Check for z14 or z15
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn simd256_support() -> bool {
    std::arch::is_x86_feature_detected!("avx2")
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn simd256_support() -> bool {
    // XXX: Check for z14 or z15
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn bmi2_adx_support() -> bool {
    std::arch::is_x86_feature_detected!("bmi2") && std::arch::is_x86_feature_detected!("adx")
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn bmi2_adx_support() -> bool {
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn aes_ni_support() -> bool {
    // FIXME: std::arch::is_x86_feature_detected!("movbe") is not supported yet
    //        we assume here that it is supported :|
    std::arch::is_x86_feature_detected!("avx")
        && std::arch::is_x86_feature_detected!("sse")
        && std::arch::is_x86_feature_detected!("aes")
        && std::arch::is_x86_feature_detected!("pclmulqdq")
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn aes_ni_support() -> bool {
    false
}

fn main() {
    if simd128_support() {
        println!("cargo:rustc-cfg=simd128");
    }
    if simd256_support() {
        println!("cargo:rustc-cfg=simd256");
    }
    if bmi2_adx_support() {
        println!("cargo:rustc-cfg=bmi2");
        println!("cargo:rustc-cfg=adx");
    }
    if aes_ni_support() {
        println!("cargo:rustc-cfg=aes_ni");
    }
}
