//! Helper to check for required CPU feattures.

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub(super) fn simd128_support() -> bool {
    std::arch::is_x86_feature_detected!("sse2")
        && std::arch::is_x86_feature_detected!("sse3")
        && std::arch::is_x86_feature_detected!("sse4.1")
        && std::arch::is_x86_feature_detected!("avx")
}

#[cfg(target_arch = "aarch64")]
pub(super) fn simd128_support() -> bool {
    true
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
pub(super) fn simd128_support() -> bool {
    // XXX: Check for z14 or z15
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub(super) fn simd256_support() -> bool {
    simd128_support() && std::arch::is_x86_feature_detected!("avx2")
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub(super) fn simd256_support() -> bool {
    // XXX: Check for z14 or z15
    false
}
