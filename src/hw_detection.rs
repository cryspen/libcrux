//! Helper to check for required CPU feattures.
#![allow(unused)]

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod cpuid;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use cpuid::{self as cpu_id, Feature};

#[cfg(test)]
mod test;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub(super) fn simd128_support() -> bool {
    cpu_id::supported(Feature::sse2)
        && cpu_id::supported(Feature::sse3)
        && cpu_id::supported(Feature::sse4_1)
        && cpu_id::supported(Feature::avx)
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
    cpu_id::supported(Feature::avx2)
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub(super) fn simd256_support() -> bool {
    // XXX: Check for z14 or z15
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub(super) fn x25519_cpu_support() -> bool {
    cpu_id::supported(Feature::bmi2) && cpu_id::supported(Feature::adx)
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
#[allow(unused)]
pub(super) fn x25519_cpu_support() -> bool {
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub(super) fn bmi2_adx_support() -> bool {
    cpu_id::supported(Feature::bmi2) && cpu_id::supported(Feature::adx)
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub(super) fn bmi2_adx_support() -> bool {
    false
}

/// Check whether AES is supported
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn aes_ni_support() -> bool {
    cpu_id::supported(Feature::avx)
        && cpu_id::supported(Feature::sse)
        && cpu_id::supported(Feature::aes)
        && cpu_id::supported(Feature::pclmulqdq)
        && cpu_id::supported(Feature::movbe)
}

/// Check whether AES is supported
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub fn aes_ni_support() -> bool {
    false
}
