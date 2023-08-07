#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use x86::{self as cpu_id, Feature};

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod macos_arm;

#[cfg(test)]
mod test;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn simd128_support() -> bool {
    cpu_id::supported(Feature::sse2)
        && cpu_id::supported(Feature::sse3)
        && cpu_id::supported(Feature::sse4_1)
        && cpu_id::supported(Feature::avx)
}

#[cfg(target_arch = "aarch64")]
pub fn simd128_support() -> bool {
    true
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
pub fn simd128_support() -> bool {
    // XXX: Check for z14 or z15
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn simd256_support() -> bool {
    cpu_id::supported(Feature::avx2)
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub fn simd256_support() -> bool {
    // XXX: Check for z14 or z15
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn x25519_cpu_support() -> bool {
    cpu_id::supported(Feature::bmi2) && cpu_id::supported(Feature::adx)
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
#[allow(unused)]
pub fn x25519_cpu_support() -> bool {
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn bmi2_adx_support() -> bool {
    cpu_id::supported(Feature::bmi2) && cpu_id::supported(Feature::adx)
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub fn bmi2_adx_support() -> bool {
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
#[cfg(target_arch = "aarch64")]
pub fn aes_ni_support() -> bool {
    use macos_arm::aes;

    aes()
}

/// Check whether AES is supported
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
pub fn aes_ni_support() -> bool {
    false
}
