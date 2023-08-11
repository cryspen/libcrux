#![no_std]

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use x86::{self as cpu_id, Feature};

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod macos_arm;
#[cfg(all(target_arch = "aarch64", target_os = "linux"))]
mod macos_linux;

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
pub fn x25519_support() -> bool {
    cpu_id::supported(Feature::bmi2) && cpu_id::supported(Feature::adx)
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
#[allow(unused)]
pub fn x25519_support() -> bool {
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

/// Check whether p(cl)mull is supported
pub fn pmull_support() -> bool {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    {
        use crate::macos_arm::*;
        pmull()
    }

    #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
    false
}

/// Check whether advanced SIMD features are supported
pub fn adv_simd_support() -> bool {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    {
        use macos_arm::*;
        adv_simd()
    }

    #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
    false
}

/// Check whether AES is supported
pub fn aes_ni_support() -> bool {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    {
        use crate::macos_arm::*;
        aes()
    }

    #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
    false
}

/// Check whether SHA256 is supported
pub fn sha256_support() -> bool {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    {
        use crate::macos_arm::*;
        sha256()
    }

    #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86 {
    /// Check whether p(cl)mull is supported
    pub fn pmull_support() -> bool {
        cpu_id::supported(Feature::pclmulqdq)
    }

    /// Check whether advanced SIMD features are supported
    pub fn adv_simd_support() -> bool {
        false
    }

    /// Check whether AES is supported
    pub fn aes_ni_support() -> bool {
        cpu_id::supported(Feature::avx)
            && cpu_id::supported(Feature::sse)
            && cpu_id::supported(Feature::aes)
            && cpu_id::supported(Feature::pclmulqdq)
            && cpu_id::supported(Feature::movbe)
    }
}
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use x86::*;

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    all(
        target_arch = "aarch64",
        not(any(target_os = "macos", target_os = "linux"))
    )
)))]
mod other {
    /// Check whether p(cl)mull is supported
    pub fn pmull_support() -> bool {
        false
    }

    /// Check whether advanced SIMD features are supported
    pub fn adv_simd_support() -> bool {
        false
    }

    /// Check whether AES is supported
    pub fn aes_ni_support() -> bool {
        false
    }
}
#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    all(
        target_arch = "aarch64",
        not(any(target_os = "macos", target_os = "linux"))
    )
)))]
pub use other::*;
