//! High-level functions to detect available CPU features
//! at runtime on supported processor architectures and
//! operation systems

#![no_std]

// Use std for tests
#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use x86::{self as cpu_id, Feature};

#[cfg(all(target_arch = "aarch64", target_os = "linux"))]
mod linux_arm;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod macos_arm;

#[cfg(test)]
mod test;

pub use platform::*;

#[cfg(hax)]
mod platform {
    pub fn simd128_support() -> bool {
        false
    }
    pub fn simd256_support() -> bool {
        false
    }
    pub fn x25519_support() -> bool {
        false
    }
    pub fn bmi2_adx_support() -> bool {
        false
    }
    pub fn pmull_support() -> bool {
        false
    }
    pub fn adv_simd_support() -> bool {
        false
    }
    pub fn aes_ni_support() -> bool {
        false
    }
    pub fn sha256_support() -> bool {
        false
    }
}

#[cfg(not(hax))]
mod platform {
    use super::*;

    // TODO: Check for z14 or z15
    pub fn simd128_support() -> bool {
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        {
            use macos_arm::*;
            adv_simd()
        }

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            cpu_id::supported(Feature::sse2)
                && cpu_id::supported(Feature::sse3)
                && cpu_id::supported(Feature::sse4_1)
                && cpu_id::supported(Feature::avx)
        }

        #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
        {
            use linux_arm::*;
            adv_simd()
        }

        #[cfg(not(any(
            all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")),
            target_arch = "x86",
            target_arch = "x86_64"
        )))]
        {
            false
        }
    }

    pub fn simd256_support() -> bool {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        return cpu_id::supported(Feature::avx2);

        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
        false
    }

    pub fn x25519_support() -> bool {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        return cpu_id::supported(Feature::bmi2) && cpu_id::supported(Feature::adx);

        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
        false
    }

    pub fn bmi2_adx_support() -> bool {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        return cpu_id::supported(Feature::bmi2) && cpu_id::supported(Feature::adx);

        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
        false
    }

    /// Check whether p(cl)mull is supported
    pub fn pmull_support() -> bool {
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        {
            use crate::macos_arm::*;
            pmull()
        }

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            cpu_id::supported(Feature::pclmulqdq)
        }

        #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
        {
            use crate::linux_arm::*;
            pmull()
        }

        #[cfg(not(any(
            all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")),
            target_arch = "x86",
            target_arch = "x86_64"
        )))]
        {
            false
        }
    }

    /// Check whether advanced SIMD features are supported
    pub fn adv_simd_support() -> bool {
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        {
            use macos_arm::*;
            adv_simd()
        }

        #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
        {
            use linux_arm::*;
            adv_simd()
        }

        #[cfg(not(all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos"))))]
        {
            false
        }
    }

    /// Check whether AES is supported
    pub fn aes_ni_support() -> bool {
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        {
            use crate::macos_arm::*;
            aes()
        }

        #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
        {
            use crate::linux_arm::*;
            aes()
        }

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            cpu_id::supported(Feature::avx)
                && cpu_id::supported(Feature::sse)
                && cpu_id::supported(Feature::aes)
                && cpu_id::supported(Feature::pclmulqdq)
                && cpu_id::supported(Feature::movbe)
        }

        #[cfg(not(any(
            all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")),
            target_arch = "x86",
            target_arch = "x86_64"
        )))]
        {
            false
        }
    }

    /// Check whether SHA256 is supported
    pub fn sha256_support() -> bool {
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        {
            use crate::macos_arm::*;
            sha256()
        }

        #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
        {
            use crate::linux_arm::*;
            sha256()
        }

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            cpu_id::supported(Feature::sha)
        }

        #[cfg(not(any(
            all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")),
            target_arch = "x86",
            target_arch = "x86_64"
        )))]
        {
            false
        }
    }
}
