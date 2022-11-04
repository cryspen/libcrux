use libcrux_hacl::{
    Hacl_Curve25519_51_ecdh, Hacl_Curve25519_51_secret_to_public, Hacl_Curve25519_64_ecdh,
};

use super::hw_detection::{self, x25519_cpu_support};

pub fn derive(p: &[u8], s: &[u8]) -> Result<[u8; 32], &'static str> {
    let mut result = [0u8; 32];
    let r = if x25519_cpu_support() {
        unsafe { Hacl_Curve25519_64_ecdh(result.as_mut_ptr(), s.as_ptr() as _, p.as_ptr() as _) }
    } else {
        unsafe { Hacl_Curve25519_51_ecdh(result.as_mut_ptr(), s.as_ptr() as _, p.as_ptr() as _) }
    };
    if !r {
        Err("Error deriving x25519")
    } else {
        Ok(result)
    }
}

pub fn derive_base(s: &[u8]) -> [u8; 32] {
    let mut result = [0u8; 32];
    unsafe { Hacl_Curve25519_51_secret_to_public(result.as_mut_ptr(), s.as_ptr() as _) }
    result
}
