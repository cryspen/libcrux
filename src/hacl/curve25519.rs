use libcrux_hacl::*;

use libcrux_platform::x25519_support;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn fast_x25519(result: &mut [u8], private: &[u8], public: &[u8]) -> bool {
    unsafe {
        Hacl_Curve25519_64_ecdh(
            result.as_mut_ptr(),
            private.as_ptr() as _,
            public.as_ptr() as _,
        )
    }
}
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn fast_x25519(_: &mut [u8], _: &[u8], _: &[u8]) -> bool {
    false
}

pub fn derive(p: &[u8], s: &[u8]) -> Result<[u8; 32], &'static str> {
    let mut result = [0u8; 32];
    let r = if x25519_support() {
        log::trace!("HACL x25519 mulx");
        fast_x25519(&mut result, s, p)
    } else {
        log::trace!("HACL x25519 ref");
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
