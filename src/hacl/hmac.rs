use libcrux_hacl::{
    Hacl_HMAC_compute_sha1, Hacl_HMAC_compute_sha2_256, Hacl_HMAC_compute_sha2_384,
    Hacl_HMAC_compute_sha2_512,
};

macro_rules! impl_hmac {
    ($name:ident,$fun:expr,$tag_len:literal) => {
        /// Compute HMAC.
        ///
        /// Note that this function panics if `key` or `data` is larger than 2**32 bytes.
        pub fn $name(key: &[u8], data: &[u8]) -> [u8; $tag_len] {
            let mut dst = [0u8; $tag_len];
            unsafe {
                $fun(
                    dst.as_mut_ptr(),
                    key.as_ptr() as _,
                    key.len().try_into().unwrap(),
                    data.as_ptr() as _,
                    data.len().try_into().unwrap(),
                )
            }
            dst
        }
    };
}

impl_hmac!(sha1, Hacl_HMAC_compute_sha1, 20);
impl_hmac!(sha2_256, Hacl_HMAC_compute_sha2_256, 32);
impl_hmac!(sha2_384, Hacl_HMAC_compute_sha2_384, 48);
impl_hmac!(sha2_512, Hacl_HMAC_compute_sha2_512, 64);
