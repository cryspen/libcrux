use libcrux_hacl::{
    Hacl_Hash_SHA2_hash_224, Hacl_Hash_SHA2_hash_256, Hacl_Hash_SHA2_hash_384,
    Hacl_Hash_SHA2_hash_512,
};

/// SHA2 224
///
/// Note the function panics when `payload` is larger than 2^32 bytes.
pub fn sha224(payload: &[u8]) -> [u8; 28] {
    let mut digest = [0u8; 28];
    unsafe {
        Hacl_Hash_SHA2_hash_224(
            digest.as_mut_ptr(),
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
        );
    }
    digest
}

/// SHA2 256
///
/// Note the function panics when `payload` is larger than 2^32 bytes.
pub fn sha256(payload: &[u8]) -> [u8; 32] {
    let mut digest = [0u8; 32];
    unsafe {
        Hacl_Hash_SHA2_hash_256(
            digest.as_mut_ptr(),
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
        );
    }
    digest
}

/// SHA2 384
///
/// Note the function panics when `payload` is larger than 2^32 bytes.
pub fn sha384(payload: &[u8]) -> [u8; 48] {
    let mut digest = [0u8; 48];
    unsafe {
        Hacl_Hash_SHA2_hash_384(
            digest.as_mut_ptr(),
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
        );
    }
    digest
}

/// SHA2 512
///
/// Note the function panics when `payload` is larger than 2^32 bytes.
pub fn sha512(payload: &[u8]) -> [u8; 64] {
    let mut digest = [0u8; 64];
    unsafe {
        Hacl_Hash_SHA2_hash_512(
            digest.as_mut_ptr(),
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
        );
    }
    digest
}

pub mod streaming {
    use libcrux_hacl::{
        Hacl_Hash_SHA2_copy_256, Hacl_Hash_SHA2_copy_512, Hacl_Hash_SHA2_digest_224,
        Hacl_Hash_SHA2_digest_256, Hacl_Hash_SHA2_digest_384, Hacl_Hash_SHA2_digest_512,
        Hacl_Hash_SHA2_free_224, Hacl_Hash_SHA2_free_256, Hacl_Hash_SHA2_free_384,
        Hacl_Hash_SHA2_free_512, Hacl_Hash_SHA2_malloc_224, Hacl_Hash_SHA2_malloc_256,
        Hacl_Hash_SHA2_malloc_384, Hacl_Hash_SHA2_malloc_512, Hacl_Hash_SHA2_reset_224,
        Hacl_Hash_SHA2_reset_256, Hacl_Hash_SHA2_reset_384, Hacl_Hash_SHA2_reset_512,
        Hacl_Hash_SHA2_state_t_224, Hacl_Hash_SHA2_state_t_384, Hacl_Hash_SHA2_update_224,
        Hacl_Hash_SHA2_update_256, Hacl_Hash_SHA2_update_384, Hacl_Hash_SHA2_update_512,
    };

    macro_rules! impl_streaming {
        ($name:ident, $digest_size:literal, $state:ty, $malloc:expr, $reset:expr, $update:expr, $finish:expr, $free:expr, $copy:expr) => {
            pub struct $name {
                state: *mut $state,
            }

            impl $name {
                /// Initialize a new digest state.
                pub fn new() -> $name {
                    let state = $name {
                        state: unsafe { $malloc() },
                    };
                    unsafe { $reset(state.state) };
                    state
                }

                /// Add the `payload` to the digest.
                pub fn update(&mut self, payload: &[u8]) {
                    // Note that we don't really need mut here because the mutability is
                    // only in unsafe C code.
                    // But this way we force the borrow checker to do the right thing.
                    unsafe { $update(self.state, payload.as_ptr() as _, payload.len() as u32) };
                }

                /// Get the digest.
                ///
                /// Note that the digest state can be continued to be used, to extend the
                /// digest.
                pub fn finish(&mut self) -> [u8; $digest_size] {
                    // Note that we don't really need mut here because the mutability is
                    // only in unsafe C code.
                    // But this way we force the borrow checker to do the right thing.
                    let mut digest = [0u8; $digest_size];
                    unsafe {
                        $finish(self.state, digest.as_mut_ptr());
                    }
                    digest
                }
            }

            impl Drop for $name {
                fn drop(&mut self) {
                    unsafe { $free(self.state) };
                }
            }

            impl Clone for $name {
                fn clone(&self) -> Self {
                    unsafe {
                        Self {
                            state: $copy(self.state),
                        }
                    }
                }
            }

            unsafe impl Send for $name {}
        };
    }

    impl_streaming!(
        Sha224,
        28,
        Hacl_Hash_SHA2_state_t_224,
        Hacl_Hash_SHA2_malloc_224,
        Hacl_Hash_SHA2_reset_224,
        Hacl_Hash_SHA2_update_224,
        Hacl_Hash_SHA2_digest_224,
        Hacl_Hash_SHA2_free_224,
        Hacl_Hash_SHA2_copy_256
    );

    impl_streaming!(
        Sha256,
        32,
        Hacl_Hash_SHA2_state_t_224,
        Hacl_Hash_SHA2_malloc_256,
        Hacl_Hash_SHA2_reset_256,
        Hacl_Hash_SHA2_update_256,
        Hacl_Hash_SHA2_digest_256,
        Hacl_Hash_SHA2_free_256,
        Hacl_Hash_SHA2_copy_256
    );

    impl_streaming!(
        Sha384,
        48,
        Hacl_Hash_SHA2_state_t_384,
        Hacl_Hash_SHA2_malloc_384,
        Hacl_Hash_SHA2_reset_384,
        Hacl_Hash_SHA2_update_384,
        Hacl_Hash_SHA2_digest_384,
        Hacl_Hash_SHA2_free_384,
        Hacl_Hash_SHA2_copy_512
    );

    impl_streaming!(
        Sha512,
        64,
        Hacl_Hash_SHA2_state_t_384,
        Hacl_Hash_SHA2_malloc_512,
        Hacl_Hash_SHA2_reset_512,
        Hacl_Hash_SHA2_update_512,
        Hacl_Hash_SHA2_digest_512,
        Hacl_Hash_SHA2_free_512,
        Hacl_Hash_SHA2_copy_512
    );
}
