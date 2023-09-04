use libcrux_hacl::{
    Hacl_Streaming_SHA2_hash_224, Hacl_Streaming_SHA2_hash_256, Hacl_Streaming_SHA2_hash_384,
    Hacl_Streaming_SHA2_hash_512,
};

/// SHA2 224
///
/// Note the function panics when `payload` is larger than 2^32 bytes.
pub fn sha224(payload: &[u8]) -> [u8; 28] {
    let mut digest = [0u8; 28];
    unsafe {
        Hacl_Streaming_SHA2_hash_224(
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
            digest.as_mut_ptr(),
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
        Hacl_Streaming_SHA2_hash_256(
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
            digest.as_mut_ptr(),
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
        Hacl_Streaming_SHA2_hash_384(
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
            digest.as_mut_ptr(),
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
        Hacl_Streaming_SHA2_hash_512(
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
            digest.as_mut_ptr(),
        );
    }
    digest
}

pub mod streaming {
    use libcrux_hacl::{
        Hacl_Streaming_SHA2_create_in_224, Hacl_Streaming_SHA2_create_in_256,
        Hacl_Streaming_SHA2_create_in_384, Hacl_Streaming_SHA2_create_in_512,
        Hacl_Streaming_SHA2_finish_224, Hacl_Streaming_SHA2_finish_256,
        Hacl_Streaming_SHA2_finish_384, Hacl_Streaming_SHA2_finish_512,
        Hacl_Streaming_SHA2_free_224, Hacl_Streaming_SHA2_free_256, Hacl_Streaming_SHA2_free_384,
        Hacl_Streaming_SHA2_free_512, Hacl_Streaming_SHA2_init_224, Hacl_Streaming_SHA2_init_256,
        Hacl_Streaming_SHA2_init_384, Hacl_Streaming_SHA2_init_512,
        Hacl_Streaming_SHA2_state_sha2_224, Hacl_Streaming_SHA2_state_sha2_384,
        Hacl_Streaming_SHA2_update_224, Hacl_Streaming_SHA2_update_256,
        Hacl_Streaming_SHA2_update_384, Hacl_Streaming_SHA2_update_512,
    };

    macro_rules! impl_streaming {
        ($name:ident, $digest_size:literal, $state:ty, $create:expr, $init:expr, $update:expr, $finish:expr, $free:expr) => {
            pub struct $name {
                state: *mut $state,
            }

            impl $name {
                /// Initialize a new digest state.
                pub fn new() -> $name {
                    let state = $name {
                        state: unsafe { $create() },
                    };
                    unsafe { $init(state.state) };
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
        };
    }

    impl_streaming!(
        Sha224,
        28,
        Hacl_Streaming_SHA2_state_sha2_224,
        Hacl_Streaming_SHA2_create_in_224,
        Hacl_Streaming_SHA2_init_224,
        Hacl_Streaming_SHA2_update_224,
        Hacl_Streaming_SHA2_finish_224,
        Hacl_Streaming_SHA2_free_224
    );

    impl_streaming!(
        Sha256,
        32,
        Hacl_Streaming_SHA2_state_sha2_224,
        Hacl_Streaming_SHA2_create_in_256,
        Hacl_Streaming_SHA2_init_256,
        Hacl_Streaming_SHA2_update_256,
        Hacl_Streaming_SHA2_finish_256,
        Hacl_Streaming_SHA2_free_256
    );

    impl_streaming!(
        Sha384,
        48,
        Hacl_Streaming_SHA2_state_sha2_384,
        Hacl_Streaming_SHA2_create_in_384,
        Hacl_Streaming_SHA2_init_384,
        Hacl_Streaming_SHA2_update_384,
        Hacl_Streaming_SHA2_finish_384,
        Hacl_Streaming_SHA2_free_384
    );

    impl_streaming!(
        Sha512,
        64,
        Hacl_Streaming_SHA2_state_sha2_384,
        Hacl_Streaming_SHA2_create_in_512,
        Hacl_Streaming_SHA2_init_512,
        Hacl_Streaming_SHA2_update_512,
        Hacl_Streaming_SHA2_finish_512,
        Hacl_Streaming_SHA2_free_512
    );
}
