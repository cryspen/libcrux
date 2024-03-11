#![allow(dead_code)]

use libcrux_hacl::{
    Hacl_Hash_SHA3_sha3_224, Hacl_Hash_SHA3_sha3_256, Hacl_Hash_SHA3_sha3_384,
    Hacl_Hash_SHA3_sha3_512, Hacl_Hash_SHA3_shake128_hacl, Hacl_Hash_SHA3_shake256_hacl,
};

/// SHA3 224
#[inline(always)]
pub(crate) fn sha224(payload: &[u8]) -> [u8; 28] {
    let mut digest = [0u8; 28];
    unsafe {
        Hacl_Hash_SHA3_sha3_224(
            digest.as_mut_ptr(),
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
        );
    }
    digest
}

/// SHA3 256
#[inline(always)]
pub(crate) fn sha256(payload: &[u8]) -> [u8; 32] {
    let mut digest = [0u8; 32];
    unsafe {
        Hacl_Hash_SHA3_sha3_256(
            digest.as_mut_ptr(),
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
        );
    }
    digest
}

/// SHA3 384
#[inline(always)]
pub(crate) fn sha384(payload: &[u8]) -> [u8; 48] {
    let mut digest = [0u8; 48];
    unsafe {
        Hacl_Hash_SHA3_sha3_384(
            digest.as_mut_ptr(),
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
        );
    }
    digest
}

/// SHA3 512
#[inline(always)]
pub(crate) fn sha512(payload: &[u8]) -> [u8; 64] {
    let mut digest = [0u8; 64];
    unsafe {
        Hacl_Hash_SHA3_sha3_512(
            digest.as_mut_ptr(),
            payload.as_ptr() as _,
            payload.len().try_into().unwrap(),
        );
    }
    digest
}

/// SHAKE 128
#[inline(always)]
pub(crate) fn shake128<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    unsafe {
        Hacl_Hash_SHA3_shake128_hacl(
            data.len() as u32,
            data.as_ptr() as _,
            BYTES as u32,
            out.as_mut_ptr(),
        );
    }
    out
}

/// SHAKE 256
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub(crate) fn shake256<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    unsafe {
        Hacl_Hash_SHA3_shake256_hacl(
            data.len() as u32,
            data.as_ptr() as _,
            BYTES as u32,
            out.as_mut_ptr(),
        );
    }
    out
}

#[cfg(simd256)]
pub mod x4 {
    use libcrux_hacl::{
        Hacl_Hash_SHA3_Simd256_sha3_224, Hacl_Hash_SHA3_Simd256_sha3_256,
        Hacl_Hash_SHA3_Simd256_sha3_384, Hacl_Hash_SHA3_Simd256_sha3_512,
        Hacl_Hash_SHA3_Simd256_shake128, Hacl_Hash_SHA3_Simd256_shake256,
    };

    macro_rules! impl_sha3_vec {
        ($name:ident, $fun:expr, $out_len:literal) => {
            #[inline(always)]
            pub(crate) fn $name(
                payload0: &[u8],
                payload1: &[u8],
                payload2: &[u8],
                payload3: &[u8],
            ) -> (
                [u8; $out_len],
                [u8; $out_len],
                [u8; $out_len],
                [u8; $out_len],
            ) {
                let input_len = payload0.len();
                debug_assert!(
                    input_len == payload1.len()
                        && input_len == payload2.len()
                        && input_len == payload3.len()
                        && input_len <= u32::MAX as usize
                );
                let mut digest0 = [0u8; $out_len];
                let mut digest1 = [0u8; $out_len];
                let mut digest2 = [0u8; $out_len];
                let mut digest3 = [0u8; $out_len];
                unsafe {
                    $fun(
                        input_len as u32,
                        payload0.as_ptr() as _,
                        payload1.as_ptr() as _,
                        payload2.as_ptr() as _,
                        payload3.as_ptr() as _,
                        digest0.as_mut_ptr(),
                        digest1.as_mut_ptr(),
                        digest2.as_mut_ptr(),
                        digest3.as_mut_ptr(),
                    );
                }
                (digest0, digest1, digest2, digest3)
            }
        };
    }

    impl_sha3_vec!(sha224, Hacl_Hash_SHA3_Simd256_sha3_224, 28);
    impl_sha3_vec!(sha256, Hacl_Hash_SHA3_Simd256_sha3_256, 32);
    impl_sha3_vec!(sha384, Hacl_Hash_SHA3_Simd256_sha3_384, 48);
    impl_sha3_vec!(sha512, Hacl_Hash_SHA3_Simd256_sha3_512, 64);

    /// SHAKE 128
    #[inline(always)]
    pub(crate) fn shake128<const BYTES: usize>(
        payload0: &[u8],
        payload1: &[u8],
        payload2: &[u8],
        payload3: &[u8],
    ) -> ([u8; BYTES], [u8; BYTES], [u8; BYTES], [u8; BYTES]) {
        let input_len = payload0.len();
        debug_assert!(
            input_len == payload1.len()
                && input_len == payload2.len()
                && input_len == payload3.len()
                && input_len <= u32::MAX as usize
                && BYTES <= u32::MAX as usize
        );
        let mut digest0 = [0u8; BYTES];
        let mut digest1 = [0u8; BYTES];
        let mut digest2 = [0u8; BYTES];
        let mut digest3 = [0u8; BYTES];
        unsafe {
            Hacl_Hash_SHA3_Simd256_shake128(
                input_len as u32,
                payload0.as_ptr() as _,
                payload1.as_ptr() as _,
                payload2.as_ptr() as _,
                payload3.as_ptr() as _,
                BYTES as u32,
                digest0.as_mut_ptr(),
                digest1.as_mut_ptr(),
                digest2.as_mut_ptr(),
                digest3.as_mut_ptr(),
            );
        }
        (digest0, digest1, digest2, digest3)
    }

    /// SHAKE 256
    ///
    /// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
    /// the output will only return `u32::MAX` bytes.
    #[inline(always)]
    pub(crate) fn shake256<const BYTES: usize>(
        payload0: &[u8],
        payload1: &[u8],
        payload2: &[u8],
        payload3: &[u8],
    ) -> ([u8; BYTES], [u8; BYTES], [u8; BYTES], [u8; BYTES]) {
        let input_len = payload0.len();
        debug_assert!(
            input_len == payload1.len()
                && input_len == payload2.len()
                && input_len == payload3.len()
                && input_len <= u32::MAX as usize
                && BYTES <= u32::MAX as usize
        );
        let mut digest0 = [0u8; BYTES];
        let mut digest1 = [0u8; BYTES];
        let mut digest2 = [0u8; BYTES];
        let mut digest3 = [0u8; BYTES];
        unsafe {
            Hacl_Hash_SHA3_Simd256_shake256(
                input_len as u32,
                payload0.as_ptr() as _,
                payload1.as_ptr() as _,
                payload2.as_ptr() as _,
                payload3.as_ptr() as _,
                BYTES as u32,
                digest0.as_mut_ptr(),
                digest1.as_mut_ptr(),
                digest2.as_mut_ptr(),
                digest3.as_mut_ptr(),
            );
        }
        (digest0, digest1, digest2, digest3)
    }
}

/// This module groups together functions that can be used to absorb or squeeze
/// bytes in increments.
/// TODO: This module should not be public, see: https://github.com/cryspen/libcrux/issues/157
pub mod incremental {
    use std::ptr::null_mut;

    use libcrux_hacl::{
        Hacl_Hash_SHA3_Scalar_shake128_absorb_final, Hacl_Hash_SHA3_Scalar_shake128_absorb_nblocks,
        Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks, Hacl_Hash_SHA3_Scalar_state_free,
        Hacl_Hash_SHA3_Scalar_state_malloc,
    };

    /// SHAKE 128
    ///

    /// Handle to internal SHAKE 129 state
    pub struct Shake128State {
        state: *mut u64,
    }

    impl Shake128State {
        /// Create a new state.
        ///
        /// This allocates the necessary memory.
        pub fn new() -> Self {
            let state = Self {
                state: unsafe { Hacl_Hash_SHA3_Scalar_state_malloc() },
            };

            state
        }

        /// Free and consume the state.
        ///
        /// **NOTE:** This consumes the value. It is not usable after this call!
        pub fn free(&mut self) {
            unsafe {
                Hacl_Hash_SHA3_Scalar_state_free(self.state);
                // null the pointer (hacl isn't doing that unfortunately)
                // This way we can check whether the memory was freed already or not.
                self.state = null_mut();
            }
        }

        pub fn absorb_blocks(&mut self, input: &[u8]) {
            unsafe {
                Hacl_Hash_SHA3_Scalar_shake128_absorb_nblocks(
                    self.state,
                    input.as_ptr() as _,
                    input.len() as u32,
                )
            };
        }

        pub fn absorb_final(&mut self, input: &[u8]) {
            unsafe {
                Hacl_Hash_SHA3_Scalar_shake128_absorb_final(
                    self.state,
                    input.as_ptr() as _,
                    input.len() as u32,
                )
            };
        }
        pub fn squeeze_blocks<const OUTPUT_BYTES: usize>(&mut self) -> [u8; OUTPUT_BYTES] {
            debug_assert!(OUTPUT_BYTES % 168 == 0);
            let mut output = [0u8; OUTPUT_BYTES];
            unsafe {
                Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks(
                    self.state,
                    output.as_mut_ptr(),
                    OUTPUT_BYTES as u32,
                )
            };

            output
        }
    }

    /// **NOTE:** When generating C code with Eurydice, the state needs to be freed
    ///           manually for now due to a bug in Eurydice.
    impl Drop for Shake128State {
        fn drop(&mut self) {
            unsafe {
                // A manual free may have occurred already.
                // Avoid double free.
                if !self.state.is_null() {
                    Hacl_Hash_SHA3_Scalar_state_free(self.state)
                }
            }
        }
    }
}

pub mod incremental_x4 {
    use std::ptr::null_mut;

    use libcrux_hacl::{
        Hacl_Hash_SHA3_Scalar_shake128_absorb_final, Hacl_Hash_SHA3_Scalar_shake128_absorb_nblocks,
        Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks, Hacl_Hash_SHA3_Scalar_state_free,
        Hacl_Hash_SHA3_Scalar_state_malloc,
    };
    #[cfg(simd256)]
    use libcrux_hacl::{
        Hacl_Hash_SHA3_Simd256_shake128_absorb_final,
        Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks,
        Hacl_Hash_SHA3_Simd256_shake128_squeeze_nblocks, Hacl_Hash_SHA3_Simd256_state_free,
        Hacl_Hash_SHA3_Simd256_state_malloc, Lib_IntVector_Intrinsics_vec256,
    };
    #[cfg(simd256)]
    use libcrux_platform::simd256_support;

    /// SHAKE 128
    ///
    /// Handle to internal SHAKE 128 state
    #[cfg(simd256)]
    pub struct Shake128StateX4 {
        statex4: *mut Lib_IntVector_Intrinsics_vec256,
        state: [*mut u64; 4],
    }

    #[cfg(not(simd256))]
    pub struct Shake128StateX4 {
        state: [*mut u64; 4],
    }

    impl Shake128StateX4 {
        #[cfg(simd256)]
        pub fn new() -> Self {
            if cfg!(simd256) && simd256_support() {
                Self {
                    statex4: unsafe { Hacl_Hash_SHA3_Simd256_state_malloc() },
                    state: [null_mut(), null_mut(), null_mut(), null_mut()],
                }
            } else {
                Self {
                    statex4: null_mut(),
                    state: unsafe {
                        [
                            Hacl_Hash_SHA3_Scalar_state_malloc(),
                            Hacl_Hash_SHA3_Scalar_state_malloc(),
                            Hacl_Hash_SHA3_Scalar_state_malloc(),
                            Hacl_Hash_SHA3_Scalar_state_malloc(),
                        ]
                    },
                }
            }
        }

        #[cfg(not(simd256))]
        pub fn new() -> Self {
            Self {
                state: unsafe {
                    [
                        Hacl_Hash_SHA3_Scalar_state_malloc(),
                        Hacl_Hash_SHA3_Scalar_state_malloc(),
                        Hacl_Hash_SHA3_Scalar_state_malloc(),
                        Hacl_Hash_SHA3_Scalar_state_malloc(),
                    ]
                },
            }
        }

        /// Free and consume the state.
        ///
        /// **NOTE:** This consumes the value. It is not usable after this call!
        #[cfg(simd256)]
        pub fn free(mut self) {
            if cfg!(simd256) && simd256_support() {
                unsafe {
                    Hacl_Hash_SHA3_Simd256_state_free(self.statex4);
                    // null the pointer (hacl isn't doing that unfortunately)
                    // This way we can check whether the memory was freed already or not.
                    self.statex4 = null_mut();
                }
            } else {
                for i in 0..4 {
                    unsafe {
                        Hacl_Hash_SHA3_Scalar_state_free(self.state[i]);
                        // null the pointer (hacl isn't doing that unfortunately)
                        // This way we can check whether the memory was freed already or not.
                        self.state[i] = null_mut();
                    }
                }
            }
        }

        /// Free and consume the state.
        ///
        /// **NOTE:** This consumes the value. It is not usable after this call!
        #[cfg(not(simd256))]
        pub fn free(mut self) {
            for i in 0..4 {
                unsafe {
                    Hacl_Hash_SHA3_Scalar_state_free(self.state[i]);
                    // null the pointer (hacl isn't doing that unfortunately)
                    // This way we can check whether the memory was freed already or not.
                    self.state[i] = null_mut();
                }
            }
        }

        /// Absorb up to 4 blocks at a time.
        ///
        /// The input length must be a multiple of the SHA3 block length of 168.
        ///
        /// The input is truncated at `u32::MAX`.
        #[cfg(simd256)]
        pub fn absorb_blocks(&mut self, input: [&[u8]; 4]) {
            debug_assert!(
                (input[0].len() == input[1].len() || input[1].len() == 0)
                    && (input[0].len() == input[2].len() || input[2].len() == 0)
                    && (input[0].len() == input[3].len() || input[3].len() == 0)
            );
            debug_assert!(input[0].len() % 168 == 0);

            if simd256_support() {
                unsafe {
                    Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks(
                        self.statex4,
                        input[0].as_ptr() as _,
                        input[1].as_ptr() as _,
                        input[2].as_ptr() as _,
                        input[3].as_ptr() as _,
                        input[0].len() as u32,
                    )
                };
            } else {
                for i in 0..4 {
                    if !input[i].is_empty() {
                        unsafe {
                            Hacl_Hash_SHA3_Scalar_shake128_absorb_nblocks(
                                self.state[i],
                                input[i].as_ptr() as _,
                                input[i].len() as u32,
                            );
                        };
                    }
                }
            }
        }

        /// Absorb up to 4 blocks at a time.
        ///
        /// The input length must be a multiple of the SHA3 block length of 168.
        ///
        /// The input is truncated at `u32::MAX`.
        #[cfg(not(simd256))]
        pub fn absorb_blocks(&mut self, input: [&[u8]; 4]) {
            debug_assert!(
                (input[0].len() == input[1].len() || input[1].len() == 0)
                    && (input[0].len() == input[2].len() || input[2].len() == 0)
                    && (input[0].len() == input[3].len() || input[3].len() == 0)
            );
            debug_assert!(input[0].len() % 168 == 0);

            for i in 0..4 {
                if !input[i].is_empty() {
                    unsafe {
                        Hacl_Hash_SHA3_Scalar_shake128_absorb_nblocks(
                            self.state[i],
                            input[i].as_ptr() as _,
                            input[i].len() as u32,
                        );
                    };
                }
            }
        }

        /// Absorb up to 4 final blocks at a time.
        ///
        /// The input length must be a multiple of the SHA3 block length of 168.
        ///
        /// The input is truncated at `u32::MAX`.
        #[cfg(simd256)]
        pub fn absorb_final(&mut self, input: [&[u8]; 4]) {
            debug_assert!(
                (input[0].len() == input[1].len() || input[1].len() == 0)
                    && (input[0].len() == input[2].len() || input[2].len() == 0)
                    && (input[0].len() == input[3].len() || input[3].len() == 0)
            );
            debug_assert!(input[0].len() < 168);

            if cfg!(simd256) && simd256_support() {
                unsafe {
                    Hacl_Hash_SHA3_Simd256_shake128_absorb_final(
                        self.statex4,
                        input[0].as_ptr() as _,
                        input[1].as_ptr() as _,
                        input[2].as_ptr() as _,
                        input[3].as_ptr() as _,
                        input[0].len() as u32,
                    )
                };
            } else {
                for i in 0..4 {
                    if !input[i].is_empty() {
                        unsafe {
                            Hacl_Hash_SHA3_Scalar_shake128_absorb_final(
                                self.state[i],
                                input[i].as_ptr() as _,
                                input[i].len() as u32,
                            );
                        };
                    }
                }
            }
        }

        /// Absorb up to 4 final blocks at a time.
        ///
        /// The input length must be a multiple of the SHA3 block length of 168.
        ///
        /// The input is truncated at `u32::MAX`.
        #[cfg(not(simd256))]
        pub fn absorb_final(&mut self, input: [&[u8]; 4]) {
            debug_assert!(
                (input[0].len() == input[1].len() || input[1].len() == 0)
                    && (input[0].len() == input[2].len() || input[2].len() == 0)
                    && (input[0].len() == input[3].len() || input[3].len() == 0)
            );
            debug_assert!(input[0].len() < 168);

            for i in 0..4 {
                if !input[i].is_empty() {
                    unsafe {
                        Hacl_Hash_SHA3_Scalar_shake128_absorb_final(
                            self.state[i],
                            input[i].as_ptr() as _,
                            input[i].len() as u32,
                        );
                    };
                }
            }
        }

        #[cfg(simd256)]
        pub fn squeeze_blocks<const OUTPUT_BYTES: usize, const M: usize>(
            &mut self,
        ) -> [[u8; OUTPUT_BYTES]; M] {
            debug_assert!(OUTPUT_BYTES % 168 == 0);
            debug_assert!(M <= self.state.len() && (M == 2 || M == 3 || M == 4));

            if cfg!(simd256) && simd256_support() {
                let mut output = [[0u8; OUTPUT_BYTES]; 4];
                unsafe {
                    Hacl_Hash_SHA3_Simd256_shake128_squeeze_nblocks(
                        self.statex4,
                        output[0].as_mut_ptr(),
                        output[1].as_mut_ptr(),
                        output[2].as_mut_ptr(),
                        output[3].as_mut_ptr(),
                        OUTPUT_BYTES as u32,
                    );
                };
                core::array::from_fn(|i| output[i])
            } else {
                let mut output = [[0u8; OUTPUT_BYTES]; M];
                for i in 0..M {
                    unsafe {
                        Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks(
                            self.state[i],
                            output[i].as_mut_ptr(),
                            OUTPUT_BYTES as u32,
                        );
                    };
                }
                output
            }
        }

        #[cfg(not(simd256))]
        pub fn squeeze_blocks<const OUTPUT_BYTES: usize, const M: usize>(
            &mut self,
        ) -> [[u8; OUTPUT_BYTES]; M] {
            debug_assert!(OUTPUT_BYTES % 168 == 0);
            debug_assert!(M <= self.state.len());

            let mut output = [[0u8; OUTPUT_BYTES]; M];

            for i in 0..M {
                unsafe {
                    Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks(
                        self.state[i],
                        output[i].as_mut_ptr(),
                        OUTPUT_BYTES as u32,
                    );
                };
            }

            output
        }
    }

    /// **NOTE:** When generating C code with Eurydice, the state needs to be freed
    ///           manually for now due to a bug in Eurydice.
    impl Drop for Shake128StateX4 {
        #[cfg(simd256)]
        fn drop(&mut self) {
            if cfg!(simd256) && simd256_support() {
                // A manual free may have occurred already.
                // Avoid double free.
                unsafe {
                    if !self.statex4.is_null() {
                        Hacl_Hash_SHA3_Simd256_state_free(self.statex4);
                    }
                }
            } else {
                // A manual free may have occurred already.
                // Avoid double free.
                for i in 0..4 {
                    unsafe {
                        if !self.state[i].is_null() {
                            Hacl_Hash_SHA3_Scalar_state_free(self.state[i])
                        }
                    }
                }
            }
        }

        #[cfg(not(simd256))]
        fn drop(&mut self) {
            // A manual free may have occurred already.
            // Avoid double free.
            for i in 0..4 {
                unsafe {
                    if !self.state[i].is_null() {
                        Hacl_Hash_SHA3_Scalar_state_free(self.state[i])
                    }
                }
            }
        }
    }
}
