use core::ptr::null_mut;

use libcrux_hacl::{
    Hacl_Hash_SHA3_Scalar_shake128_absorb_final, Hacl_Hash_SHA3_Scalar_shake128_absorb_nblocks,
    Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks, Hacl_Hash_SHA3_Scalar_state_free,
    Hacl_Hash_SHA3_Scalar_state_malloc, 
    Hacl_Hash_SHA3_shake256_hacl
};

#[cfg(feature = "simd256")]
use libcrux_hacl::{
    Hacl_Hash_SHA3_Simd256_shake128_absorb_final, Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks,
    Hacl_Hash_SHA3_Simd256_shake128_squeeze_nblocks, Hacl_Hash_SHA3_Simd256_state_free,
    Hacl_Hash_SHA3_Simd256_state_malloc, Lib_IntVector_Intrinsics_vec256, 
    Hacl_Hash_SHA3_Simd256_shake256
};
#[cfg(feature = "simd256")]
use libcrux_platform::simd256_support;

/// SHAKE 256
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
#[cfg(feature = "simd256")]
pub(crate) fn shake256<const BYTES: usize>(
    payload: [&[u8];4],
) -> [[u8; BYTES];4] {
    let input_len = payload[0].len();
    debug_assert!(
        input_len == payload[1].len()
            && input_len == payload[2].len()
            && input_len == payload[3].len()
            && input_len <= u32::MAX as usize
            && BYTES <= u32::MAX as usize
    );
    let mut digest = [[0u8; BYTES];4];
    if simd256_support() {
        unsafe {
            Hacl_Hash_SHA3_Simd256_shake256(
                input_len as u32,
                payload[0].as_ptr() as _,
                payload[1].as_ptr() as _,
                payload[2].as_ptr() as _,
                payload[3].as_ptr() as _,
                BYTES as u32,
                digest[0].as_mut_ptr(),
                digest[1].as_mut_ptr(),
                digest[2].as_mut_ptr(),
                digest[3].as_mut_ptr(),
            );
        }
    } else {
        unsafe {
            Hacl_Hash_SHA3_shake256_hacl(
                input_len as u32,
                payload[0].as_ptr() as _,
                BYTES as u32,
                digest[0].as_mut_ptr(),
            );
            Hacl_Hash_SHA3_shake256_hacl(
                input_len as u32,
                payload[1].as_ptr() as _,
                BYTES as u32,
                digest[1].as_mut_ptr(),
            );
            Hacl_Hash_SHA3_shake256_hacl(
                input_len as u32,
                payload[2].as_ptr() as _,
                BYTES as u32,
                digest[2].as_mut_ptr(),
            );
            Hacl_Hash_SHA3_shake256_hacl(
                input_len as u32,
                payload[3].as_ptr() as _,
                BYTES as u32,
                digest[3].as_mut_ptr(),
            );
        }
    }
    digest
}

#[inline(always)]
#[cfg(not(feature = "simd256"))]
pub(crate) fn shake256<const BYTES: usize>(
    payload: [&[u8];4],
) -> [[u8; BYTES];4] {
    let input_len = payload[0].len();
    debug_assert!(
        input_len == payload[1].len()
            && input_len == payload[2].len()
            && input_len == payload[3].len()
            && input_len <= u32::MAX as usize
            && BYTES <= u32::MAX as usize
    );
    let mut digest = [[0u8; BYTES];4];
    
    unsafe {
        Hacl_Hash_SHA3_shake256_hacl(
            input_len as u32,
            payload[0].as_ptr() as _,
            BYTES as u32,
            digest[0].as_mut_ptr(),
        );
        Hacl_Hash_SHA3_shake256_hacl(
            input_len as u32,
            payload[1].as_ptr() as _,
            BYTES as u32,
            digest[1].as_mut_ptr(),
        );
        Hacl_Hash_SHA3_shake256_hacl(
            input_len as u32,
            payload[2].as_ptr() as _,
            BYTES as u32,
            digest[2].as_mut_ptr(),
        );
        Hacl_Hash_SHA3_shake256_hacl(
            input_len as u32,
            payload[3].as_ptr() as _,
            BYTES as u32,
            digest[3].as_mut_ptr(),
        );
    }
    digest
}


/// Incremental SHAKE 128
///
/// Handle to internal SHAKE 128 state
#[cfg(feature = "simd256")]
pub struct Shake128StateX4 {
    statex4: *mut Lib_IntVector_Intrinsics_vec256,
    state: [*mut u64; 4],
}

#[cfg(not(feature = "simd256"))]
pub struct Shake128StateX4 {
    state: [*mut u64; 4],
}

impl Shake128StateX4 {
    #[cfg(feature = "simd256")]
    pub fn new() -> Self {
        if simd256_support() {
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

    #[cfg(not(feature = "simd256"))]
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
    #[cfg(feature = "simd256")]
    pub fn free(mut self) {
        if simd256_support() {
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
    #[cfg(not(feature = "simd256"))]
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
    #[cfg(feature = "simd256")]
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
    #[cfg(not(feature = "simd256"))]
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
    #[cfg(feature = "simd256")]
    pub fn absorb_final(&mut self, input: [&[u8]; 4]) {
        debug_assert!(
            (input[0].len() == input[1].len() || input[1].len() == 0)
                && (input[0].len() == input[2].len() || input[2].len() == 0)
                && (input[0].len() == input[3].len() || input[3].len() == 0)
        );
        debug_assert!(input[0].len() < 168);

        if simd256_support() {
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
    #[cfg(not(feature = "simd256"))]
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

    #[cfg(feature = "simd256")]
    pub fn squeeze_blocks<const OUTPUT_BYTES: usize, const M: usize>(
        &mut self,
    ) -> [[u8; OUTPUT_BYTES]; M] {
        debug_assert!(OUTPUT_BYTES % 168 == 0);
        debug_assert!(M <= self.state.len() && (M == 2 || M == 3 || M == 4));

        if simd256_support() {
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

    #[cfg(not(feature = "simd256"))]
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
    #[cfg(feature = "simd256")]
    fn drop(&mut self) {
        if simd256_support() {
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

    #[cfg(not(feature = "simd256"))]
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
