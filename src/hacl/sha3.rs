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
        pub fn new() -> Self {
            let state = Self {
                state: unsafe { Hacl_Hash_SHA3_Scalar_state_malloc() },
            };

            state
        }

        pub fn absorb_nblocks(&mut self, input: &[u8]) {
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
        pub fn squeeze_nblocks<const OUTPUT_BYTES: usize>(&mut self) -> [u8; OUTPUT_BYTES] {
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
    impl Drop for Shake128State {
        fn drop(&mut self) {
            unsafe { Hacl_Hash_SHA3_Scalar_state_free(self.state) }
        }
    }
}

#[cfg(simd256)]
pub mod incremental_x4 {
    use libcrux_hacl::{
        Hacl_Hash_SHA3_Simd256_shake128_absorb_final,
        Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks,
        Hacl_Hash_SHA3_Simd256_shake128_squeeze_nblocks, Hacl_Hash_SHA3_Simd256_state_free,
        Hacl_Hash_SHA3_Simd256_state_malloc, Lib_IntVector_Intrinsics_vec256,
    };

    /// SHAKE 128
    ///

    /// Handle to internal SHAKE 129 state
    pub struct Shake128StateX4 {
        state: *mut Lib_IntVector_Intrinsics_vec256,
    }

    impl Shake128StateX4 {
        pub fn new() -> Self {
            let state = Self {
                state: unsafe { Hacl_Hash_SHA3_Simd256_state_malloc() },
            };

            state
        }

        pub fn absorb_nblocks(
            &mut self,
            input0: &[u8],
            input1: &[u8],
            input2: &[u8],
            input3: &[u8],
        ) {
            debug_assert!(
                input0.len() == input1.len()
                && input0.len() == input2.len()
                && input0.len() == input3.len()
            );
            debug_assert!(input0.len() % 168 == 0);

            unsafe {
                Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks(
                    self.state,
                    input0.as_ptr() as _,
                    input1.as_ptr() as _,
                    input2.as_ptr() as _,
                    input3.as_ptr() as _,
                    input0.len() as u32,
                )
            };
        }

        pub fn absorb_final(&mut self, input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) {
            
            debug_assert!(
                input0.len() == input1.len()
                && input0.len() == input2.len()
                && input0.len() == input3.len()
            );
            debug_assert!(input0.len() < 168);

            unsafe {
                Hacl_Hash_SHA3_Simd256_shake128_absorb_final(
                    self.state,
                    input0.as_ptr() as _,
                    input1.as_ptr() as _,
                    input2.as_ptr() as _,
                    input3.as_ptr() as _,
                    input0.len() as u32,
                )
            };
        }
        pub fn squeeze_nblocks<const OUTPUT_BYTES: usize>(&mut self) -> [[u8; OUTPUT_BYTES]; 4] {
            debug_assert!(OUTPUT_BYTES % 168 == 0);
            let mut output = [[0u8; OUTPUT_BYTES]; 4];
            unsafe {
                Hacl_Hash_SHA3_Simd256_shake128_squeeze_nblocks(
                    self.state,
                    output[0].as_mut_ptr(),
                    output[1].as_mut_ptr(),
                    output[2].as_mut_ptr(),
                    output[3].as_mut_ptr(),
                    OUTPUT_BYTES as u32,
                )
            };

            output
        }
    }
    impl Drop for Shake128StateX4 {
        fn drop(&mut self) {
            unsafe { Hacl_Hash_SHA3_Simd256_state_free(self.state) }
        }
    }
}
