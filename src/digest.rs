//! # Hashing
//!
//! Depending on the platform and available features the most efficient implementation
//! is chosen.
//!
//! ## SHA 2
//!
//! The HACL streaming implementations are used for all SHA2 variants on all platforms.
//!
//! ## SHA 3
//!
//! The portable HACL implementations are used unless running on an x64 CPU.
//! On x64 CPUs the libjade implementation is used and if AVX2 is available, the
//! optimised libjade implementation is used.

use crate::hacl::{
    blake2,
    sha2::{
        self,
        streaming::{Sha224, Sha256, Sha384, Sha512},
    },
    sha3,
};

use libcrux_platform::{simd128_support, simd256_support};

#[derive(Debug)]
pub enum Error {
    InvalidStateFinished,
    ModeUnsupportedForStreaming,
}

/// The Digest Algorithm.
#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u32)]
pub enum Algorithm {
    Sha1 = 1,
    Sha224 = 2,
    Sha256 = 3,
    Sha384 = 4,
    Sha512 = 5,
    Blake2s = 6,
    Blake2b = 7,
    Sha3_224 = 8,
    Sha3_256 = 9,
    Sha3_384 = 10,
    Sha3_512 = 11,
}

impl From<u32> for Algorithm {
    fn from(v: u32) -> Algorithm {
        match v {
            1 => Algorithm::Sha1,
            2 => Algorithm::Sha224,
            3 => Algorithm::Sha256,
            4 => Algorithm::Sha384,
            5 => Algorithm::Sha512,
            6 => Algorithm::Blake2s,
            7 => Algorithm::Blake2b,
            8 => Algorithm::Sha3_224,
            9 => Algorithm::Sha3_256,
            10 => Algorithm::Sha3_384,
            11 => Algorithm::Sha3_512,
            _ => panic!("Unknown Digest mode {}", v),
        }
    }
}

impl From<Algorithm> for u32 {
    fn from(v: Algorithm) -> u32 {
        match v {
            Algorithm::Sha1 => 1,
            Algorithm::Sha224 => 2,
            Algorithm::Sha256 => 3,
            Algorithm::Sha384 => 4,
            Algorithm::Sha512 => 5,
            Algorithm::Blake2s => 6,
            Algorithm::Blake2b => 7,
            Algorithm::Sha3_224 => 8,
            Algorithm::Sha3_256 => 9,
            Algorithm::Sha3_384 => 10,
            Algorithm::Sha3_512 => 11,
        }
    }
}

/// Returns the output size of a digest.
pub const fn digest_size(mode: Algorithm) -> usize {
    match mode {
        Algorithm::Sha1 => 20,
        Algorithm::Sha224 => 28,
        Algorithm::Sha256 => 32,
        Algorithm::Sha384 => 48,
        Algorithm::Sha512 => 64,
        Algorithm::Blake2s => 32,
        Algorithm::Blake2b => 64,
        Algorithm::Sha3_224 => 28,
        Algorithm::Sha3_256 => 32,
        Algorithm::Sha3_384 => 48,
        Algorithm::Sha3_512 => 64,
    }
}

impl Algorithm {
    pub fn size(self) -> usize {
        digest_size(self)
    }
}

pub type Sha2_224Digest = [u8; digest_size(Algorithm::Sha224)];
pub type Sha2_256Digest = [u8; digest_size(Algorithm::Sha256)];
pub type Sha2_384Digest = [u8; digest_size(Algorithm::Sha384)];
pub type Sha2_512Digest = [u8; digest_size(Algorithm::Sha512)];

pub type Sha3_224Digest = [u8; digest_size(Algorithm::Sha3_224)];
pub type Sha3_256Digest = [u8; digest_size(Algorithm::Sha3_256)];
pub type Sha3_384Digest = [u8; digest_size(Algorithm::Sha3_384)];
pub type Sha3_512Digest = [u8; digest_size(Algorithm::Sha3_512)];

// Single-shot API

macro_rules! sha3_impl {
    ($fun_name:ident, $output:ty, $jasmin_fun:expr, $hacl_fun:expr) => {
        #[cfg(all(
            libjade,
            target_arch = "x86_64",
            any(target_os = "linux", target_os = "macos")
        ))]
        pub fn $fun_name(payload: &[u8]) -> $output {
            // On x64 we use Jasmin for AVX2 and fallback.
            $jasmin_fun(payload)
        }

        #[cfg(not(all(
            libjade,
            target_arch = "x86_64",
            any(target_os = "linux", target_os = "macos")
        )))]
        pub fn $fun_name(payload: &[u8]) -> $output {
            // On all other platforms we use HACL
            $hacl_fun(payload)
        }
    };
}

sha3_impl!(
    sha3_224,
    Sha3_224Digest,
    crate::jasmin::sha3::sha3_224,
    sha3::sha224
);
sha3_impl!(
    sha3_256,
    Sha3_256Digest,
    crate::jasmin::sha3::sha3_256,
    sha3::sha256
);
sha3_impl!(
    sha3_384,
    Sha3_384Digest,
    crate::jasmin::sha3::sha3_384,
    sha3::sha384
);
sha3_impl!(
    sha3_512,
    Sha3_512Digest,
    crate::jasmin::sha3::sha3_512,
    sha3::sha512
);

/// Create the digest for the given `data` and mode `alg`.
/// The output has length [`digest_size(alg)`], i.e. blake2 returns a full-sized
/// digest.
///
/// Note that this will return a vector on the heap. Use functions like [`sha2_256`]
/// if you want an array.
pub fn hash(alg: Algorithm, payload: &[u8]) -> Vec<u8> {
    // Note that one-shot hacl functions are slower than streaming.
    // So we only use streaming.
    match alg {
        Algorithm::Sha1 => todo!(),
        Algorithm::Sha224 => sha2::sha224(payload).into(),
        Algorithm::Sha256 => sha2::sha256(payload).into(),
        Algorithm::Sha384 => sha2::sha384(payload).into(),
        Algorithm::Sha512 => sha2::sha512(payload).into(),
        Algorithm::Blake2s => blake2s(payload, &[]),
        Algorithm::Blake2b => blake2b(payload, &[]),
        Algorithm::Sha3_224 => sha3_224(payload).into(),
        Algorithm::Sha3_256 => sha3_256(payload).into(),
        Algorithm::Sha3_384 => sha3_384(payload).into(),
        Algorithm::Sha3_512 => sha3_512(payload).into(),
    }
}

#[cfg(simd128)]
fn blake2s_128<const LEN: usize>(payload: &[u8], key: &[u8]) -> [u8; LEN] {
    blake2::simd128::blake2s(payload, key)
}

#[cfg(not(simd128))]
fn blake2s_128<const LEN: usize>(payload: &[u8], key: &[u8]) -> [u8; LEN] {
    blake2::blake2s::<LEN>(payload, key)
}

/// A simple wrapper to multiplex
fn blake2s(payload: &[u8], key: &[u8]) -> Vec<u8> {
    const DIGEST_LEN: usize = digest_size(Algorithm::Blake2s);
    if simd128_support() {
        blake2s_128::<DIGEST_LEN>(payload, key)
    } else {
        blake2::blake2s::<DIGEST_LEN>(payload, key)
    }
    .into()
}

#[cfg(simd256)]
fn blake2b_256<const LEN: usize>(payload: &[u8], key: &[u8]) -> [u8; LEN] {
    blake2::simd256::blake2b(payload, key)
}

#[cfg(not(simd256))]
fn blake2b_256<const LEN: usize>(payload: &[u8], key: &[u8]) -> [u8; LEN] {
    blake2::blake2b::<LEN>(payload, key)
}

/// Blake2b
fn blake2b(payload: &[u8], key: &[u8]) -> Vec<u8> {
    const DIGEST_LEN: usize = digest_size(Algorithm::Blake2b);
    if simd256_support() {
        blake2b_256::<DIGEST_LEN>(payload, key)
    } else {
        blake2::blake2b::<DIGEST_LEN>(payload, key)
    }
    .into()
}

/// SHA2 224
pub fn sha2_224(payload: &[u8]) -> Sha2_224Digest {
    sha2::sha224(payload)
}

/// SHA2 256
pub fn sha2_256(payload: &[u8]) -> Sha2_256Digest {
    sha2::sha256(payload)
}

/// SHA2 384
pub fn sha2_384(payload: &[u8]) -> Sha2_384Digest {
    sha2::sha384(payload)
}

/// SHA2 512
pub fn sha2_512(payload: &[u8]) -> Sha2_512Digest {
    sha2::sha512(payload)
}

// Streaming API - This is the recommended one.
macro_rules! impl_streaming {
    ($name:ident, $state:ty, $result:ty) => {
        #[derive(Clone)]
        pub struct $name {
            state: $state,
        }
        impl $name {
            /// Initialize a new digest state.
            pub fn new() -> Self {
                Self {
                    state: <$state>::new(),
                }
            }

            /// Add the `payload` to the digest.
            pub fn update(&mut self, payload: &[u8]) {
                self.state.update(payload);
            }

            /// Get the digest.
            ///
            /// Note that the digest state can be continued to be used, to extend the
            /// digest.
            pub fn finish(&mut self) -> $result {
                self.state.finish()
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }
    };
}
impl_streaming!(Sha2_224, Sha224, Sha2_224Digest);
impl_streaming!(Sha2_256, Sha256, Sha2_256Digest);
impl_streaming!(Sha2_384, Sha384, Sha2_384Digest);
impl_streaming!(Sha2_512, Sha512, Sha2_512Digest);

// SHAKE messages from SHA 3

#[cfg(simd256)]
fn shake128x4_256<const LEN: usize>(
    data0: &[u8],
    data1: &[u8],
    data2: &[u8],
    data3: &[u8],
) -> ([u8; LEN], [u8; LEN], [u8; LEN], [u8; LEN]) {
    sha3::x4::shake128(data0, data1, data2, data3)
}

#[cfg(not(simd256))]
fn shake128x4_256<const LEN: usize>(
    data0: &[u8],
    data1: &[u8],
    data2: &[u8],
    data3: &[u8],
) -> ([u8; LEN], [u8; LEN], [u8; LEN], [u8; LEN]) {
    shake128x4_portable(data0, data1, data2, data3)
}

// Fake the x4 and call shake128 4 times.
fn shake128x4_portable<const LEN: usize>(
    data0: &[u8],
    data1: &[u8],
    data2: &[u8],
    data3: &[u8],
) -> ([u8; LEN], [u8; LEN], [u8; LEN], [u8; LEN]) {
    let input_len = data0.len();
    debug_assert!(
        input_len == data1.len()
            && input_len == data2.len()
            && input_len == data3.len()
            && input_len <= u32::MAX as usize
            && LEN <= u32::MAX as usize
    );
    let digest0 = sha3::shake128(data0);
    let digest1 = sha3::shake128(data1);
    let digest2 = sha3::shake128(data2);
    let digest3 = sha3::shake128(data3);
    (digest0, digest1, digest2, digest3)
}

/// SHAKE 128 x4
///
/// This calls 4 times shake128 at a time. If there's no SIMD256 support present
/// on the platform, regular shake128 is executed 4 times.
///
/// The caller must define the size of the output in the return type.
pub fn shake128x4<const LEN: usize>(
    data0: &[u8],
    data1: &[u8],
    data2: &[u8],
    data3: &[u8],
) -> ([u8; LEN], [u8; LEN], [u8; LEN], [u8; LEN]) {
    if simd256_support() {
        shake128x4_256(data0, data1, data2, data3)
    } else {
        shake128x4_portable(data0, data1, data2, data3)
    }
}

/// SHAKE 128
///
/// The caller must define the size of the output in the return type.
pub fn shake128<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
    sha3::shake128(data)
}

/// SHAKE 256
///
/// The caller must define the size of the output in the return type.
pub fn shake256<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
    sha3::shake256(data)
}

/// An incremental eXtendable Output Function API for SHA3 (shake).
///
/// This x4 variant of the incremental API always processes 4 inputs at a time.
/// This uses AVX2 when available to run the 4 operations in parallel.
///
/// More generic APIs will be added later.
pub mod incremental_x4 {

    /// Incremental state
    #[cfg_attr(hax, hax_lib::opaque_type)]
    pub struct Shake128StateX4 {
        state: crate::hacl::sha3::incremental_x4::Shake128StateX4,
    }

    impl Shake128StateX4 {
        /// Create a new Shake128 x4 state.
        #[inline(always)]
        pub fn new() -> Self {
            Self {
                state: crate::hacl::sha3::incremental_x4::Shake128StateX4::new(),
            }
        }

        /// This is only used internally to work around Eurydice bugs.
        #[inline(always)]
        pub fn free_memory(self) {
            self.state.free();
        }

        /// Absorb 4 blocks.
        ///
        /// A blocks MUST all be the same length.
        /// Each slice MUST be a multiple of the block length 168.
        #[inline(always)]
        pub fn absorb_4blocks(&mut self, input: [&[u8]; 4]) {
            self.state.absorb_blocks(input)
        }

        /// Absorb up to 4 blocks.
        ///
        /// The `input` must be of length 1 to 4.
        /// A blocks MUST all be the same length.
        /// Each slice MUST be a multiple of the block length 168.
        #[inline(always)]
        pub fn absorb_final<const N: usize>(&mut self, input: [&[u8]; N]) {
            // Pad the input to the length of 4
            let data = [
                input[0],
                if N > 1 { input[1] } else { &input[0] },
                if N > 2 { input[2] } else { &input[0] },
                if N > 3 { input[3] } else { &input[0] },
            ];
            self.state.absorb_final(data);
        }

        /// Squeeze `M` blocks of length `N`
        #[inline(always)]
        pub fn squeeze_blocks<const N: usize, const M: usize>(&mut self) -> [[u8; N]; M] {
            self.state.squeeze_blocks()
        }
    }
}
