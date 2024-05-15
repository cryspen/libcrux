// XXX: Can't do no_std
// #![no_std]

pub mod rust_simd;

pub type Sha3_224Digest = [u8; 28];
pub type Sha3_256Digest = [u8; 32];
pub type Sha3_384Digest = [u8; 48];
pub type Sha3_512Digest = [u8; 64];

/// The Digest Algorithm.
#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u32)]
pub enum Algorithm {
    Sha3_224 = 1,
    Sha3_256 = 2,
    Sha3_384 = 3,
    Sha3_512 = 4,
}

impl From<u32> for Algorithm {
    fn from(v: u32) -> Algorithm {
        match v {
            1 => Algorithm::Sha3_224,
            2 => Algorithm::Sha3_256,
            3 => Algorithm::Sha3_384,
            4 => Algorithm::Sha3_512,
            _ => panic!("Unknown Digest mode {}", v),
        }
    }
}

impl From<Algorithm> for u32 {
    fn from(v: Algorithm) -> u32 {
        match v {
            Algorithm::Sha3_224 => 1,
            Algorithm::Sha3_256 => 2,
            Algorithm::Sha3_384 => 3,
            Algorithm::Sha3_512 => 4,
        }
    }
}

/// Returns the output size of a digest.
pub const fn digest_size(mode: Algorithm) -> usize {
    match mode {
        Algorithm::Sha3_224 => 28,
        Algorithm::Sha3_256 => 32,
        Algorithm::Sha3_384 => 48,
        Algorithm::Sha3_512 => 64,
    }
}

// /// SHA3
// pub fn hash<const LEN: usize>(algorithm: Algorithm, payload: &[u8]) -> [u8; LEN] {
//     debug_assert!(payload.len() <= u32::MAX as usize);

//     let mut out = [0u8; LEN];
//     match algorithm {
//         Algorithm::Sha3_224 => sha224_ema(&mut out, payload),
//         Algorithm::Sha3_256 => sha256_ema(&mut out, payload),
//         Algorithm::Sha3_384 => sha384_ema(&mut out, payload),
//         Algorithm::Sha3_512 => sha512_ema(&mut out, payload),
//     }
//     out
// }

/// SHA3 224
#[inline(always)]
pub fn sha224(data: &[u8]) -> [u8; 28] {
    rust_simd::sha3_224(data)
}

// /// SHA3 224
// #[inline(always)]
// pub fn sha224_ema(digest: &mut [u8], payload: &[u8]) {
//     debug_assert!(payload.len() <= u32::MAX as usize);
//     debug_assert!(digest.len() == 28);

//     unsafe {
//         Hacl_Hash_SHA3_sha3_224(
//             digest.as_mut_ptr(),
//             payload.as_ptr() as _,
//             payload.len().try_into().unwrap(),
//         );
//     }
// }

/// SHA3 256
#[inline(always)]
pub fn sha256(data: &[u8]) -> [u8; 32] {
    rust_simd::sha3_256(data)
}

// /// SHA3 256
// #[inline(always)]
// pub fn sha256_ema(digest: &mut [u8], payload: &[u8]) {
//     debug_assert!(payload.len() <= u32::MAX as usize);
//     debug_assert!(digest.len() == 32);

//     unsafe {
//         Hacl_Hash_SHA3_sha3_256(
//             digest.as_mut_ptr(),
//             payload.as_ptr() as _,
//             payload.len().try_into().unwrap(),
//         );
//     }
// }

/// SHA3 384
#[inline(always)]
pub fn sha384(data: &[u8]) -> [u8; 48] {
    rust_simd::sha3_384(data)
}

// /// SHA3 384
// #[inline(always)]
// pub fn sha384_ema(digest: &mut [u8], payload: &[u8]) {
//     debug_assert!(payload.len() <= u32::MAX as usize);
//     debug_assert!(digest.len() == 48);

//     unsafe {
//         Hacl_Hash_SHA3_sha3_384(
//             digest.as_mut_ptr(),
//             payload.as_ptr() as _,
//             payload.len().try_into().unwrap(),
//         );
//     }
// }

/// SHA3 512
#[inline(always)]
pub fn sha512(data: &[u8]) -> [u8; 64] {
    rust_simd::sha3_512(data)
}

// /// SHA3 512
// #[inline(always)]
// pub fn sha512_ema(digest: &mut [u8], payload: &[u8]) {
//     debug_assert!(payload.len() <= u32::MAX as usize);
//     debug_assert!(digest.len() == 64);

//     unsafe {
//         Hacl_Hash_SHA3_sha3_512(
//             digest.as_mut_ptr(),
//             payload.as_ptr() as _,
//             payload.len().try_into().unwrap(),
//         );
//     }
// }

/// SHAKE 128
#[inline(always)]
pub fn shake128<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    rust_simd::shake128(data)
}

/// SHAKE 256
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake256<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    rust_simd::shake256(data)
}
