// XXX: Can't do no_std
// #![no_std]

// Low* library code
mod lowstar;

// SHA3 plus helpers
mod hacl;
use crate::hacl::hash_sha3::{self, shake128_hacl, shake256_hacl};

/// A Sha3x4 API
pub mod x4;

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

/// SHA3
pub fn hash<const LEN: usize>(algorithm: Algorithm, payload: &[u8]) -> [u8; LEN] {
    debug_assert!(payload.len() <= u32::MAX as usize);
    let payload = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(payload.as_ptr() as *mut u8, payload.len()))
    };

    let mut out = [0u8; LEN];
    match algorithm {
        Algorithm::Sha3_224 => hash_sha3::sha3_224(&mut out, payload, payload.len() as u32),
        Algorithm::Sha3_256 => hash_sha3::sha3_256(&mut out, payload, payload.len() as u32),
        Algorithm::Sha3_384 => hash_sha3::sha3_384(&mut out, payload, payload.len() as u32),
        Algorithm::Sha3_512 => hash_sha3::sha3_512(&mut out, payload, payload.len() as u32),
    }
    out
}

/// SHA3 224
pub fn sha3_224(payload: &[u8]) -> Sha3_224Digest {
    debug_assert!(payload.len() <= u32::MAX as usize);
    let payload = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(payload.as_ptr() as *mut u8, payload.len()))
    };
    let mut out = [0u8; 28];

    hash_sha3::sha3_224(&mut out, payload, payload.len() as u32);

    out
}

/// SHA3 256
pub fn sha3_256(payload: &[u8]) -> Sha3_256Digest {
    debug_assert!(payload.len() <= u32::MAX as usize);
    let payload = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(payload.as_ptr() as *mut u8, payload.len()))
    };
    let mut out = [0u8; 32];

    hash_sha3::sha3_256(&mut out, payload, payload.len() as u32);

    out
}

/// SHA3 384
pub fn sha3_384(payload: &[u8]) -> Sha3_384Digest {
    debug_assert!(payload.len() <= u32::MAX as usize);
    let payload = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(payload.as_ptr() as *mut u8, payload.len()))
    };
    let mut out = [0u8; 48];

    hash_sha3::sha3_384(&mut out, payload, payload.len() as u32);

    out
}

/// SHA3 512
pub fn sha3_512(payload: &[u8]) -> Sha3_512Digest {
    debug_assert!(payload.len() <= u32::MAX as usize);
    let payload = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(payload.as_ptr() as *mut u8, payload.len()))
    };
    let mut out = [0u8; 64];

    hash_sha3::sha3_512(&mut out, payload, payload.len() as u32);

    out
}

/// SHAKE 128
///
/// The caller must define the size of the output in the return type.
pub fn shake128<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
    debug_assert!(LEN <= u32::MAX as usize && data.len() <= u32::MAX as usize);
    let data = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(data.as_ptr() as *mut u8, data.len()))
    };
    let mut out = [0u8; LEN];
    shake128_hacl(data.len() as u32, data, LEN as u32, &mut out);

    out
}

/// SHAKE 256
///
/// The caller must define the size of the output in the return type.
pub fn shake256<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
    debug_assert!(LEN <= u32::MAX as usize && data.len() <= u32::MAX as usize);
    let data = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(data.as_ptr() as *mut u8, data.len()))
    };
    let mut out = [0u8; LEN];
    shake256_hacl(data.len() as u32, data, LEN as u32, &mut out);

    out
}
