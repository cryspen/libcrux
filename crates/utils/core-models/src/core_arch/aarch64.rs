//! A (partial) Rust-based model of [`core::arch::aarch64`].
//!
//! This module provides a purely Rust implementation of selected operations from
//! `core::arch::aarch64` (ARM64 NEON intrinsics).
//!
//! # Design
//!
//! Similar to the x86 models, ARM64 SIMD vector types are modeled using `BitVec`:
//! - 128-bit vectors (`int16x8_t`, `uint32x4_t`, etc.) → `BitVec<128>`
//! - 64-bit vectors (`int16x4_t`, `uint16x4_t`, etc.) → `BitVec<64>`
//!
//! All intrinsics are modeled with exact type signatures matching `core::arch::aarch64`.

#![allow(clippy::too_many_arguments)]
#![allow(non_camel_case_types)]

use crate::abstractions::{bit::*, bitvec::*};

pub(crate) mod upstream {
    #[cfg(target_arch = "aarch64")]
    pub use core::arch::aarch64::*;
}

// ============================================================================
// Type Definitions
// ============================================================================

/// 128-bit vector of 8 signed 16-bit integers.
pub type int16x8_t = BitVec<128>;

/// 64-bit vector of 4 signed 16-bit integers.
pub type int16x4_t = BitVec<64>;

/// 128-bit vector of 4 signed 32-bit integers.
pub type int32x4_t = BitVec<128>;

/// 128-bit vector of 2 signed 64-bit integers.
pub type int64x2_t = BitVec<128>;

/// 128-bit vector of 16 unsigned 8-bit integers.
pub type uint8x16_t = BitVec<128>;

/// 128-bit vector of 8 unsigned 16-bit integers.
pub type uint16x8_t = BitVec<128>;

/// 64-bit vector of 4 unsigned 16-bit integers.
pub type uint16x4_t = BitVec<64>;

/// 128-bit vector of 4 unsigned 32-bit integers.
pub type uint32x4_t = BitVec<128>;

/// 128-bit vector of 2 unsigned 64-bit integers.
pub type uint64x2_t = BitVec<128>;

/// 64-bit vector of 2 unsigned 32-bit integers.
pub type uint32x2_t = BitVec<64>;

/// Polynomial type for carryless multiplication.
pub type poly64_t = u64;
pub type poly64x1_t = BitVec<64>;
pub type poly128_t = u128;

// ============================================================================
// Conversions (for testing against upstream)
// ============================================================================

#[hax_lib::exclude]
#[cfg(target_arch = "aarch64")]
mod conversions {
    use super::*;
    use super::upstream;

    // Helper to convert Vec<u8> to fixed array
    fn vec_to_array_16(v: Vec<u8>) -> [u8; 16] {
        v.try_into().unwrap()
    }

    fn vec_to_array_8(v: Vec<u8>) -> [u8; 8] {
        v.try_into().unwrap()
    }

    impl From<BitVec<128>> for upstream::int16x8_t {
        fn from(bv: BitVec<128>) -> upstream::int16x8_t {
            let bytes: [u8; 16] = vec_to_array_16(bv.to_vec());
            unsafe { upstream::vld1q_s16(bytes.as_ptr() as *const i16) }
        }
    }

    impl From<upstream::int16x8_t> for BitVec<128> {
        fn from(v: upstream::int16x8_t) -> BitVec<128> {
            let mut bytes = [0u8; 16];
            unsafe { upstream::vst1q_s16(bytes.as_mut_ptr() as *mut i16, v) };
            BitVec::from_slice(&bytes, 8)
        }
    }

    impl From<BitVec<128>> for upstream::uint8x16_t {
        fn from(bv: BitVec<128>) -> upstream::uint8x16_t {
            let bytes: [u8; 16] = vec_to_array_16(bv.to_vec());
            unsafe { upstream::vld1q_u8(bytes.as_ptr()) }
        }
    }

    impl From<upstream::uint8x16_t> for BitVec<128> {
        fn from(v: upstream::uint8x16_t) -> BitVec<128> {
            let mut bytes = [0u8; 16];
            unsafe { upstream::vst1q_u8(bytes.as_mut_ptr(), v) };
            BitVec::from_slice(&bytes, 8)
        }
    }

    impl From<BitVec<128>> for upstream::uint16x8_t {
        fn from(bv: BitVec<128>) -> upstream::uint16x8_t {
            let bytes: [u8; 16] = vec_to_array_16(bv.to_vec());
            unsafe { upstream::vld1q_u16(bytes.as_ptr() as *const u16) }
        }
    }

    impl From<upstream::uint16x8_t> for BitVec<128> {
        fn from(v: upstream::uint16x8_t) -> BitVec<128> {
            let mut bytes = [0u8; 16];
            unsafe { upstream::vst1q_u16(bytes.as_mut_ptr() as *mut u16, v) };
            BitVec::from_slice(&bytes, 8)
        }
    }

    impl From<BitVec<128>> for upstream::int32x4_t {
        fn from(bv: BitVec<128>) -> upstream::int32x4_t {
            let bytes: [u8; 16] = vec_to_array_16(bv.to_vec());
            unsafe { upstream::vld1q_s32(bytes.as_ptr() as *const i32) }
        }
    }

    impl From<upstream::int32x4_t> for BitVec<128> {
        fn from(v: upstream::int32x4_t) -> BitVec<128> {
            let mut bytes = [0u8; 16];
            unsafe { upstream::vst1q_s32(bytes.as_mut_ptr() as *mut i32, v) };
            BitVec::from_slice(&bytes, 8)
        }
    }

    impl From<BitVec<128>> for upstream::uint32x4_t {
        fn from(bv: BitVec<128>) -> upstream::uint32x4_t {
            let bytes: [u8; 16] = vec_to_array_16(bv.to_vec());
            unsafe { upstream::vld1q_u32(bytes.as_ptr() as *const u32) }
        }
    }

    impl From<upstream::uint32x4_t> for BitVec<128> {
        fn from(v: upstream::uint32x4_t) -> BitVec<128> {
            let mut bytes = [0u8; 16];
            unsafe { upstream::vst1q_u32(bytes.as_mut_ptr() as *mut u32, v) };
            BitVec::from_slice(&bytes, 8)
        }
    }

    impl From<BitVec<128>> for upstream::int64x2_t {
        fn from(bv: BitVec<128>) -> upstream::int64x2_t {
            let bytes: [u8; 16] = vec_to_array_16(bv.to_vec());
            unsafe { upstream::vld1q_s64(bytes.as_ptr() as *const i64) }
        }
    }

    impl From<upstream::int64x2_t> for BitVec<128> {
        fn from(v: upstream::int64x2_t) -> BitVec<128> {
            let mut bytes = [0u8; 16];
            unsafe { upstream::vst1q_s64(bytes.as_mut_ptr() as *mut i64, v) };
            BitVec::from_slice(&bytes, 8)
        }
    }

    impl From<BitVec<128>> for upstream::uint64x2_t {
        fn from(bv: BitVec<128>) -> upstream::uint64x2_t {
            let bytes: [u8; 16] = vec_to_array_16(bv.to_vec());
            unsafe { upstream::vld1q_u64(bytes.as_ptr() as *const u64) }
        }
    }

    impl From<upstream::uint64x2_t> for BitVec<128> {
        fn from(v: upstream::uint64x2_t) -> BitVec<128> {
            let mut bytes = [0u8; 16];
            unsafe { upstream::vst1q_u64(bytes.as_mut_ptr() as *mut u64, v) };
            BitVec::from_slice(&bytes, 8)
        }
    }

    impl From<BitVec<64>> for upstream::int16x4_t {
        fn from(bv: BitVec<64>) -> upstream::int16x4_t {
            let bytes: [u8; 8] = vec_to_array_8(bv.to_vec());
            unsafe { upstream::vld1_s16(bytes.as_ptr() as *const i16) }
        }
    }

    impl From<upstream::int16x4_t> for BitVec<64> {
        fn from(v: upstream::int16x4_t) -> BitVec<64> {
            let mut bytes = [0u8; 8];
            unsafe { upstream::vst1_s16(bytes.as_mut_ptr() as *mut i16, v) };
            BitVec::from_slice(&bytes, 8)
        }
    }

    impl From<BitVec<64>> for upstream::uint16x4_t {
        fn from(bv: BitVec<64>) -> upstream::uint16x4_t {
            let bytes: [u8; 8] = vec_to_array_8(bv.to_vec());
            unsafe { upstream::vld1_u16(bytes.as_ptr() as *const u16) }
        }
    }

    impl From<upstream::uint16x4_t> for BitVec<64> {
        fn from(v: upstream::uint16x4_t) -> BitVec<64> {
            let mut bytes = [0u8; 8];
            unsafe { upstream::vst1_u16(bytes.as_mut_ptr() as *mut u16, v) };
            BitVec::from_slice(&bytes, 8)
        }
    }
}

// ============================================================================
// Duplicate (broadcast) intrinsics
// ============================================================================

pub use dup::*;
pub mod dup {
    use super::*;

    /// Duplicate scalar to all lanes of vector.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vdupq_n_s16.html)
    #[hax_lib::opaque]
    pub fn vdupq_n_s16(value: i16) -> int16x8_t {
        BitVec::from_fn(|i| Bit::of_int(value, (i % 16) as u32))
    }

    /// Duplicate scalar to all lanes of vector.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vdupq_n_u16.html)
    #[hax_lib::opaque]
    pub fn vdupq_n_u16(value: u16) -> uint16x8_t {
        BitVec::from_fn(|i| Bit::of_int(value, (i % 16) as u32))
    }

    /// Duplicate scalar to all lanes of vector.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vdupq_n_u32.html)
    #[hax_lib::opaque]
    pub fn vdupq_n_u32(value: u32) -> uint32x4_t {
        BitVec::from_fn(|i| Bit::of_int(value, (i % 32) as u32))
    }

    /// Duplicate scalar to all lanes of vector.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vdupq_n_u64.html)
    #[hax_lib::opaque]
    pub fn vdupq_n_u64(value: u64) -> uint64x2_t {
        BitVec::from_fn(|i| Bit::of_int(value, (i % 64) as u32))
    }

    /// Duplicate scalar to all lanes of vector.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vdupq_n_u8.html)
    #[hax_lib::opaque]
    pub fn vdupq_n_u8(value: u8) -> uint8x16_t {
        BitVec::from_fn(|i| Bit::of_int(value, (i % 8) as u32))
    }

    /// Duplicate vector element to all lanes.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vdupq_laneq_u32.html)
    #[hax_lib::opaque]
    pub fn vdupq_laneq_u32<const N: i32>(a: uint32x4_t) -> uint32x4_t {
        let start = (N as u64) * 32;
        BitVec::from_fn(|i| a[start + (i % 32)])
    }
}

// ============================================================================
// Load intrinsics
// ============================================================================

pub use load::*;
pub mod load {
    use super::*;

    /// Load 128-bit vector from memory.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vld1q_s16.html)
    #[hax_lib::exclude]
    pub unsafe fn vld1q_s16(_ptr: *const i16) -> int16x8_t {
        unimplemented!()
    }

    /// Load 128-bit vector from memory.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vld1q_u8.html)
    #[hax_lib::exclude]
    pub unsafe fn vld1q_u8(_ptr: *const u8) -> uint8x16_t {
        unimplemented!()
    }

    /// Load 128-bit vector from memory.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vld1q_u16.html)
    #[hax_lib::exclude]
    pub unsafe fn vld1q_u16(_ptr: *const u16) -> uint16x8_t {
        unimplemented!()
    }

    /// Load 128-bit vector from memory.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vld1q_u32.html)
    #[hax_lib::exclude]
    pub unsafe fn vld1q_u32(_ptr: *const u32) -> uint32x4_t {
        unimplemented!()
    }

    /// Load 128-bit vector from memory.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vld1q_u64.html)
    #[hax_lib::exclude]
    pub unsafe fn vld1q_u64(_ptr: *const u64) -> uint64x2_t {
        unimplemented!()
    }
}

// ============================================================================
// Store intrinsics
// ============================================================================

pub use store::*;
pub mod store {
    use super::*;

    /// Store 128-bit vector to memory.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vst1q_s16.html)
    #[hax_lib::exclude]
    pub unsafe fn vst1q_s16(_ptr: *mut i16, _a: int16x8_t) {
        unimplemented!()
    }

    /// Store 128-bit vector to memory.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vst1q_u8.html)
    #[hax_lib::exclude]
    pub unsafe fn vst1q_u8(_ptr: *mut u8, _a: uint8x16_t) {
        unimplemented!()
    }

    /// Store 128-bit vector to memory.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vst1q_u64.html)
    #[hax_lib::exclude]
    pub unsafe fn vst1q_u64(_ptr: *mut u64, _a: uint64x2_t) {
        unimplemented!()
    }
}

// ============================================================================
// Arithmetic intrinsics
// ============================================================================

pub use arithmetic::*;
pub mod arithmetic {
    use super::*;

    /// Add (vector).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vaddq_s16.html)
    #[hax_lib::opaque]
    pub fn vaddq_s16(_a: int16x8_t, _b: int16x8_t) -> int16x8_t {
        unimplemented!()
    }

    /// Add (vector).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vaddq_u32.html)
    #[hax_lib::opaque]
    pub fn vaddq_u32(_a: uint32x4_t, _b: uint32x4_t) -> uint32x4_t {
        unimplemented!()
    }

    /// Subtract (vector).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vsubq_s16.html)
    #[hax_lib::opaque]
    pub fn vsubq_s16(_a: int16x8_t, _b: int16x8_t) -> int16x8_t {
        unimplemented!()
    }

    /// Multiply by scalar.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vmulq_n_s16.html)
    #[hax_lib::opaque]
    pub fn vmulq_n_s16(_a: int16x8_t, _b: i16) -> int16x8_t {
        unimplemented!()
    }

    /// Multiply by scalar.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vmulq_n_u16.html)
    #[hax_lib::opaque]
    pub fn vmulq_n_u16(_a: uint16x8_t, _b: u16) -> uint16x8_t {
        unimplemented!()
    }

    /// Multiply by scalar.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vmulq_n_u32.html)
    #[hax_lib::opaque]
    pub fn vmulq_n_u32(_a: uint32x4_t, _b: u32) -> uint32x4_t {
        unimplemented!()
    }

    /// Multiply (vector).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vmulq_s16.html)
    #[hax_lib::opaque]
    pub fn vmulq_s16(_a: int16x8_t, _b: int16x8_t) -> int16x8_t {
        unimplemented!()
    }

    /// Signed saturating doubling multiply returning high half.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vqdmulhq_n_s16.html)
    #[hax_lib::opaque]
    pub fn vqdmulhq_n_s16(_a: int16x8_t, _b: i16) -> int16x8_t {
        unimplemented!()
    }

    /// Signed saturating doubling multiply returning high half.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vqdmulhq_s16.html)
    #[hax_lib::opaque]
    pub fn vqdmulhq_s16(_a: int16x8_t, _b: int16x8_t) -> int16x8_t {
        unimplemented!()
    }

    /// Signed saturating doubling multiply returning high half.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vqdmulhq_n_s32.html)
    #[hax_lib::opaque]
    pub fn vqdmulhq_n_s32(_a: int32x4_t, _b: i32) -> int32x4_t {
        unimplemented!()
    }

    /// Signed multiply long (vector, by element).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vmull_s16.html)
    #[hax_lib::opaque]
    pub fn vmull_s16(_a: int16x4_t, _b: int16x4_t) -> int32x4_t {
        unimplemented!()
    }

    /// Signed multiply long (upper half).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vmull_high_s16.html)
    #[hax_lib::opaque]
    pub fn vmull_high_s16(_a: int16x8_t, _b: int16x8_t) -> int32x4_t {
        unimplemented!()
    }

    /// Signed multiply-accumulate long (vector, by element).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vmlal_s16.html)
    #[hax_lib::opaque]
    pub fn vmlal_s16(_a: int32x4_t, _b: int16x4_t, _c: int16x4_t) -> int32x4_t {
        unimplemented!()
    }

    /// Signed multiply-accumulate long (upper half).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vmlal_high_s16.html)
    #[hax_lib::opaque]
    pub fn vmlal_high_s16(_a: int32x4_t, _b: int16x8_t, _c: int16x8_t) -> int32x4_t {
        unimplemented!()
    }

    /// Add across vector (horizontal add).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vaddv_u16.html)
    #[hax_lib::opaque]
    pub fn vaddv_u16(_a: uint16x4_t) -> u16 {
        unimplemented!()
    }

    /// Add across vector (horizontal add).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vaddvq_s16.html)
    #[hax_lib::opaque]
    pub fn vaddvq_s16(_a: int16x8_t) -> i16 {
        unimplemented!()
    }

    /// Add across vector (horizontal add).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vaddvq_u16.html)
    #[hax_lib::opaque]
    pub fn vaddvq_u16(_a: uint16x8_t) -> u16 {
        unimplemented!()
    }
}

// ============================================================================
// Shift intrinsics
// ============================================================================

pub use shift::*;
pub mod shift {
    use super::*;

    /// Shift right (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshrq_n_s16.html)
    #[hax_lib::opaque]
    pub fn vshrq_n_s16<const N: i32>(_a: int16x8_t) -> int16x8_t {
        unimplemented!()
    }

    /// Shift right (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshrq_n_u16.html)
    #[hax_lib::opaque]
    pub fn vshrq_n_u16<const N: i32>(_a: uint16x8_t) -> uint16x8_t {
        unimplemented!()
    }

    /// Shift right (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshrq_n_u32.html)
    #[hax_lib::opaque]
    pub fn vshrq_n_u32<const N: i32>(_a: uint32x4_t) -> uint32x4_t {
        unimplemented!()
    }

    /// Shift right (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshrq_n_u64.html)
    #[hax_lib::opaque]
    pub fn vshrq_n_u64<const N: i32>(_a: uint64x2_t) -> uint64x2_t {
        unimplemented!()
    }

    /// Shift left (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshlq_n_s16.html)
    #[hax_lib::opaque]
    pub fn vshlq_n_s16<const N: i32>(_a: int16x8_t) -> int16x8_t {
        unimplemented!()
    }

    /// Shift left (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshlq_n_u32.html)
    #[hax_lib::opaque]
    pub fn vshlq_n_u32<const N: i32>(_a: uint32x4_t) -> uint32x4_t {
        unimplemented!()
    }

    /// Shift left (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshlq_n_u64.html)
    #[hax_lib::opaque]
    pub fn vshlq_n_u64<const N: i32>(_a: uint64x2_t) -> uint64x2_t {
        unimplemented!()
    }

    /// Shift left (register).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshlq_s16.html)
    #[hax_lib::opaque]
    pub fn vshlq_s16(_a: int16x8_t, _b: int16x8_t) -> int16x8_t {
        unimplemented!()
    }

    /// Shift left (register).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vshlq_u16.html)
    #[hax_lib::opaque]
    pub fn vshlq_u16(_a: uint16x8_t, _b: int16x8_t) -> uint16x8_t {
        unimplemented!()
    }

    /// Shift left and insert (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vsliq_n_s32.html)
    #[hax_lib::opaque]
    pub fn vsliq_n_s32<const N: i32>(_a: int32x4_t, _b: int32x4_t) -> int32x4_t {
        unimplemented!()
    }

    /// Shift left and insert (immediate).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vsliq_n_s64.html)
    #[hax_lib::opaque]
    pub fn vsliq_n_s64<const N: i32>(_a: int64x2_t, _b: int64x2_t) -> int64x2_t {
        unimplemented!()
    }
}

// ============================================================================
// Comparison intrinsics
// ============================================================================

pub use compare::*;
pub mod compare {
    use super::*;

    /// Compare greater than or equal.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vcgeq_s16.html)
    #[hax_lib::opaque]
    pub fn vcgeq_s16(_a: int16x8_t, _b: int16x8_t) -> uint16x8_t {
        unimplemented!()
    }

    /// Compare less than or equal.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vcleq_s16.html)
    #[hax_lib::opaque]
    pub fn vcleq_s16(_a: int16x8_t, _b: int16x8_t) -> uint16x8_t {
        unimplemented!()
    }
}

// ============================================================================
// Logical intrinsics
// ============================================================================

pub use logical::*;
pub mod logical {
    use super::*;

    /// Bitwise AND.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vandq_s16.html)
    #[hax_lib::opaque]
    pub fn vandq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
        BitVec::from_fn(|i| match (a[i], b[i]) {
            (Bit::One, Bit::One) => Bit::One,
            _ => Bit::Zero,
        })
    }

    /// Bitwise AND.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vandq_u16.html)
    #[hax_lib::opaque]
    pub fn vandq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
        BitVec::from_fn(|i| match (a[i], b[i]) {
            (Bit::One, Bit::One) => Bit::One,
            _ => Bit::Zero,
        })
    }

    /// Bitwise AND.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vandq_u32.html)
    #[hax_lib::opaque]
    pub fn vandq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        BitVec::from_fn(|i| match (a[i], b[i]) {
            (Bit::One, Bit::One) => Bit::One,
            _ => Bit::Zero,
        })
    }

    /// Bitwise clear (AND NOT).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vbicq_u64.html)
    #[hax_lib::opaque]
    pub fn vbicq_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        BitVec::from_fn(|i| match (a[i], b[i]) {
            (Bit::One, Bit::Zero) => Bit::One,
            _ => Bit::Zero,
        })
    }

    /// Bitwise exclusive OR.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.veorq_s16.html)
    #[hax_lib::opaque]
    pub fn veorq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
        BitVec::from_fn(|i| match (a[i], b[i]) {
            (Bit::Zero, Bit::Zero) | (Bit::One, Bit::One) => Bit::Zero,
            _ => Bit::One,
        })
    }

    /// Bitwise exclusive OR.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.veorq_u8.html)
    #[hax_lib::opaque]
    pub fn veorq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        BitVec::from_fn(|i| match (a[i], b[i]) {
            (Bit::Zero, Bit::Zero) | (Bit::One, Bit::One) => Bit::Zero,
            _ => Bit::One,
        })
    }

    /// Bitwise exclusive OR.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.veorq_u32.html)
    #[hax_lib::opaque]
    pub fn veorq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        BitVec::from_fn(|i| match (a[i], b[i]) {
            (Bit::Zero, Bit::Zero) | (Bit::One, Bit::One) => Bit::Zero,
            _ => Bit::One,
        })
    }

    /// Bitwise exclusive OR.
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.veorq_u64.html)
    #[hax_lib::opaque]
    pub fn veorq_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        BitVec::from_fn(|i| match (a[i], b[i]) {
            (Bit::Zero, Bit::Zero) | (Bit::One, Bit::One) => Bit::Zero,
            _ => Bit::One,
        })
    }
}

// ============================================================================
// Reinterpret cast intrinsics
// ============================================================================

pub use reinterpret::*;
pub mod reinterpret {
    use super::*;

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s16_u16.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s16_u16(a: uint16x8_t) -> int16x8_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_u16_s16.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_u16_s16(a: int16x8_t) -> uint16x8_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s32_u32.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s32_u32(a: uint32x4_t) -> int32x4_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_u32_s32.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_u32_s32(a: int32x4_t) -> uint32x4_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_u8_s16.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_u8_s16(a: int16x8_t) -> uint8x16_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s16_u8.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s16_u8(a: uint8x16_t) -> int16x8_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_u32_s16.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_u32_s16(a: int16x8_t) -> uint32x4_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s16_u32.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s16_u32(a: uint32x4_t) -> int16x8_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s16_s32.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s16_s32(a: int32x4_t) -> int16x8_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s32_s16.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s32_s16(a: int16x8_t) -> int32x4_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s16_s64.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s16_s64(a: int64x2_t) -> int16x8_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s64_s16.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s64_s16(a: int16x8_t) -> int64x2_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_s64_s32.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_s64_s32(a: int32x4_t) -> int64x2_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_u8_s64.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_u8_s64(a: int64x2_t) -> uint8x16_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_u32_u8.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_u32_u8(a: uint8x16_t) -> uint32x4_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_u8_u32.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_u8_u32(a: uint32x4_t) -> uint8x16_t {
        a
    }

    /// Reinterpret cast (no-op on bits).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vreinterpretq_u16_u8.html)
    #[hax_lib::opaque]
    pub fn vreinterpretq_u16_u8(a: uint8x16_t) -> uint16x8_t {
        a
    }
}

// ============================================================================
// Transpose / Permute intrinsics
// ============================================================================

pub use transpose::*;
pub mod transpose {
    use super::*;

    /// Transpose vectors (primary, 16-bit).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vtrn1q_s16.html)
    #[hax_lib::opaque]
    pub fn vtrn1q_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
        // Interleave even elements: a[0], b[0], a[2], b[2], a[4], b[4], a[6], b[6]
        BitVec::from_fn(|i| {
            let lane = i / 16;
            let bit_in_lane = i % 16;
            let src_lane = (lane / 2) * 2; // 0, 0, 2, 2, 4, 4, 6, 6
            if lane % 2 == 0 {
                a[src_lane * 16 + bit_in_lane]
            } else {
                b[src_lane * 16 + bit_in_lane]
            }
        })
    }

    /// Transpose vectors (secondary, 16-bit).
    /// [Rust Documentation](https://doc.rust-lang.org/core/arch/aarch64/fn.vtrn2q_s16.html)
    #[hax_lib::opaque]
    pub fn vtrn2q_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
        // Interleave odd elements: a[1], b[1], a[3], b[3], a[5], b[5], a[7], b[7]
        BitVec::from_fn(|i| {
            let lane = i / 16;
            let bit_in_lane = i % 16;
            let src_lane = (lane / 2) * 2 + 1; // 1, 1, 3, 3, 5, 5, 7, 7
            if lane % 2 == 0 {
                a[src_lane * 16 + bit_in_lane]
            } else {
                b[src_lane * 16 + bit_in_lane]
            }
        })
    }

    /// Transpose vectors (primary, 32-bit).
    #[hax_lib::opaque]
    pub fn vtrn1q_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
        // a[0], b[0], a[2], b[2]
        BitVec::from_fn(|i| {
            let lane = i / 32;
            let bit_in_lane = i % 32;
            let src_lane = (lane / 2) * 2;
            if lane % 2 == 0 {
                a[src_lane * 32 + bit_in_lane]
            } else {
                b[src_lane * 32 + bit_in_lane]
            }
        })
    }

    /// Transpose vectors (secondary, 32-bit).
    #[hax_lib::opaque]
    pub fn vtrn2q_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
        // a[1], b[1], a[3], b[3]
        BitVec::from_fn(|i| {
            let lane = i / 32;
            let bit_in_lane = i % 32;
            let src_lane = (lane / 2) * 2 + 1;
            if lane % 2 == 0 {
                a[src_lane * 32 + bit_in_lane]
            } else {
                b[src_lane * 32 + bit_in_lane]
            }
        })
    }

    /// Transpose vectors (primary, 64-bit).
    #[hax_lib::opaque]
    pub fn vtrn1q_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
        // a[0], b[0]
        BitVec::from_fn(|i| {
            let lane = i / 64;
            let bit_in_lane = i % 64;
            if lane == 0 {
                a[bit_in_lane]
            } else {
                b[bit_in_lane]
            }
        })
    }

    /// Transpose vectors (secondary, 64-bit).
    #[hax_lib::opaque]
    pub fn vtrn2q_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
        // a[1], b[1]
        BitVec::from_fn(|i| {
            let lane = i / 64;
            let bit_in_lane = i % 64;
            if lane == 0 {
                a[64 + bit_in_lane]
            } else {
                b[64 + bit_in_lane]
            }
        })
    }

    /// Transpose vectors (primary, 64-bit unsigned).
    #[hax_lib::opaque]
    pub fn vtrn1q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        BitVec::from_fn(|i| {
            let lane = i / 64;
            let bit_in_lane = i % 64;
            if lane == 0 {
                a[bit_in_lane]
            } else {
                b[bit_in_lane]
            }
        })
    }

    /// Transpose vectors (secondary, 64-bit unsigned).
    #[hax_lib::opaque]
    pub fn vtrn2q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        BitVec::from_fn(|i| {
            let lane = i / 64;
            let bit_in_lane = i % 64;
            if lane == 0 {
                a[64 + bit_in_lane]
            } else {
                b[64 + bit_in_lane]
            }
        })
    }

    /// Extract vector from pair of vectors.
    #[hax_lib::opaque]
    pub fn vextq_u32<const N: i32>(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let n = N as u64;
        BitVec::from_fn(|i| {
            let total_bit = n * 32 + i as u64;
            if total_bit < 128 {
                a[total_bit]
            } else {
                b[total_bit - 128]
            }
        })
    }
}

// ============================================================================
// Get lane / Extract intrinsics
// ============================================================================

pub use extract::*;
pub mod extract {
    use super::*;

    /// Get low 64 bits of 128-bit vector.
    #[hax_lib::opaque]
    pub fn vget_low_s16(a: int16x8_t) -> int16x4_t {
        BitVec::from_fn(|i| a[i])
    }

    /// Get low 64 bits of 128-bit vector.
    #[hax_lib::opaque]
    pub fn vget_low_u16(a: uint16x8_t) -> uint16x4_t {
        BitVec::from_fn(|i| a[i])
    }

    /// Get high 64 bits of 128-bit vector.
    #[hax_lib::opaque]
    pub fn vget_high_u16(a: uint16x8_t) -> uint16x4_t {
        BitVec::from_fn(|i| a[64 + i])
    }
}

// ============================================================================
// Table lookup intrinsics
// ============================================================================

pub use tbl::*;
pub mod tbl {
    use super::*;

    /// Table lookup (single table, 128-bit).
    #[hax_lib::opaque]
    pub fn vqtbl1q_u8(_t: uint8x16_t, _idx: uint8x16_t) -> uint8x16_t {
        unimplemented!()
    }
}

// ============================================================================
// SHA3 / Crypto intrinsics
// ============================================================================

pub use sha3::*;
pub mod sha3 {
    use super::*;
    use super::logical::{veorq_u64, vbicq_u64};

    /// Rotate and XOR.
    #[hax_lib::opaque]
    pub fn vrax1q_u64(_a: uint64x2_t, _b: uint64x2_t) -> uint64x2_t {
        unimplemented!()
    }

    /// Three-way XOR.
    #[hax_lib::opaque]
    pub fn veor3q_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
        // a XOR b XOR c
        let ab = veorq_u64(a, b);
        veorq_u64(ab, c)
    }

    /// XOR and rotate.
    #[hax_lib::opaque]
    pub fn vxarq_u64<const LEFT: i32, const RIGHT: i32>(_a: uint64x2_t, _b: uint64x2_t) -> uint64x2_t {
        unimplemented!()
    }

    /// Bit clear and XOR.
    #[hax_lib::opaque]
    pub fn vbcaxq_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
        // a XOR (b AND NOT c)
        let b_and_not_c = vbicq_u64(b, c);
        veorq_u64(a, b_and_not_c)
    }

    /// Polynomial multiply long.
    #[hax_lib::opaque]
    pub fn vmull_p64(_a: poly64_t, _b: poly64_t) -> poly128_t {
        unimplemented!()
    }
}

// ============================================================================
// AES intrinsics
// ============================================================================

pub use aes::*;
pub mod aes {
    use super::*;

    /// AES single round encryption.
    #[hax_lib::opaque]
    pub fn vaeseq_u8(_data: uint8x16_t, _key: uint8x16_t) -> uint8x16_t {
        unimplemented!()
    }

    /// AES mix columns.
    #[hax_lib::opaque]
    pub fn vaesmcq_u8(_data: uint8x16_t) -> uint8x16_t {
        unimplemented!()
    }
}

// ============================================================================
// Tests
// ============================================================================

/// Tests of equivalence between our models and `upstream::*` (core::arch::aarch64).
/// Each test runs 100 iterations with random inputs.
#[cfg(all(test, target_arch = "aarch64"))]
mod tests {
    use super::*;

    /// Number of random tests to run for each intrinsic
    const N: usize = 100;

    // ========================================================================
    // Duplicate (dup) intrinsics tests
    // ========================================================================

    #[test]
    fn test_vdupq_n_s16() {
        for _ in 0..N {
            let v: i16 = rand::random();
            let result = vdupq_n_s16(v);
            let expected: BitVec<128> = unsafe { upstream::vdupq_n_s16(v).into() };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vdupq_n_u16() {
        for _ in 0..N {
            let v: u16 = rand::random();
            let result = vdupq_n_u16(v);
            let expected: BitVec<128> = unsafe { upstream::vdupq_n_u16(v).into() };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vdupq_n_u32() {
        for _ in 0..N {
            let v: u32 = rand::random();
            let result = vdupq_n_u32(v);
            let expected: BitVec<128> = unsafe { upstream::vdupq_n_u32(v).into() };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vdupq_n_u64() {
        for _ in 0..N {
            let v: u64 = rand::random();
            let result = vdupq_n_u64(v);
            let expected: BitVec<128> = unsafe { upstream::vdupq_n_u64(v).into() };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vdupq_n_u8() {
        for _ in 0..N {
            let v: u8 = rand::random();
            let result = vdupq_n_u8(v);
            let expected: BitVec<128> = unsafe { upstream::vdupq_n_u8(v).into() };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vdupq_laneq_u32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            // Test all 4 lane indices
            let result0 = vdupq_laneq_u32::<0>(a);
            let expected0: BitVec<128> = unsafe { upstream::vdupq_laneq_u32::<0>(a.into()).into() };
            assert_eq!(result0, expected0);

            let result1 = vdupq_laneq_u32::<1>(a);
            let expected1: BitVec<128> = unsafe { upstream::vdupq_laneq_u32::<1>(a.into()).into() };
            assert_eq!(result1, expected1);

            let result2 = vdupq_laneq_u32::<2>(a);
            let expected2: BitVec<128> = unsafe { upstream::vdupq_laneq_u32::<2>(a.into()).into() };
            assert_eq!(result2, expected2);

            let result3 = vdupq_laneq_u32::<3>(a);
            let expected3: BitVec<128> = unsafe { upstream::vdupq_laneq_u32::<3>(a.into()).into() };
            assert_eq!(result3, expected3);
        }
    }

    // ========================================================================
    // Logical intrinsics tests
    // ========================================================================

    #[test]
    fn test_vandq_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vandq_s16(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vandq_s16(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vandq_u16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vandq_u16(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vandq_u16(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vandq_u32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vandq_u32(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vandq_u32(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vbicq_u64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vbicq_u64(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vbicq_u64(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_veorq_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = veorq_s16(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::veorq_s16(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_veorq_u8() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = veorq_u8(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::veorq_u8(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_veorq_u32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = veorq_u32(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::veorq_u32(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_veorq_u64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = veorq_u64(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::veorq_u64(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    // ========================================================================
    // Reinterpret cast intrinsics tests
    // ========================================================================

    #[test]
    fn test_vreinterpretq_s16_u16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s16_u16(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s16_u16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_u16_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_u16_s16(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_u16_s16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_s32_u32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s32_u32(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s32_u32(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_u32_s32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_u32_s32(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_u32_s32(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_u8_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_u8_s16(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_u8_s16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_s16_u8() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s16_u8(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s16_u8(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_u32_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_u32_s16(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_u32_s16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_s16_u32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s16_u32(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s16_u32(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_s16_s32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s16_s32(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s16_s32(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_s32_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s32_s16(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s32_s16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_s16_s64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s16_s64(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s16_s64(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_s64_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s64_s16(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s64_s16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_s64_s32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_s64_s32(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_s64_s32(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_u8_s64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_u8_s64(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_u8_s64(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_u32_u8() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_u32_u8(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_u32_u8(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_u8_u32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_u8_u32(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_u8_u32(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vreinterpretq_u16_u8() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vreinterpretq_u16_u8(a);
            let expected: BitVec<128> = unsafe {
                upstream::vreinterpretq_u16_u8(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    // ========================================================================
    // Transpose / Permute intrinsics tests
    // ========================================================================

    #[test]
    fn test_vtrn1q_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vtrn1q_s16(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vtrn1q_s16(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vtrn2q_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vtrn2q_s16(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vtrn2q_s16(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vtrn1q_s32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vtrn1q_s32(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vtrn1q_s32(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vtrn2q_s32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vtrn2q_s32(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vtrn2q_s32(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vtrn1q_s64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vtrn1q_s64(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vtrn1q_s64(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vtrn2q_s64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vtrn2q_s64(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vtrn2q_s64(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vtrn1q_u64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vtrn1q_u64(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vtrn1q_u64(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vtrn2q_u64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let result = vtrn2q_u64(a, b);
            let expected: BitVec<128> = unsafe {
                upstream::vtrn2q_u64(a.into(), b.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vextq_u32() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();

            // Test all 4 possible N values (0-3)
            let result0 = vextq_u32::<0>(a, b);
            let expected0: BitVec<128> = unsafe { upstream::vextq_u32::<0>(a.into(), b.into()).into() };
            assert_eq!(result0, expected0);

            let result1 = vextq_u32::<1>(a, b);
            let expected1: BitVec<128> = unsafe { upstream::vextq_u32::<1>(a.into(), b.into()).into() };
            assert_eq!(result1, expected1);

            let result2 = vextq_u32::<2>(a, b);
            let expected2: BitVec<128> = unsafe { upstream::vextq_u32::<2>(a.into(), b.into()).into() };
            assert_eq!(result2, expected2);

            let result3 = vextq_u32::<3>(a, b);
            let expected3: BitVec<128> = unsafe { upstream::vextq_u32::<3>(a.into(), b.into()).into() };
            assert_eq!(result3, expected3);
        }
    }

    // ========================================================================
    // Extract intrinsics tests
    // ========================================================================

    #[test]
    fn test_vget_low_s16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vget_low_s16(a);
            let expected: BitVec<64> = unsafe {
                upstream::vget_low_s16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vget_low_u16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vget_low_u16(a);
            let expected: BitVec<64> = unsafe {
                upstream::vget_low_u16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vget_high_u16() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let result = vget_high_u16(a);
            let expected: BitVec<64> = unsafe {
                upstream::vget_high_u16(a.into()).into()
            };
            assert_eq!(result, expected);
        }
    }

    // ========================================================================
    // SHA3 / Crypto intrinsics tests
    // ========================================================================

    #[test]
    fn test_veor3q_u64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let c: BitVec<128> = BitVec::rand();
            let result = veor3q_u64(a, b, c);
            // veor3q_u64 is a XOR b XOR c, test against manual computation
            let expected = veorq_u64(veorq_u64(a, b), c);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_vbcaxq_u64() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();
            let c: BitVec<128> = BitVec::rand();
            let result = vbcaxq_u64(a, b, c);
            // vbcaxq_u64 is a XOR (b AND NOT c), test against manual computation
            let expected = veorq_u64(a, vbicq_u64(b, c));
            assert_eq!(result, expected);
        }
    }
}
