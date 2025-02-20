//! This module provides a specification-friendly bit vector type.
use super::bit::{Bit, MachineInteger};
use super::funarr::FunArray;

// TODO: this module uses `u128/i128` as mathematic integers. We should use `hax_lib::int` or bigint.

use std::fmt::Formatter;

/// A fixed-size bit vector type.
///
/// `BitVec<N>` is a specification-friendly, fixed-length bit vector that internally
/// stores an array of [`Bit`] values, where each `Bit` represents a single binary digit (0 or 1).
///
/// This type provides several utility methods for constructing and converting bit vectors:
///
/// The [`Debug`] implementation for `BitVec` pretty-prints the bits in groups of eight,
/// making the bit pattern more human-readable. The type also implements indexing,
/// allowing for easy access to individual bits.
#[hax_lib::fstar::before("noeq")]
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct BitVec<const N: usize>(FunArray<N, Bit>);

/// Pretty prints a bit slice by group of 8
#[hax_lib::exclude]
fn bit_slice_to_string(bits: &[Bit]) -> String {
    bits.into_iter()
        .map(|bit| match bit {
            Bit::Zero => '0',
            Bit::One => '1',
        })
        .collect::<Vec<_>>()
        .chunks(8)
        .map(|bits| bits.into_iter().collect::<String>())
        .map(|s| format!("{s} "))
        .collect::<String>()
        .trim()
        .into()
}

#[hax_lib::exclude]
impl<const N: usize> core::fmt::Debug for BitVec<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", bit_slice_to_string(self.0.as_ref()))
    }
}

#[hax_lib::attributes]
impl<const N: usize> core::ops::Index<usize> for BitVec<N> {
    type Output = Bit;
    #[requires(index < N)]
    fn index(&self, index: usize) -> &Self::Output {
        &self.0.get(index)
    }
}

/// Convert a bit slice into an unsigned number.
#[hax_lib::exclude]
fn u64_int_from_bit_slice(bits: &[Bit]) -> u64 {
    bits.into_iter()
        .enumerate()
        .map(|(i, bit)| u64::from(bit.clone()) << i)
        .sum::<u64>()
}

/// Convert a bit slice into a machine integer of type `T`.
#[hax_lib::exclude]
fn int_from_bit_slice<T: TryFrom<i128> + MachineInteger + Copy>(bits: &[Bit]) -> T {
    debug_assert!(bits.len() <= T::BITS as usize);
    let result = if T::SIGNED {
        let is_negative = matches!(bits[T::BITS as usize - 1], Bit::One);
        let s = u64_int_from_bit_slice(&bits[0..T::BITS as usize - 1]) as i128;
        if is_negative {
            -s
        } else {
            s
        }
    } else {
        u64_int_from_bit_slice(bits) as i128
    };
    let Ok(n) = result.try_into() else {
        // Conversion must succeed as `result` is guaranteed to be in range due to the bit-length check.
        unreachable!()
    };
    n
}

// /// Convert a bit slice into a machine integer of type `T`.
// fn int_from_bit_funarray<const N: usize, T: TryFrom<i128> + MachineInteger + Copy>(
//     bits: FunArray<N, Bit>,
// ) -> T {
//     debug_assert!(N <= T::BITS as usize);
//     let result = if T::SIGNED {
//         let is_negative = matches!(bits[T::BITS as usize - 1], Bit::One);
//         // let s = u64_int_from_bit_slice(&bits[0..T::BITS as usize - 1]) as i128;
//         // let s = u64_int_from_bit_slice(&bits[0..T::BITS as usize - 1]) as i128;
//         if is_negative {
//             -s
//         } else {
//             s
//         }
//     } else {
//         u64_int_from_bit_slice(bits) as i128
//     };
//     let Ok(n) = result.try_into() else {
//         // Conversion must succeed as `result` is guaranteed to be in range due to the bit-length check.
//         unreachable!()
//     };
//     n
// }

#[hax_lib::fstar::replace(
    r"
let ${BitVec::<0>::from_fn::<fn(usize)->Bit>}
    (v_N: usize)
    (f: (i: usize {v i < v v_N}) -> $:{Bit})
    : t_BitVec v_N = 
    ${BitVec::<0>}(${FunArray::<0,()>::from_fn::<fn(usize)->()>} v_N f)
"
)]
const _: () = ();

// impl<const N: usize> BitVec<N> {
//     #[hax_lib::fstar::replace_body("HEEEYYY")]
//     pub fn to_funarray<const M: usize, T: TryFrom<i128> + MachineInteger + Copy>(
//         &self,
//     ) -> FunArray<M, T> {
//         todo!()
//     }
// }

#[hax_lib::exclude]
impl<const N: usize> BitVec<N> {
    /// Constructor for BitVec. `BitVec::<N>::from_fn` constructs a bitvector out of a function that takes usizes smaller than `N` and produces bits.
    pub fn from_fn<F: Fn(usize) -> Bit>(f: F) -> Self {
        Self(FunArray::from_fn(f))
    }
    /// Convert a slice of machine integers where only the `d` least significant bits are relevant.
    pub fn from_slice<T: Into<i128> + MachineInteger + Copy>(x: &[T], d: usize) -> Self {
        Self::from_fn(|i| Bit::of_int(x[i / d], (i % d) as u32))
    }

    /// Construct a BitVec out of a machine integer.
    pub fn from_int<T: Into<i128> + MachineInteger + Copy>(n: T) -> Self {
        Self::from_slice(&[n.into()], T::BITS as usize)
    }

    /// Convert a BitVec into a machine integer of type `T`.
    pub fn to_int<T: TryFrom<i128> + MachineInteger + Copy>(self) -> T {
        int_from_bit_slice(self.0.as_ref())
    }

    /// Convert a BitVec into a vector of machine integers of type `T`.
    pub fn to_vec<T: TryFrom<i128> + MachineInteger + Copy>(&self) -> Vec<T> {
        self.0
            .as_ref()
            .chunks(T::BITS as usize)
            .map(int_from_bit_slice)
            .collect()
    }

    /// Generate a random BitVec.
    pub fn rand() -> Self {
        use rand::prelude::*;
        let random_source: [bool; N] = {
            let mut rng = rand::rng();
            core::array::from_fn(|_| rng.random::<bool>())
        };
        Self::from_fn(|i| random_source[i].into())
    }
}
