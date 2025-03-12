//! This module provides a specification-friendly bit vector type.
use super::bit::{Bit, MachineInteger};
use super::funarr::*;

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
pub struct BitVec<const N: u64>(FunArray<N, Bit>);

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
impl<const N: u64> core::fmt::Debug for BitVec<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", bit_slice_to_string(&self.0.as_vec()))
    }
}

#[hax_lib::attributes]
impl<const N: u64> core::ops::Index<u64> for BitVec<N> {
    type Output = Bit;
    #[requires(index < N)]
    fn index(&self, index: u64) -> &Self::Output {
        &self.0.get(index)
    }
}

// impl<const N: u64> FunArray<N, Bit> {
//     pub fn to_u64(self) -> u64 {
//         self.fold(0, |acc, n| (acc * 2) + u64::from(n))
//     }
//     pub fn log2(self) -> Option<u64> {
//         self.fold((0u64, None), |acc, n| {
//             let (position, acc) = acc;
//             (
//                 position + 1,
//                 match (acc, n) {
//                     // We have multiple `1`, this cannot be a power of 2
//                     (Some(_), Bit::One) => None,
//                     (None, Bit::One) => Some(position),
//                     (_, Bit::Zero) => acc,
//                 },
//             )
//         })
//         .1
//     }
// }

// #[cfg(hax)]
// use hax_lib::int::Abstraction;

// /// Convert a fun array of bits into an unsigned number.
// // #[cfg(hax)]
// fn math_int_from_fnarr_bit<const N: usize>(bits: FunArray<N, Bit>) -> hax_lib::Int {
//     bits.fold(hax_lib::int!(0), |acc, n| {
//         (acc * hax_lib::int!(2)) + u8::from(n).lift()
//     })
// }

// #[hax_lib::requires(N.lift() == T::bits().lift())]
// /// Convert a bit slice into a machine integer of type `T`.
// fn int_from_fnarr_bit<const N: usize, T: MachineInteger + Copy>(
//     bits: FunArray<N, Bit>,
// ) -> hax_lib::Int {
//     debug_assert!(N == T::bits() as usize);
//     if T::SIGNED {
//         let is_negative = matches!(bits[T::bits() as usize - 1], Bit::One);
//         let s = math_int_from_fnarr_bit(FunArray::<N, _>::from_fn(|i| {
//             if i == N - 1 {
//                 Bit::Zero
//             } else {
//                 bits[i]
//             }
//         }));
//         if is_negative {
//             hax_lib::int!(0) - s
//         } else {
//             s
//         }
//     } else {
//         math_int_from_fnarr_bit(bits)
//     }
// }

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
    debug_assert!(bits.len() <= T::bits() as usize);
    let result = if T::SIGNED {
        let is_negative = matches!(bits[T::bits() as usize - 1], Bit::One);
        let s = u64_int_from_bit_slice(&bits[0..T::bits() as usize - 1]) as i128;
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

/// An F* attribute that indiquates a rewritting lemma should be applied
pub const REWRITE_RULE: () = {};

#[hax_lib::fstar::replace(
    r#"
let ${BitVec::<0>::from_fn::<fn(u64)->Bit>}
    (v_N: u64)
    (f: (i: u64 {v i < v v_N}) -> $:{Bit})
    : t_BitVec v_N = 
    ${BitVec::<0>}(${FunArray::<0,()>::from_fn::<fn(u64)->()>} v_N f)

open FStar.FunctionalExtensionality
let ${BitVec::<0>::pointwise}
    (v_N: u64) (f: t_BitVec v_N)
    (#[${_pointwise_apply_mk_term} (v v_N) (fun (i:nat{i < v v_N}) -> f._0 (mk_u64 i))] def: (n: nat {n < v v_N}) -> $:{Bit})
    : t_BitVec v_N
    = ${BitVec::<0>::from_fn::<fn(u64)->Bit>} v_N (on (i: u64 {v i < v v_N}) (fun i -> def (v i)))

let extensionality' (#a: Type) (#b: Type) (f g: FStar.FunctionalExtensionality.(a ^-> b))
  : Lemma (ensures (FStar.FunctionalExtensionality.feq f g <==> f == g))
  = ()

open FStar.Tactics.V2
#push-options "--z3rlimit 80 --admit_smt_queries true"
let ${BitVec::<128>::rewrite_pointwise} (x: $:{BitVec<128>}) heeey
: Lemma (x == ${BitVec::<128>::pointwise} (${128u64}) x) =
    let a = x._0 in
    let b = (${BitVec::<128>::pointwise} (${128u64}) x)._0 in
    assert_norm (FStar.FunctionalExtensionality.feq a b);
    extensionality' a b

let ${BitVec::<256>::rewrite_pointwise} (x: $:{BitVec<256>})
: Lemma (x == ${BitVec::<256>::pointwise} (${256u64}) x) =
    let a = x._0 in
    let b = (${BitVec::<256>::pointwise} (${256u64}) x)._0 in
    assert_norm (FStar.FunctionalExtensionality.feq a b);
    extensionality' a b
#pop-options

let postprocess_rewrite_helper (rw_lemma: term) (): Tac unit = with_compat_pre_core 1 (fun () -> 
    let debug_mode = ext_enabled "debug_bv_postprocess_rewrite" in
    let crate = match cur_module () with | crate::_ -> crate | _ -> fail "Empty module name" in
    // Remove indirections
    norm [primops; iota; delta_namespace [crate; "Libcrux_intrinsics"]; zeta_full];
    // Rewrite call chains
    let lemmas = FStar.List.Tot.map (fun f -> pack_ln (FStar.Stubs.Reflection.V2.Data.Tv_FVar f)) (lookup_attr (`${REWRITE_RULE}) (top_env ())) in
    l_to_r lemmas;
    /// Get rid of casts
    norm [primops; iota; delta_namespace ["Rust_primitives"; "Prims.pow2"]; zeta_full];
    if debug_mode then print ("[postprocess_rewrite_helper] lemmas = " ^ term_to_string (quote lemmas));
    if debug_mode then dump "[postprocess_rewrite_helper] After applying lemmas";
    // Apply pointwise rw
    let done = alloc false in
    ctrl_rewrite TopDown (fun _ -> if read done then (false, Skip) else (true, Continue))
                            (fun _ -> (fun () -> apply_lemma_rw rw_lemma; write done true)
                                    `or_else` trefl);
    // Normalize as much as possible
    norm [primops; iota; delta_namespace ["Core"; crate; "Minicore"; "Libcrux_intrinsics"; "FStar.FunctionalExtensionality"; "Rust_primitives"]; zeta_full];
    // Compute the last bits
    compute ();
    // Force full normalization
    norm [primops; iota; delta; zeta_full];
    if debug_mode then dump "[postprocess_rewrite_helper] after full normalization";
    // Solves the goal `<normalized body> == ?u`
    trefl ()
)

let ${BitVec::<256>::postprocess_rewrite} = postprocess_rewrite_helper (`${BitVec::<256>::rewrite_pointwise})
let ${BitVec::<128>::postprocess_rewrite} = postprocess_rewrite_helper (`${BitVec::<128>::rewrite_pointwise})
"#
)]
const _: () = ();

#[hax_lib::fstar::replace(
    r#"
"#
)]
pub fn postprocess_normalize_128() {}

#[hax_lib::exclude]
impl BitVec<128> {
    pub fn rewrite_pointwise(self) {}
    pub fn postprocess_rewrite() {}
}
#[hax_lib::exclude]
impl BitVec<256> {
    pub fn rewrite_pointwise(self) {}
    pub fn postprocess_rewrite() {}
}

#[hax_lib::exclude]
impl<const N: u64> BitVec<N> {
    pub fn pointwise(self) -> Self {
        self
    }

    /// Constructor for BitVec. `BitVec::<N>::from_fn` constructs a bitvector out of a function that takes usizes smaller than `N` and produces bits.
    pub fn from_fn<F: Fn(u64) -> Bit>(f: F) -> Self {
        Self(FunArray::from_fn(f))
    }
    /// Convert a slice of machine integers where only the `d` least significant bits are relevant.
    pub fn from_slice<T: Into<i128> + MachineInteger + Copy>(x: &[T], d: u64) -> Self {
        Self::from_fn(|i| Bit::of_int(x[(i / d) as usize], (i % d) as u32))
    }

    /// Construct a BitVec out of a machine integer.
    pub fn from_int<T: Into<i128> + MachineInteger + Copy>(n: T) -> Self {
        Self::from_slice(&[n.into()], T::bits() as u64)
    }

    /// Convert a BitVec into a machine integer of type `T`.
    pub fn to_int<T: TryFrom<i128> + MachineInteger + Copy>(self) -> T {
        int_from_bit_slice(&self.0.as_vec())
    }

    /// Convert a BitVec into a vector of machine integers of type `T`.
    pub fn to_vec<T: TryFrom<i128> + MachineInteger + Copy>(&self) -> Vec<T> {
        self.0
            .as_vec()
            .chunks(T::bits() as usize)
            .map(int_from_bit_slice)
            .collect()
    }

    /// Generate a random BitVec.
    pub fn rand() -> Self {
        use rand::prelude::*;
        let random_source: Vec<_> = {
            let mut rng = rand::rng();
            (0..N).map(|_| rng.random::<bool>()).collect()
        };
        Self::from_fn(|i| random_source[i as usize].into())
    }
}

use hax_lib::{int, ToInt};

#[hax_lib::attributes]
impl<const N: u64> BitVec<N> {
    #[hax_lib::requires(CHUNK > 0 && CHUNK.to_int() * SHIFTS.to_int() == N.to_int())]
    pub fn chunked_shift<const CHUNK: u64, const SHIFTS: u64>(
        self,
        shl: FunArray<SHIFTS, i128>,
    ) -> BitVec<N> {
        // TODO: this inner method is because of https://github.com/cryspen/hax-evit/issues/29
        #[hax_lib::fstar::options("--z3rlimit 50 --split_queries always")]
        #[hax_lib::requires(CHUNK > 0 && CHUNK.to_int() * SHIFTS.to_int() == N.to_int())]
        fn chunked_shift<const N: u64, const CHUNK: u64, const SHIFTS: u64>(
            bitvec: BitVec<N>,
            shl: FunArray<SHIFTS, i128>,
        ) -> BitVec<N> {
            BitVec::from_fn(|i| {
                let nth_bit = i % CHUNK;
                let nth_chunk = i / CHUNK;
                hax_lib::assert_prop!(nth_chunk.to_int() <= SHIFTS.to_int() - int!(1));
                hax_lib::assert_prop!(
                    nth_chunk.to_int() * CHUNK.to_int()
                        <= (SHIFTS.to_int() - int!(1)) * CHUNK.to_int()
                );
                let shift: i128 = if nth_chunk < SHIFTS {
                    shl[nth_chunk]
                } else {
                    0
                };
                let local_index = (nth_bit as i128).wrapping_sub(shift);
                if local_index < CHUNK as i128 && local_index >= 0 {
                    let local_index = local_index as u64;
                    hax_lib::assert_prop!(
                        nth_chunk.to_int() * CHUNK.to_int() + local_index.to_int()
                            < SHIFTS.to_int() * CHUNK.to_int()
                    );
                    bitvec[nth_chunk * CHUNK + local_index]
                } else {
                    Bit::Zero
                }
            })
        }
        chunked_shift::<N, CHUNK, SHIFTS>(self, shl)
    }
}
