//! F* verification lemmas for SHA3/Keccak implementation.
//!
//! This module contains lemmas used for F* verification across
//! the libcrux-sha3 crate. These lemmas are only used during
//! formal verification with hax and F*, and have no runtime behavior.

/// Lemma proving the division-multiplication-modulo identity.
///
/// For any `a`, `b` with `b != 0`,
/// proves that `(a / b) * b + (a % b) = a`.
///
/// This is used in the `squeeze` function to verify correct buffer indexing
/// when squeezing multiple blocks.
#[hax_lib::fstar::replace(
    r#"
let lemma_div_mul_mod (a b: usize)
    : Lemma
        (requires b <>. mk_usize 0)
        (ensures (a /! b) *! b +! (a %! b) =. a)
    = ()
"#
)]
const _LEMMA_DIV_MUL_MOD: () = ();

/// Lemma proving multiplication bounds for successive elements.
///
/// For any `k < n`,
/// proves that `k * d + d ≤ n * d`.
///
/// This is used in the `keccak` functions to verify that block iterations
/// stay within bounds.
#[hax_lib::fstar::replace(
    r#"
let rec mul_succ_le (k n d: nat)
  : Lemma
    (requires k < n)
    (ensures k * d + d <= n * d)
    (decreases n) =
  if n = 0 then ()
  else if k = n - 1 then ()
  else mul_succ_le k (n - 1) d
"#
)]
const _LEMMA_MUL_SUCC_LE: () = ();
