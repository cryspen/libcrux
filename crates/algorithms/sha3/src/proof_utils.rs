use hax_lib::{forall, implies, Prop};

/// Checks if all slices in an array have the same length.
pub(crate) fn slices_same_len<const N: usize>(slices: &[&[u8]; N]) -> Prop {
    forall(|i: usize| implies(i < N, slices[0].len() == slices[i].len()))
}

pub(crate) fn valid_rate(rate: usize) -> bool {
    // This is could be changed to checking against the specific valid rates
    // corresponding to: SHA3-512, SHA3-384, SHA3-256/SHAKE256, SHA3-224, SHAKE128
    // rate == 72 || rate == 104 || rate == 136 || rate == 144 || rate == 168
    rate != 0 && rate <= 200 && rate % 8 == 0 && (rate % 32 == 8 || rate % 32 == 16)
}

mod lemmas {
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
}
