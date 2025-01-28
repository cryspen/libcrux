//! # Constant time operations
//!
//! These are crude attempts to prevent LLVM from optimizing away the code in this
//! module. This is not guaranteed to work but at the time of writing, achieved
//! its goals.
//! `read_volatile` could be used as well but seems unnecessary at this point in
//! time.
//! Examine the output that LLVM produces for this code from time to time to ensure
//! operations are not being optimized away/constant-timedness is not being broken.

// XXX: We have to disable some of this for C extraction for now. See eurydice/issues#37

use hax_lib::{ensures, fstar, loop_invariant, requires};

/// Return 1 if `value` is not zero and 0 otherwise.
#[ensures(|result| fstar!(r#"($value == (mk_u8 0) ==> $result == (mk_u8 0)) /\
    ($value =!= (mk_u8 0) ==> $result == (mk_u8 1))"#))]
fn inz(value: u8) -> u8 {
    // We need the original value for the F* proof
    let _orig_value = value;

    let value = value as u16;
    let result = ((!value).wrapping_add(1) >> 8) as u8;
    let res = result & 1;

    // F* proof
    fstar!(
        r#"if v $_orig_value = 0 then  (
        assert($value == zero);
        lognot_lemma $value;
        assert((~.$value +. (mk_u16 1)) == zero);
        assert((Core.Num.impl__u16__wrapping_add (~.$value <: u16) (mk_u16 1) <: u16) == zero);
        logor_lemma $value zero;
        assert(($value |. (Core.Num.impl__u16__wrapping_add (~.$value <: u16) (mk_u16 1) <: u16) <: u16) == $value);
        assert (v $result == v (($value >>! (mk_i32 8))));
        assert ((v $value / pow2 8) == 0);
        assert ($result == (mk_u8 0));
        logand_lemma (mk_u8 1) $result;
        assert ($res == (mk_u8 0)))
    else (
        assert (v $value <> 0);
        lognot_lemma $value;
        assert (v (~.$value) = pow2 16 - 1 - v $value);
        assert (v (~.$value) + 1 = pow2 16 - v $value);
        assert (v ($value) <= pow2 8 - 1);
        assert ((v (~.$value) + 1) = (pow2 16 - pow2 8) + (pow2 8 - v $value));
        assert ((v (~.$value) + 1) = (pow2 8 - 1) * pow2 8 + (pow2 8 - v $value));
        assert ((v (~.$value) + 1)/pow2 8 = (pow2 8 - 1));
        assert (v ((Core.Num.impl__u16__wrapping_add (~.$value <: u16) (mk_u16 1) <: u16) >>! (mk_i32 8)) = pow2 8 - 1);
        assert ($result = ones);
        logand_lemma (mk_u8 1) $result;
        assert ($res = (mk_u8 1)))"#
    );

    res
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[ensures(|result| fstar!(r#"($value == (mk_u8 0) ==> $result == (mk_u8 0)) /\
    ($value =!= (mk_u8 0) ==> $result == (mk_u8 1))"#))]
fn is_non_zero(value: u8) -> u8 {
    #[cfg(eurydice)]
    return inz(value);

    // Eurydice can't handle this
    // XXX: May be fixed by now
    #[cfg(not(eurydice))]
    core::hint::black_box(inz(value))
}

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
#[requires(lhs.len() == rhs.len())]
#[ensures(|result| fstar!(r#"($lhs == $rhs ==> $result == (mk_u8 0)) /\
    ($lhs =!= $rhs ==> $result == (mk_u8 1))"#))]
fn _compare(lhs: &[u8], rhs: &[u8]) -> u8 {
    let mut r: u8 = 0;

    for i in 0..lhs.len() {
        loop_invariant!(|i: usize| {
            fstar!(
                r#"v $i <= Seq.length $lhs /\
            (if (Seq.slice $lhs 0 (v $i) = Seq.slice $rhs 0 (v $i)) then
                $r == (mk_u8 0)
                else ~ ($r == (mk_u8 0)))"#
            )
        });

        let nr = r | (lhs[i] ^ rhs[i]);

        // F* proof
        fstar!(
            r#"if $r =. (mk_u8 0) then (
            if (Seq.index $lhs (v $i) = Seq.index $rhs (v $i)) then (
               logxor_lemma (Seq.index $lhs (v $i)) (Seq.index $rhs (v $i));
               assert (((${lhs}.[ $i ] <: u8) ^. (${rhs}.[ $i ] <: u8) <: u8) = zero);
               logor_lemma $r ((${lhs}.[ $i ] <: u8) ^. (${rhs}.[ $i ] <: u8) <: u8);
               assert ($nr = $r);
               assert (forall j. Seq.index (Seq.slice $lhs 0 (v $i)) j == Seq.index $lhs j);
               assert (forall j. Seq.index (Seq.slice $rhs 0 (v $i)) j == Seq.index $rhs j);
               eq_intro (Seq.slice $lhs 0 ((v $i) + 1)) (Seq.slice $rhs 0 ((v $i) + 1))
            )
            else (
               logxor_lemma (Seq.index $lhs (v $i)) (Seq.index $rhs (v $i));
               assert (((${lhs}.[ $i ] <: u8) ^. (${rhs}.[ $i ] <: u8) <: u8) <>  zero);
               logor_lemma r ((${lhs}.[ $i ] <: u8) ^. (${rhs}.[ $i ] <: u8) <: u8);
               assert (v $nr > 0);
               assert (Seq.index (Seq.slice $lhs 0 ((v $i)+1)) (v $i) <> 
                       Seq.index (Seq.slice $rhs 0 ((v $i)+1)) (v $i));
               assert (Seq.slice $lhs 0 ((v $i)+1) <> Seq.slice $rhs 0 ((v $i) + 1))
            )
          ) else (
            logor_lemma $r ((${lhs}.[ $i ] <: u8) ^. (${rhs}.[ $i ] <: u8) <: u8);
            assert (v $nr >= v $r);
            assert (Seq.slice $lhs 0 (v $i) <> Seq.slice $rhs 0 (v $i));
            if (Seq.slice $lhs 0 ((v $i)+1) = Seq.slice $rhs 0 ((v $i) + 1)) then
              (assert (forall j. j < (v $i) + 1 ==> Seq.index (Seq.slice $lhs 0 ((v $i)+1)) j == Seq.index (Seq.slice $rhs 0 ((v $i)+1)) j);
               eq_intro (Seq.slice $lhs 0 (v $i)) (Seq.slice $rhs 0 (v $i));
               assert(False))
          )"#
        );

        r = nr;
    }

    is_non_zero(r)
}

/// If `selector` is not zero, return the bytes in `rhs`; return the bytes in
/// `lhs` otherwise.
#[requires(
    lhs.len() == rhs.len() &&
    lhs.len() == N
)]
#[ensures(|result| fstar!(r#"($selector == (mk_u8 0) ==> $result == $lhs) /\
        ($selector =!= (mk_u8 0) ==> $result == $rhs)"#))]
#[fstar::options("--ifuel 0 --z3rlimit 50")]
fn select_ct<const N: usize>(lhs: &[u8], rhs: &[u8], selector: u8) -> [u8; N] {
    let mask = is_non_zero(selector).wrapping_sub(1);
    let mut out = [0u8; N];

    fstar!(
        "assert (if $selector = (mk_u8 0) then $mask = ones else $mask = zero);
        lognot_lemma $mask;
        assert (if $selector = (mk_u8 0) then ~.$mask = zero else ~.$mask = ones)"
    );

    for i in 0..N {
        loop_invariant!(|i: usize| {
            fstar!(
                r#"v $i <= v $SHARED_SECRET_SIZE /\
            (forall j. j < v $i ==> (if ($selector =. (mk_u8 0)) then Seq.index $out j == Seq.index $lhs j else Seq.index $out j == Seq.index $rhs j)) /\
            (forall j. j >= v $i ==> Seq.index $out j == (mk_u8 0))"#
            )
        });
        fstar!(r#"assert ((${out}.[ $i ] <: u8) = (mk_u8 0))"#);

        let outi = (lhs[i] & mask) | (rhs[i] & !mask);

        fstar!(
            r#"if ($selector = (mk_u8 0)) then (
            logand_lemma (${lhs}.[ $i ] <: u8) $mask;
            assert (((${lhs}.[ $i ] <: u8) &. $mask <: u8) == (${lhs}.[ $i ] <: u8));
            logand_lemma (${rhs}.[ $i ] <: u8) (~.$mask);
            assert (((${rhs}.[ $i ] <: u8) &. (~.$mask <: u8) <: u8) == zero);
            logor_lemma ((${lhs}.[ $i ] <: u8) &. $mask <: u8) ((${rhs}.[ $i ] <: u8) &. (~.$mask <: u8) <: u8);
            assert ((((${lhs}.[ $i ] <: u8) &. $mask <: u8) |. ((${rhs}.[ $i ] <: u8) &. (~.$mask <: u8) <: u8) <: u8) == (${lhs}.[ $i ] <: u8));
            logor_lemma (${out}.[ $i ] <: u8) (${lhs}.[ $i ] <: u8);
            assert (((${out}.[ $i ] <: u8) |. (((${lhs}.[ $i ] <: u8) &. $mask <: u8) |. ((${rhs}.[ $i ] <: u8) &. (~.$mask <: u8) <: u8) <: u8) <: u8) == (${lhs}.[ $i ] <: u8));
            assert ($outi = (${lhs}.[ $i ] <: u8))
          )
          else (
            logand_lemma (${lhs}.[ $i ] <: u8) $mask;
            assert (((${lhs}.[ $i ] <: u8) &. $mask <: u8) == zero);
            logand_lemma (${rhs}.[ $i ] <: u8) (~.$mask);
            assert (((${rhs}.[ $i ] <: u8) &. (~.$mask <: u8) <: u8) == (${rhs}.[ $i ] <: u8));
            logor_lemma (${rhs}.[ $i ] <: u8) zero;
            assert ((logor zero (${rhs}.[ $i ] <: u8)) == (${rhs}.[ $i ] <: u8));
            assert ((((${lhs}.[ $i ] <: u8) &. $mask <: u8) |. ((${rhs}.[ $i ] <: u8) &. (~.$mask <: u8) <: u8)) == (${rhs}.[ $i ] <: u8));
            logor_lemma (${out}.[ $i ] <: u8) (${rhs}.[ $i ] <: u8);
            assert (((${out}.[ $i ] <: u8) |. (((${lhs}.[ $i ] <: u8) &. $mask <: u8) |. ((${rhs}.[ $i ] <: u8) &. (~.$mask <: u8) <: u8) <: u8) <: u8) == (${rhs}.[ $i ] <: u8));
            assert ($outi = (${rhs}.[ $i ] <: u8))
          )"#
        );

        out[i] = outi;
    }

    fstar!(
        "if ($selector =. (mk_u8 0)) then (
            eq_intro $out $lhs
        )
        else (
            eq_intro $out $rhs
        )"
    );

    out
}

// Don't inline this to avoid that the compiler optimizes this out.
#[inline(never)]
#[requires(lhs.len() == rhs.len())]
#[ensures(|result| fstar!(r#"($lhs == $rhs ==> $result == (mk_u8 0)) /\
    ($lhs =!= $rhs ==> $result == (mk_u8 1))"#))]
pub fn compare(lhs: &[u8], rhs: &[u8]) -> u8 {
    #[cfg(eurydice)]
    return _compare(lhs, rhs);

    #[cfg(not(eurydice))]
    core::hint::black_box(_compare(lhs, rhs))
}

// Don't inline this to avoid that the compiler optimizes this out.
#[inline(never)]
#[requires(
    lhs.len() == rhs.len() &&
    lhs.len() == N
)]
#[ensures(|result| fstar!(r#"($selector == (mk_u8 0) ==> $result == $lhs) /\
       ($selector =!= (mk_u8 0) ==> $result == $rhs)"#))]
pub fn select<const N: usize>(lhs: &[u8], rhs: &[u8], selector: u8) -> [u8; N] {
    #[cfg(eurydice)]
    return select_ct(lhs, rhs, selector);

    #[cfg(not(eurydice))]
    core::hint::black_box(select_ct(lhs, rhs, selector))
}

// Don't inline this to avoid that the compiler optimizes this out.
#[inline(never)]
#[requires(
    lhs_c.len() == rhs_c.len() &&
    lhs_s.len() == rhs_s.len() &&
    lhs_s.len() == N
)]
#[ensures(|result| fstar!(r#"let selector = if $lhs_c =. $rhs_c then (mk_u8 0) else (mk_u8 1) in
    ((selector == (mk_u8 0) ==> $result == $lhs_s) /\
     (selector =!= (mk_u8 0) ==> $result == $rhs_s))"#))]
pub fn compare_select<const N: usize>(
    lhs_c: &[u8],
    rhs_c: &[u8],
    lhs_s: &[u8],
    rhs_s: &[u8],
) -> [u8; N] {
    let selector = compare(lhs_c, rhs_c);
    select(lhs_s, rhs_s, selector)
}
