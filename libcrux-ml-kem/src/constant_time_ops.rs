use crate::constants::SHARED_SECRET_SIZE;

// These are crude attempts to prevent LLVM from optimizing away the code in this
// module. This is not guaranteed to work but at the time of writing, achieved
// its goals.
// `read_volatile` could be used as well but seems unnecessary at this point in
// time.
// Examine the output that LLVM produces for this code from time to time to ensure
// operations are not being optimized away/constant-timedness is not being broken.
//
// XXX: We have to disable this for C extraction for now. See eurydice/issues#37

/// Return 1 if `value` is not zero and 0 otherwise.
#[hax_lib::ensures(|result| fstar!(r#"($value == 0uy ==> $result == 0uy) /\
    ($value =!= 0uy ==> $result == 1uy)"#))]
fn inz(value: u8) -> u8 {
    let _orig_value = value;
    let value = value as u16;
    let result = ((!value).wrapping_add(1) >> 8) as u8;
    let res = result & 1;
    hax_lib::fstar!(
        r#"if v $_orig_value = 0 then  (
        assert($value == zero);
        lognot_lemma $value;
        assert((~.$value +. 1us) == zero);
        assert((Core.Num.impl__u16__wrapping_add (~.$value <: u16) 1us <: u16) == zero);
        logor_lemma $value zero;
        assert(($value |. (Core.Num.impl__u16__wrapping_add (~.$value <: u16) 1us <: u16) <: u16) == $value);
        assert (v $result == v (($value >>! 8l)));
        assert ((v $value / pow2 8) == 0);
        assert ($result == 0uy);
        logand_lemma 1uy $result;
        assert ($res == 0uy))
    else (
        assert (v $value <> 0);
        lognot_lemma $value;
        assert (v (~.$value) = pow2 16 - 1 - v $value);
        assert (v (~.$value) + 1 = pow2 16 - v $value);
        assert (v ($value) <= pow2 8 - 1);
        assert ((v (~.$value) + 1) = (pow2 16 - pow2 8) + (pow2 8 - v $value));
        assert ((v (~.$value) + 1) = (pow2 8 - 1) * pow2 8 + (pow2 8 - v $value));
        assert ((v (~.$value) + 1)/pow2 8 = (pow2 8 - 1));
        assert (v ((Core.Num.impl__u16__wrapping_add (~.$value <: u16) 1us <: u16) >>! 8l) = pow2 8 - 1);
        assert ($result = ones);
        logand_lemma 1uy $result;
        assert ($res = 1uy))"#
    );
    res
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[hax_lib::ensures(|result| fstar!(r#"($value == 0uy ==> $result == 0uy) /\
    ($value =!= 0uy ==> $result == 1uy)"#))]
fn is_non_zero(value: u8) -> u8 {
    #[cfg(eurydice)]
    return inz(value);

    #[cfg(not(eurydice))]
    core::hint::black_box(inz(value))
}

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
#[hax_lib::requires(lhs.len() == rhs.len())]
#[hax_lib::ensures(|result| fstar!(r#"($lhs == $rhs ==> $result == 0uy) /\
    ($lhs =!= $rhs ==> $result == 1uy)"#))]
fn compare(lhs: &[u8], rhs: &[u8]) -> u8 {
    let mut r: u8 = 0;
    for i in 0..lhs.len() {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"v $i <= Seq.length $lhs /\
            (if (Seq.slice $lhs 0 (v $i) = Seq.slice $rhs 0 (v $i)) then
                $r == 0uy
                else ~ ($r == 0uy))"#
            )
        });
        let nr = r | (lhs[i] ^ rhs[i]);
        hax_lib::fstar!(
            r#"if $r =. 0uy then (
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
#[hax_lib::requires(
    lhs.len() == rhs.len() &&
    lhs.len() == SHARED_SECRET_SIZE
)]
#[hax_lib::ensures(|result| fstar!(r#"($selector == 0uy ==> $result == $lhs) /\
        ($selector =!= 0uy ==> $result == $rhs)"#))]
#[hax_lib::fstar::options("--ifuel 0 --z3rlimit 50")]
fn select_ct(lhs: &[u8], rhs: &[u8], selector: u8) -> [u8; SHARED_SECRET_SIZE] {
    let mask = is_non_zero(selector).wrapping_sub(1);
    hax_lib::fstar!(
        "assert (if $selector = 0uy then $mask = ones else $mask = zero);
        lognot_lemma $mask;
        assert (if $selector = 0uy then ~.$mask = zero else ~.$mask = ones)"
    );
    let mut out = [0u8; SHARED_SECRET_SIZE];

    for i in 0..SHARED_SECRET_SIZE {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"v $i <= v $SHARED_SECRET_SIZE /\
            (forall j. j < v $i ==> (if ($selector =. 0uy) then Seq.index $out j == Seq.index $lhs j else Seq.index $out j == Seq.index $rhs j)) /\
            (forall j. j >= v $i ==> Seq.index $out j == 0uy)"#
            )
        });
        hax_lib::fstar!(r#"assert ((${out}.[ $i ] <: u8) = 0uy)"#);
        let outi = (lhs[i] & mask) | (rhs[i] & !mask);
        hax_lib::fstar!(
            r#"if ($selector = 0uy) then (
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

    hax_lib::fstar!(
        "if ($selector =. 0uy) then (
            eq_intro $out $lhs
        )
        else (
            eq_intro $out $rhs
        )"
    );
    out
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[hax_lib::requires(lhs.len() == rhs.len())]
#[hax_lib::ensures(|result| fstar!(r#"($lhs == $rhs ==> $result == 0uy) /\
    ($lhs =!= $rhs ==> $result == 1uy)"#))]
pub(crate) fn compare_ciphertexts_in_constant_time(lhs: &[u8], rhs: &[u8]) -> u8 {
    #[cfg(eurydice)]
    return compare(lhs, rhs);

    #[cfg(not(eurydice))]
    core::hint::black_box(compare(lhs, rhs))
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[hax_lib::requires(
    lhs.len() == rhs.len() &&
    lhs.len() == SHARED_SECRET_SIZE
)]
#[hax_lib::ensures(|result| fstar!(r#"($selector == 0uy ==> $result == $lhs) /\
       ($selector =!= 0uy ==> $result == $rhs)"#))]
pub(crate) fn select_shared_secret_in_constant_time(
    lhs: &[u8],
    rhs: &[u8],
    selector: u8,
) -> [u8; SHARED_SECRET_SIZE] {
    #[cfg(eurydice)]
    return select_ct(lhs, rhs, selector);

    #[cfg(not(eurydice))]
    core::hint::black_box(select_ct(lhs, rhs, selector))
}

#[hax_lib::requires(
    lhs_c.len() == rhs_c.len() &&
    lhs_s.len() == rhs_s.len() &&
    lhs_s.len() == SHARED_SECRET_SIZE
)]
#[hax_lib::ensures(|result| fstar!(r#"let selector = if $lhs_c =. $rhs_c then 0uy else 1uy in
    ((selector == 0uy ==> $result == $lhs_s) /\
     (selector =!= 0uy ==> $result == $rhs_s))"#))]
pub(crate) fn compare_ciphertexts_select_shared_secret_in_constant_time(
    lhs_c: &[u8],
    rhs_c: &[u8],
    lhs_s: &[u8],
    rhs_s: &[u8],
) -> [u8; SHARED_SECRET_SIZE] {
    let selector = compare_ciphertexts_in_constant_time(lhs_c, rhs_c);

    select_shared_secret_in_constant_time(lhs_s, rhs_s, selector)
}
