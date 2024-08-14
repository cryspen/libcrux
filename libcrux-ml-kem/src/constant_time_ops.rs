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
#[hax_lib::ensures(|result| fstar!("Hax_lib.implies ($value =. 0uy <: bool)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        $result =. 0uy <: bool) &&
    Hax_lib.implies ($value <>. 0uy <: bool)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        $result =. 1uy <: bool)"))]
fn inz(value: u8) -> u8 {
    let orig_value = value;
    let value = value as u16;
    let result = ((!value).wrapping_add(1) >> 8) as u8;
    let res = result & 1;
    hax_lib::fstar!("if v $orig_value = 0 then  (
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
        assert ($res = 1uy))");
    res
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[hax_lib::ensures(|result| fstar!("Hax_lib.implies ($value =. 0uy <: bool)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        $result =. 0uy <: bool) &&
    Hax_lib.implies ($value <>. 0uy <: bool)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        $result =. 1uy <: bool)"))]
fn is_non_zero(value: u8) -> u8 {
    #[cfg(eurydice)]
    return inz(value);

    #[cfg(not(eurydice))]
    core::hint::black_box(inz(value))
}

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
#[cfg_attr(hax, hax_lib::requires(
    lhs.len() == rhs.len()
))]
#[hax_lib::ensures(|result| fstar!("Hax_lib.implies ($lhs =. $rhs <: bool)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        $result =. 0uy <: bool) &&
    Hax_lib.implies ($lhs <>. $rhs <: bool)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        $result =. 1uy <: bool)"))]
fn compare(lhs: &[u8], rhs: &[u8]) -> u8 {
    let mut r: u8 = 0;
    for i in 0..lhs.len() {
        r |= lhs[i] ^ rhs[i];
    }

    is_non_zero(r)
}

/// If `selector` is not zero, return the bytes in `rhs`; return the bytes in
/// `lhs` otherwise.
#[cfg_attr(hax, hax_lib::requires(
    lhs.len() == rhs.len() &&
    lhs.len() == SHARED_SECRET_SIZE
))]
fn select_ct(lhs: &[u8], rhs: &[u8], selector: u8) -> [u8; SHARED_SECRET_SIZE] {
    let mask = is_non_zero(selector).wrapping_sub(1);
    let mut out = [0u8; SHARED_SECRET_SIZE];

    for i in 0..SHARED_SECRET_SIZE {
        out[i] = (lhs[i] & mask) | (rhs[i] & !mask);
    }

    out
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[cfg_attr(hax, hax_lib::requires(
    lhs.len() == rhs.len()
))]
pub(crate) fn compare_ciphertexts_in_constant_time(lhs: &[u8], rhs: &[u8]) -> u8 {
    #[cfg(eurydice)]
    return compare(lhs, rhs);

    #[cfg(not(eurydice))]
    core::hint::black_box(compare(lhs, rhs))
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[cfg_attr(hax, hax_lib::requires(
    lhs.len() == rhs.len() &&
    lhs.len() == SHARED_SECRET_SIZE
))]
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

#[cfg_attr(hax, hax_lib::requires(
    lhs_c.len() == rhs_c.len() &&
    lhs_s.len() == rhs_s.len() &&
    lhs_s.len() == SHARED_SECRET_SIZE
))]
pub(crate) fn compare_ciphertexts_select_shared_secret_in_constant_time(
    lhs_c: &[u8],
    rhs_c: &[u8],
    lhs_s: &[u8],
    rhs_s: &[u8],
) -> [u8; SHARED_SECRET_SIZE] {
    let selector = compare_ciphertexts_in_constant_time(lhs_c, rhs_c);

    select_shared_secret_in_constant_time(lhs_s, rhs_s, selector)
}
