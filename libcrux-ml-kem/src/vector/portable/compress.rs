use super::arithmetic::*;
use super::vector_type::*;
use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;
use crate::vector::FIELD_MODULUS;

/// The `compress_*` functions implement the `Compress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.5), which is defined as:
///
/// ```plaintext
/// Compress_d: ℤq -> ℤ_{2ᵈ}
/// Compress_d(x) = ⌈(2ᵈ/q)·x⌋
/// ```
///
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
///
/// ```plaintext
/// Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
///               = ⌊(2^{d+1}·x + q) / 2q⌋
/// ```
///
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[cfg_attr(hax, hax_lib::requires(fe < (FIELD_MODULUS as u16)))]
#[cfg_attr(hax, hax_lib::ensures(|result|
        hax_lib::implies(833 <= fe && fe <= 2596, || result == 1) &&
        hax_lib::implies(!(833 <= fe && fe <= 2596), || result == 0)
))]
pub(crate) fn compress_message_coefficient(fe: u16) -> u8 {
    // The approach used here is inspired by:
    // https://github.com/cloudflare/circl/blob/main/pke/kyber/internal/common/poly.go#L150

    // If 833 <= fe <= 2496,
    // then -832 <= shifted <= 831
    let shifted: i16 = 1664 - (fe as i16);

    // If shifted < 0, then
    // (shifted >> 15) ^ shifted = flip_bits(shifted) = -shifted - 1, and so
    // if -832 <= shifted < 0 then 0 < shifted_positive <= 831
    //
    // If shifted >= 0 then
    // (shifted >> 15) ^ shifted = shifted, and so
    // if 0 <= shifted <= 831 then 0 <= shifted_positive <= 831
    let mask = shifted >> 15;
    let shifted_to_positive = mask ^ shifted;

    let shifted_positive_in_range = shifted_to_positive - 832;

    // If x <= 831, then x - 832 <= -1, and so x - 832 < 0, which means
    // the most significant bit of shifted_positive_in_range will be 1.
    ((shifted_positive_in_range >> 15) & 1) as u8
}

#[cfg_attr(hax,
    hax_lib::requires(
        (coefficient_bits == 4 ||
         coefficient_bits == 5 ||
         coefficient_bits == 10 ||
         coefficient_bits == 11) &&
         fe < (FIELD_MODULUS as u16)))]
#[cfg_attr(hax,
     hax_lib::ensures(
     |result| result >= 0 && result < 2i16.pow(coefficient_bits as u32)))]
pub(crate) fn compress_ciphertext_coefficient(coefficient_bits: u8, fe: u16) -> FieldElement {
    // hax_debug_assert!(
    //     coefficient_bits == 4
    //         || coefficient_bits == 5
    //         || coefficient_bits == 10
    //         || coefficient_bits == 11
    // );
    // hax_debug_assert!(fe <= (FIELD_MODULUS as u16));

    // This has to be constant time due to:
    // https://groups.google.com/a/list.nist.gov/g/pqc-forum/c/ldX0ThYJuBo/m/ovODsdY7AwAJ
    let mut compressed = (fe as u64) << coefficient_bits;
    compressed += 1664 as u64;

    compressed *= 10_321_340;
    compressed >>= 35;

    get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement
}

#[inline(always)]
#[cfg_attr(hax, hax_lib::fstar::before("
let compress_message_coefficient_range_helper (fe: u16) : Lemma
  (requires fe <. (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS) <: u16))
  (ensures v (cast (compress_message_coefficient fe) <: i16) >= 0 /\\
    v (cast (compress_message_coefficient fe) <: i16) < 2) =
  assert (v (cast (compress_message_coefficient fe) <: i16) >= 0 /\\
    v (cast (compress_message_coefficient fe) <: i16) < 2)
"))]
#[hax_lib::fstar::options("--fuel 0 --ifuel 0 --z3rlimit 2000")]
#[hax_lib::requires(fstar!("forall (i:nat). i < 16 ==> v (Seq.index ${a}.f_elements i) >= 0 /\\
    v (Seq.index ${a}.f_elements i) < 3329"))]
#[hax_lib::ensures(|result| fstar!("forall (i:nat). i < 16 ==> v (${result}.f_elements.[ sz i ] <: i16) >= 0 /\\
    v (${result}.f_elements.[ sz i ] <: i16) < 2"))]
pub(crate) fn compress_1(mut a: PortableVector) -> PortableVector {
    hax_lib::fstar!("assert (forall (i:nat). i < 16 ==> (cast (${a}.f_elements.[ sz i ]) <: u16) <.
        (cast ($FIELD_MODULUS) <: u16))");
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        hax_lib::loop_invariant!(|i: usize| { fstar!("(v $i < 16 ==> (forall (j:nat). (j >= v $i /\\ j < 16) ==>
            v (cast (${a}.f_elements.[ sz j ]) <: u16) < v (cast ($FIELD_MODULUS) <: u16))) /\\
            (forall (j:nat). j < v $i ==> v (${a}.f_elements.[ sz j ] <: i16) >= 0 /\\
                v (${a}.f_elements.[ sz j ] <: i16) < 2)") });
        hax_lib::fstar!("compress_message_coefficient_range_helper (cast (${a}.f_elements.[ $i ]) <: u16)");
        a.elements[i] = compress_message_coefficient(a.elements[i] as u16) as i16;
        hax_lib::fstar!("assert (v (${a}.f_elements.[ $i ] <: i16) >= 0 /\\
            v (${a}.f_elements.[ $i ] <: i16) < 2)");
    }

    hax_lib::fstar!("assert (forall (i:nat). i < 16 ==> v (${a}.f_elements.[ sz i ] <: i16) >= 0 /\\
        v (${a}.f_elements.[ sz i ] <: i16) < 2)");
    a
}

#[inline(always)]
#[hax_lib::fstar::options("--fuel 0 --ifuel 0 --z3rlimit 2000")]
#[hax_lib::requires(fstar!("(v $COEFFICIENT_BITS == 4 \\/
        v $COEFFICIENT_BITS == 5 \\/
        v $COEFFICIENT_BITS == 10 \\/
        v $COEFFICIENT_BITS == 11) /\\
    (forall (i:nat). i < 16 ==> v (Seq.index ${a}.f_elements i) >= 0 /\\
        v (Seq.index ${a}.f_elements i) < 3329)"))]
#[hax_lib::ensures(|result| fstar!("forall (i:nat). i < 16 ==> v (${result}.f_elements.[ sz i ] <: i16) >= 0 /\\
    v (${result}.f_elements.[ sz i ] <: i16) < pow2 (v $COEFFICIENT_BITS))"))]
pub(crate) fn compress<const COEFFICIENT_BITS: i32>(mut a: PortableVector) -> PortableVector {
    hax_lib::fstar!("assert (v (cast ($COEFFICIENT_BITS) <: u8) == v $COEFFICIENT_BITS);
        assert (v (cast ($COEFFICIENT_BITS) <: u32) == v $COEFFICIENT_BITS)");
    hax_lib::fstar!("assert (forall (i:nat). i < 16 ==> (cast (${a}.f_elements.[ sz i ]) <: u16) <.
        (cast ($FIELD_MODULUS) <: u16))");
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        hax_lib::loop_invariant!(|i: usize| { fstar!("(v $i < 16 ==> (forall (j:nat). (j >= v $i /\\ j < 16) ==>
            v (cast (${a}.f_elements.[ sz j ]) <: u16) < v (cast ($FIELD_MODULUS) <: u16))) /\\
            (forall (j:nat). j < v $i ==> v (${a}.f_elements.[ sz j ] <: i16) >= 0 /\\
                v (${a}.f_elements.[ sz j ] <: i16) < pow2 (v (cast ($COEFFICIENT_BITS) <: u32)))") });
        a.elements[i] =
            compress_ciphertext_coefficient(COEFFICIENT_BITS as u8, a.elements[i] as u16) as i16;
        hax_lib::fstar!("assert (v (${a}.f_elements.[ $i ] <: i16) >= 0 /\\
            v (${a}.f_elements.[ $i ] <: i16) < pow2 (v (cast ($COEFFICIENT_BITS) <: u32)))");
    }
    hax_lib::fstar!("assert (forall (i:nat). i < 16 ==> v (${a}.f_elements.[ sz i ] <: i16) >= 0 /\\
        v (${a}.f_elements.[ sz i ] <: i16) < pow2 (v $COEFFICIENT_BITS))");
    a
}

#[inline(always)]
pub(crate) fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(
    mut v: PortableVector,
) -> PortableVector {
    // debug_assert!(to_i16_array(v)
    //     .into_iter()
    //     .all(|coefficient| coefficient.abs() < 1 << COEFFICIENT_BITS));

    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        let mut decompressed = v.elements[i] as i32 * FIELD_MODULUS as i32;
        decompressed = (decompressed << 1) + (1i32 << COEFFICIENT_BITS);
        decompressed = decompressed >> (COEFFICIENT_BITS + 1);
        v.elements[i] = decompressed as i16;
    }

    // debug_assert!(to_i16_array(v)
    //     .into_iter()
    //     .all(|coefficient| coefficient.abs() as u16 <= 1 << 12));

    v
}
