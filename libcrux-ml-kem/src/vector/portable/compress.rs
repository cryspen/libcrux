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
        hax_lib::implies(833 <= fe && fe <= 2496, || result == 1) &&
        hax_lib::implies(!(833 <= fe && fe <= 2496), || result == 0)
))]
pub(crate) fn compress_message_coefficient(fe: u16) -> u8 {
    // The approach used here is inspired by:
    // https://github.com/cloudflare/circl/blob/main/pke/kyber/internal/common/poly.go#L150

    // If 833 <= fe <= 2496,
    // then -832 <= shifted <= 831
    let shifted: i16 = 1664 - (fe as i16);
    hax_lib::fstar!("assert (v $shifted == 1664 - v $fe)");

    // If shifted < 0, then
    // (shifted >> 15) ^ shifted = flip_bits(shifted) = -shifted - 1, and so
    // if -832 <= shifted < 0 then 0 < shifted_positive <= 831
    //
    // If shifted >= 0 then
    // (shifted >> 15) ^ shifted = shifted, and so
    // if 0 <= shifted <= 831 then 0 <= shifted_positive <= 831
    let mask = shifted >> 15;
    hax_lib::fstar!("assert (v $mask = v $shifted / pow2 15);
        assert (if v $shifted < 0 then $mask = ones else $mask = zero)");
    let shifted_to_positive = mask ^ shifted;
    hax_lib::fstar!("logxor_lemma $shifted $mask;
        assert (v $shifted < 0 ==> v $shifted_to_positive = v (lognot $shifted));
        neg_equiv_lemma $shifted;
        assert (v (lognot $shifted) = -(v $shifted) -1);
        assert (v $shifted >= 0 ==> v $shifted_to_positive = v ($mask `logxor` $shifted));
        assert (v $shifted >= 0 ==> $mask = zero);
        assert (v $shifted >= 0 ==> $mask ^. $shifted = $shifted);
        assert (v $shifted >= 0 ==> v $shifted_to_positive = v $shifted);
        assert ($shifted_to_positive >=. mk_i16 0)");

    let shifted_positive_in_range = shifted_to_positive - 832;
    hax_lib::fstar!("assert (1664 - v $fe >= 0 ==> v $shifted_positive_in_range == 832 - v $fe);
        assert (1664 - v $fe < 0 ==> v $shifted_positive_in_range == -2497 + v $fe)");

    // If x <= 831, then x - 832 <= -1, and so x - 832 < 0, which means
    // the most significant bit of shifted_positive_in_range will be 1.
    let r0 = shifted_positive_in_range >> 15;
    let r1: i16 = r0 & 1;
    let res = r1 as u8;
    hax_lib::fstar!("assert (v $r0 = v $shifted_positive_in_range / pow2 15);
        assert (if v $shifted_positive_in_range < 0 then $r0 = ones else $r0 = zero);
        logand_lemma (mk_i16 1) $r0; 
        assert (if v $shifted_positive_in_range < 0 then $r1 = mk_i16 1 else $r1 = mk_i16 0);
        assert ((v $fe >= 833 && v $fe <= 2496) ==> $r1 = mk_i16 1);
        assert (v $fe < 833 ==> $r1 = mk_i16 0);
        assert (v $fe > 2496 ==> $r1 = mk_i16 0);
        assert (v $res = v $r1)");
    res
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
pub(crate) fn compress_1(mut v: PortableVector) -> PortableVector {
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        v.elements[i] = compress_message_coefficient(v.elements[i] as u16) as i16;
    }

    v
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
        assert (v (cast ($COEFFICIENT_BITS) <: u32) == v $COEFFICIENT_BITS);
        assert (v (cast ($FIELD_MODULUS) <: u16) == 3329)");
    hax_lib::fstar!("assert (forall (i:nat). i < 16 ==> (cast (${a}.f_elements.[ sz i ]) <: u16) <.
        (cast ($FIELD_MODULUS) <: u16))");
    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        a.elements[i] =
            compress_ciphertext_coefficient(COEFFICIENT_BITS as u8, a.elements[i] as u16) as i16;
    }
    a
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --ext context_pruning")]
#[hax_lib::requires(fstar!("(v $COEFFICIENT_BITS == 4 \\/
        v $COEFFICIENT_BITS == 5 \\/
        v $COEFFICIENT_BITS == 10 \\/
        v $COEFFICIENT_BITS == 11) /\\
    (forall (i:nat). i < 16 ==> v (Seq.index ${a}.f_elements i) >= 0 /\\
        v (Seq.index ${a}.f_elements i) < pow2 (v $COEFFICIENT_BITS))"))]
#[hax_lib::ensures(|result| fstar!("forall (i:nat). i < 16 ==> v (Seq.index ${result}.f_elements i) < v $FIELD_MODULUS"))]
pub(crate) fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(
    mut a: PortableVector,
) -> PortableVector {
    hax_lib::fstar!("assert_norm (pow2 1 == 2);
        assert_norm (pow2 4 == 16);
        assert_norm (pow2 5 == 32);
        assert_norm (pow2 10 == 1024);
        assert_norm (pow2 11 == 2048)");

    for i in 0..FIELD_ELEMENTS_IN_VECTOR {
        hax_lib::loop_invariant!(|i: usize| { fstar!("(v $i < 16 ==> (forall (j:nat). (j >= v $i /\\ j < 16) ==>
            v (Seq.index ${a}.f_elements j) >= 0 /\\  v (Seq.index ${a}.f_elements j) < pow2 (v $COEFFICIENT_BITS))) /\\
            (forall (j:nat). j < v $i ==>
                v (Seq.index ${a}.f_elements j) < v $FIELD_MODULUS)") });
        hax_lib::fstar!("assert (v (${a}.f_elements.[ $i ] <: i16) < pow2 11);
          assert (v (${a}.f_elements.[ $i ] <: i16) ==
            v (cast (${a}.f_elements.[ $i ] <: i16) <: i32));
          assert (v ($FIELD_MODULUS <: i16) ==
            v (cast ($FIELD_MODULUS <: i16) <: i32));
          assert (v ((cast (${a}.f_elements.[ $i ] <: i16) <: i32) *!
            (cast ($FIELD_MODULUS <: i16) <: i32)) ==
              v (cast (${a}.f_elements.[ $i ] <: i16) <: i32) *
                v (cast ($FIELD_MODULUS <: i16) <: i32))");
        let mut decompressed = a.elements[i] as i32 * FIELD_MODULUS as i32;
        hax_lib::fstar!("assert (v ($decompressed <<! mk_i32 1) == v $decompressed * 2);
          assert (v (mk_i32 1 <<! $COEFFICIENT_BITS) == pow2 (v $COEFFICIENT_BITS));
          assert (v (($decompressed <<! mk_i32 1) +! (mk_i32 1 <<! $COEFFICIENT_BITS)) ==
            v ($decompressed <<! mk_i32 1) + v (mk_i32 1 <<! $COEFFICIENT_BITS))");
        decompressed = (decompressed << 1) + (1i32 << COEFFICIENT_BITS);
        hax_lib::fstar!("assert (v ($COEFFICIENT_BITS +! mk_i32 1) == v $COEFFICIENT_BITS + 1);
          assert (v ($decompressed >>! ($COEFFICIENT_BITS +! mk_i32 1 <: i32)) ==
            v $decompressed / pow2 (v $COEFFICIENT_BITS + 1))");
        decompressed = decompressed >> (COEFFICIENT_BITS + 1);
        hax_lib::fstar!("assert (v $decompressed < v $FIELD_MODULUS);
          assert (v (cast $decompressed <: i16) < v $FIELD_MODULUS)");
        a.elements[i] = decompressed as i16;
    }

    a
}
