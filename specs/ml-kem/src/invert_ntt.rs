use crate::ntt::get_zeta;
use crate::parameters::*;

const INVERSE_OF_128: FieldElement = FieldElement::new(3303);

/// Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
/// of a `Polynomial`.
///
/// This function implements <strong>Algorithm 9</strong> of the NIST FIPS 203 standard, which
/// is reproduced below:
///
/// ```plaintext
/// Input: array fˆ ∈ ℤ₂₅₆.
/// Output: array f ∈ ℤ₂₅₆.
///
/// f ← fˆ
/// k ← 127
/// for (len ← 2; len ≤ 128; len ← 2·len)
///     for (start ← 0; start < 256; start ← start + 2·len)
///         zeta ← ζ^(BitRev₇(k)) mod q
///         k ← k − 1
///         for (j ← start; j < start + len; j++)
///             t ← f[j]
///             f[j] ← t + f[j + len]
///             f[j + len] ← zeta·(f[j+len] − t)
///         end for
///     end for
/// end for
///
/// f ← f·3303 mod q
/// return f
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
///
#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(layer >= 1 && layer <= 7)]
fn ntt_inverse_layer(p: Polynomial, layer: usize) -> Polynomial {
    hax_lib::debug_assert!(layer <= 7);
    let len = 1 << layer;
    hax_lib::fstar!("assert (v len == pow2 (v layer))");
    let k = (256 / len) - 1;
    hax_lib::fstar!("assert (v k == 256 / (v len) - 1)");
    createi(|i| {
        let round = i / (2 * len);
        hax_lib::fstar!("assert (v round < 128 / (v len))");
        hax_lib::fstar!("assert (v len >= 2)");
        let idx = i % (2 * len);
        let q = FIELD_MODULUS as u32;
        if idx < len {
            FieldElement::new(((p[i].val as u32 + p[i + len].val as u32) % q) as u16)
        } else {
            let diff = (p[i].val as u32 + q - p[i - len].val as u32) % q;
            FieldElement::new((get_zeta(k - round).val as u32 * diff % q) as u16)
        }
    })
}

pub(crate) fn reduce_polynomial(p: Polynomial) -> Polynomial {
    createi(|i| {
        FieldElement::new(
            ((p[i].val as u32 * INVERSE_OF_128.val as u32) % FIELD_MODULUS as u32) as u16,
        )
    })
}

#[hax_lib::fstar::options("--z3rlimit 150")]
pub(crate) fn ntt_inverse(p: Polynomial) -> Polynomial {
    let p = ntt_inverse_layer(p, 1);
    let p = ntt_inverse_layer(p, 2);
    let p = ntt_inverse_layer(p, 3);
    let p = ntt_inverse_layer(p, 4);
    let p = ntt_inverse_layer(p, 5);
    let p = ntt_inverse_layer(p, 6);
    let p = ntt_inverse_layer(p, 7);
    reduce_polynomial(p)
}

/// Inverse NTT applied to each polynomial in a vector.
pub(crate) fn vector_inverse_ntt<const RANK: usize>(vector_as_ntt: Vector<RANK>) -> Vector<RANK> {
    createi(|i| ntt_inverse(vector_as_ntt[i]))
}

/// Performs Barrett reduction on all coefficients of a polynomial.
/// This is the spec equivalent of `poly_barrett_reduce` in the implementation.
pub(crate) fn poly_barrett_reduce(p: Polynomial) -> Polynomial {
    createi(|i| FieldElement::new(p[i].val % FIELD_MODULUS))
}
