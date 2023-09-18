use crate::parameters::{
    KyberFieldElement, KyberPolynomialRingElement, COEFFICIENTS_IN_RING_ELEMENT, RANK,
};

use hacspec_lib::{field::FieldElement, PanickingIntegerCasts};

const ZETA: KyberFieldElement = KyberFieldElement { value: 17 };

const INVERSE_OF_128: KyberFieldElement = KyberFieldElement { value: 3303 };

const NTT_LAYERS: [usize; 7] = [2, 4, 8, 16, 32, 64, 128];

/// Given a |value|, take the least significant 7 bits and return the number
/// obtained by reversing these bits.
fn bit_rev_7(value: u8) -> u8 {
    let mut reversed: u8 = 0;
    for bit in 0..u8::BITS - 1 {
        reversed <<= 1;
        reversed |= (value & (1 << bit)) >> bit;
    }

    reversed
}

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// Given a `KyberPolynomialRingElement` f, the NTT representation f^ is:
///
/// f^ := (f mod(X² - ζ^(2*BitRev₇(0) + 1), ..., f mod (X² − ζ^(2·BitRev₇(127) + 1))
///
/// This function implements Algorithm 8 of the NIST FIPS 203 standard, which
/// is reproduced below:
///
/// Input: array f ∈ ℤ₂₅₆
/// Output: array fˆ ∈ ℤ₂₅₆
///
/// fˆ ← f
/// k ← 1
/// for (len ← 128; len≥2; len ← len/2)
///     for (start ← 0; start < 256; start ← start + 2·len)
///         zeta ← ζ^(BitRev₇(k)) mod q
///         k ← k + 1
///         for (j ← start; j < start + len; j++)
///             t ← zeta·fˆ[j+len]
///             fˆ[j+len] ← fˆ[j] − t
///             fˆ[j] ← fˆ[j] + t
///         end for
///     end for
/// end for
/// return fˆ
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub(crate) fn ntt(f: KyberPolynomialRingElement) -> KyberPolynomialRingElement {
    let mut f_hat = f;
    let mut k: u8 = 1;

    // for (len ← 128; len ≥ 2; len ← len/2)
    for len in NTT_LAYERS.iter().rev() {
        // for (start ← 0; start < 256; start ← start + 2·len)
        for start in (0..(COEFFICIENTS_IN_RING_ELEMENT - len)).step_by(2 * len) {
            // zeta ← ζ^(BitRev₇(k)) mod q
            // k ← k + 1
            let zeta = ZETA.pow(bit_rev_7(k));
            k += 1;

            for j in start..start + len {
                let t = zeta * f_hat[j + len];
                f_hat[j + len] = f_hat[j] - t;
                f_hat[j] = f_hat[j] + t;
            }
        }
    }

    f_hat
}

/// Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// This function implements Algorithm 9 of the NIST FIPS 203 standard, which
/// is reproduced below:
///
/// Input: array fˆ ∈ ℤ₂₅₆
/// Output: array f ∈ ℤ₂₅₆
///
/// f ← fˆ
/// k ← 127
/// for (len ← 2; len ≤ 128; len ← 2·len)
///     for (start ← 0; start < 256; start ← start + 2·len)
///         zeta ← ζ^(BitRev₇(k)) mod q
///         k ← k − 1
///         for (j ← start; j < start + len; j++)
///             t ← f[j]
///             f[j] ← t + f [j + len]
///             f[j + len] ← zeta·(f[j+len] − t)
///         end for
///     end for
/// end for
///
/// f ← f·3303 mod q
/// return f
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub(crate) fn ntt_inverse(f_hat: KyberPolynomialRingElement) -> KyberPolynomialRingElement {
    let mut f = f_hat;
    let mut k: u8 = 127;

    // for (len ← 2; len ≤ 128; len ← 2·len)
    for len in NTT_LAYERS {
        // for (start ← 0; start < 256; start ← start + 2·len)
        for start in (0..(COEFFICIENTS_IN_RING_ELEMENT - len)).step_by(2 * len) {
            // zeta ← ζ^(BitRev₇(k)) mod q
            // k ← k − 1
            let zeta = ZETA.pow(bit_rev_7(k));
            k -= 1;

            for j in start..start + len {
                let t = f[j];
                f[j] = t + f[j + len];
                f[j + len] = zeta * (f[j + len] - t);
            }
        }
    }

    // f ← f·3303 mod q
    for i in 0..f.coefficients().len() {
        f[i] = f[i] * INVERSE_OF_128;
    }

    f
}

/// Given two `|KyberPolynomialRingElement|`s in their NTT representations,
/// compute their product. Given two polynomials in the NTT domain f^ and ĵ,
/// the iᵗʰ coefficient of the product k̂ is determined by the calculation:
///
/// ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X² - ζ^(2·BitRev₇(i) + 1))
///
/// This function implements Algorithm 10 of the NIST FIPS 203 standard, which
/// is reproduced below:
///
/// Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆
/// Output: An array ĥ ∈ ℤq
///
/// for(i ← 0; i < 128; i++)
///     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1], ζ^(2·BitRev₇(i) + 1))
/// end for
/// return ĥ
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
fn multiply_ntts(
    f_hat: &KyberPolynomialRingElement,
    g_hat: &KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
    let mut h_hat = KyberPolynomialRingElement::ZERO;

    for i in 0..128 {
        let binomial_product = base_case_multiply(
            (f_hat[2 * i], f_hat[2 * i + 1]),
            (g_hat[2 * i], g_hat[2 * i + 1]),
            ZETA.pow(2 * bit_rev_7(i.as_u8()) + 1),
        );

        h_hat[2 * i] = binomial_product.0;
        h_hat[2 * i + 1] = binomial_product.1;
    }

    h_hat
}

/// Represents a binomial (a₀ + a₁X) whose coefficients are
/// `|KyberFieldElement|`s:
/// - the first element of the tuple is a₀
/// - the second element of the tuple is a₁
type KyberBinomial = (KyberFieldElement, KyberFieldElement);

/// Compute the product of two `|KyberBinomial|`s with respect to the
/// modulus X² - |zeta|.
///
/// This function implements Algorithm 11 of the NIST FIPS 203 standard, which
/// is reproduced below:
///
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq
/// Input: γ ∈ ℤq
/// Output: c₀, c₁ ∈ ℤq
///
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
fn base_case_multiply(
    a: KyberBinomial,
    b: KyberBinomial,
    zeta: KyberFieldElement,
) -> KyberBinomial {
    let mut c = (FieldElement::ZERO, FieldElement::ZERO);

    c.0 = (a.0 * b.0) + (a.1 * b.1 * zeta);
    c.1 = (a.0 * b.1) + (a.1 * b.0);

    c
}

pub(crate) fn multiply_matrix_by_column(
    matrix: &[[KyberPolynomialRingElement; RANK]; RANK],
    vector: &[KyberPolynomialRingElement; RANK],
) -> [KyberPolynomialRingElement; RANK] {
    let mut result = [KyberPolynomialRingElement::ZERO; RANK];

    for (i, row) in matrix.iter().enumerate() {
        for (j, matrix_element) in row.iter().enumerate() {
            let product = multiply_ntts(matrix_element, &vector[j]);
            result[i] = result[i] + product;
        }
    }
    result
}

pub(crate) fn multiply_row_by_column(
    row_vector: &[KyberPolynomialRingElement; RANK],
    column_vector: &[KyberPolynomialRingElement; RANK],
) -> KyberPolynomialRingElement {
    let mut result = KyberPolynomialRingElement::ZERO;

    for (row_element, column_element) in row_vector.iter().zip(column_vector.iter()) {
        result = result + multiply_ntts(row_element, column_element);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use crate::compress::tests::arb_ring_element;

    #[test]
    fn seven_bit_reverse() {
        assert_eq!(64, bit_rev_7(1));
        assert_eq!(127, bit_rev_7(255));
        assert_eq!(78, bit_rev_7(185));
    }

    proptest! {
        #[test]
        fn to_ntt_and_back(ring_element in arb_ring_element(12)) {
            assert_eq!(ring_element, ntt_inverse(ntt(ring_element)));
        }
    }
}
