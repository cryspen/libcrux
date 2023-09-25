use crate::parameters::{self, KyberFieldElement, KyberPolynomialRingElement};

/// According to the NIST FIPS 203 standard (Page 10, Lines 536 - 539),
/// compressing a polynomial ring element is accomplished by `compress()`ing its
/// constituent field coefficients.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub fn compress(
    re: KyberPolynomialRingElement,
    bits_per_compressed_coefficient: usize,
) -> KyberPolynomialRingElement {
    KyberPolynomialRingElement::new(
        re.coefficients()
            .map(|coefficient| compress_d(coefficient, bits_per_compressed_coefficient)),
    )
}

/// According to the NIST FIPS 203 standard (Page 10, Lines 536 - 539),
/// compressing a polynomial ring element is accomplished by `decompress()`ing
/// its constituent field coefficients.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub fn decompress(
    re: KyberPolynomialRingElement,
    bits_per_compressed_coefficient: usize,
) -> KyberPolynomialRingElement {
    KyberPolynomialRingElement::new(
        re.coefficients()
            .map(|coefficient| decompress_d(coefficient, bits_per_compressed_coefficient)),
    )
}

/// This function implements the `Compress` function specified in the NIST FIPS
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
/// this latter expression is what the code computes, since it enables us to
/// avoid the use of floating point computations as required by the standard.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
fn compress_d(fe: KyberFieldElement, to_bit_size: usize) -> KyberFieldElement {
    assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

    let two_pow_bit_size = 2u32.pow(to_bit_size.try_into().unwrap_or_else(|_| {
        panic!(
            "Conversion should work since to_bit_size is never greater than {}.",
            parameters::BITS_PER_COEFFICIENT
        )
    }));

    let compressed = ((u32::from(fe.value) * 2 * two_pow_bit_size)
        + u32::from(KyberFieldElement::MODULUS))
        / u32::from(2 * KyberFieldElement::MODULUS);

    (compressed % two_pow_bit_size).into()
}

/// This function implements the `Decompress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.6), which is defined as:
///
/// ```plaintext
/// Decompress_d: ℤ_{2ᵈ} -> ℤq
/// Decompress_d(y) = ⌈(q/2ᵈ)·y⌋
/// ```
///
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
///
/// ```plaintext
/// Decompress_d(y) = ⌊(q/2ᵈ)·y + 1/2⌋
///                 = ⌊(2·y·q + 2ᵈ) / 2^{d+1})⌋
/// ```
///
/// this latter expression is what the code computes, since it enables us to
/// avoid the use of floating point computations as required by the standard.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
fn decompress_d(fe: KyberFieldElement, to_bit_size: usize) -> KyberFieldElement {
    assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

    let decompressed = (2 * u32::from(fe.value) * u32::from(KyberFieldElement::MODULUS)
        + (1 << to_bit_size))
        >> (to_bit_size + 1);

    decompressed.into()
}

#[cfg(test)]
pub(crate) mod tests {
    use proptest::collection::vec;
    use proptest::prelude::*;

    use crate::{
        compress::{compress, decompress},
        parameters::{self, KyberFieldElement, KyberPolynomialRingElement},
    };

    prop_compose! {
        fn arb_field_element(bit_size : usize) (
            representative in 0u16..parameters::FIELD_MODULUS) -> KyberFieldElement {
                (representative & ((1 << bit_size) - 1)).into()
        }
    }

    prop_compose! {
        pub(crate) fn arb_ring_element(bits_per_coefficient : usize) (arb_ring_coefficients in vec(arb_field_element(bits_per_coefficient), parameters::COEFFICIENTS_IN_RING_ELEMENT)) -> KyberPolynomialRingElement {
                KyberPolynomialRingElement::new(
                     arb_ring_coefficients.try_into().unwrap())
        }
    }

    // TODO: Check that for a randomly chosen x in Z_q, the expression:
    // decompress_d(compress_d(x, d), d) - x mod q
    // is almost uniform over the integers of magnitude at most B_q, where
    // B_q = round(q / 2^{d + 1})
    proptest! {
        #[test]
        fn compress_to_zero_bits(ring_element in arb_ring_element(12)) {
            let compressed = compress(ring_element, 0);
            for coefficient in compressed.coefficients() {
                assert_eq!(coefficient.value, 0);
            }
        }

        fn compress_and_decompress_are_inverses_when_no_compression(ring_element in arb_ring_element(12)) {
            let compressed = compress(ring_element, 12);
            let decompressed = decompress(compressed, 12);

            assert_eq!(compressed, decompressed);
        }
    }
}
