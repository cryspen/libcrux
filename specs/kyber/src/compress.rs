use crate::parameters::{self, KyberFieldElement, KyberPolynomialRingElement};

impl KyberFieldElement {
    ///
    /// This function implements the `Compress` function defined on Page 5 of the
    /// Kyber Round 3 specification, which is defined as:
    ///
    /// ```plaintext
    /// Compress_q(x, d) = round((2^{d} / q) * x) mod^{+}2^{d}
    /// ```
    ///
    /// Since `round(x) = floor(x + 0.5)` we have:
    ///
    /// ```plaintext
    /// Compress_q(x,d) = floor(x*2^d/q + 1/2) mod^{+}2^d
    ///                 = floor((2^{d+1} * x + q) / 2q) mod^{+}2^d
    /// ```
    ///
    /// this latter expression is what the code computes, since it enables us to
    /// avoid the use of floating point arithmetic.
    ///
    /// The Kyber Round 3 specification can be found at:
    /// httpsa/kyber-specification-round3-20210131.pdf
    ///
    pub fn compress(&self, to_bit_size: usize) -> Self {
        assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

        let two_pow_bit_size = 2u32.pow(to_bit_size.try_into().unwrap_or_else(|_| {
            panic!(
                "Conversion should work since to_bit_size is never greater than {}.",
                parameters::BITS_PER_COEFFICIENT
            )
        }));

        let compressed = ((u32::from(self.value) * 2 * two_pow_bit_size)
            + u32::from(Self::MODULUS))
            / u32::from(2 * Self::MODULUS);

        (compressed % two_pow_bit_size).into()
    }

    ///
    /// This function implements the `Decompress` function defined on Page 5 of
    /// the Kyber Round 3 secification, which is defined as:
    ///
    /// ```plaintext
    /// Decompress_q(x, d) = round((q / 2^{d}) * x)
    /// ```
    ///
    /// Since `round(x) = floor(x + 0.5)` we have:
    ///
    /// ```plaintext
    /// Decompress_q(x,d) = floor((x * q) / 2^d + 1/2)
    ///                   = floor((2 * x * q + 2^d) / 2^{d+1})
    /// ```
    ///
    /// this latter expression is what the code computes, since it enables us to
    /// avoid the use of floating point arithmetic.
    ///
    /// The Kyber Round 3 specification can be found at:
    /// httpsa/kyber-specification-round3-20210131.pdf
    ///
    pub fn decompress(&self, to_bit_size: usize) -> Self {
        assert!(to_bit_size <= parameters::BITS_PER_COEFFICIENT);

        let decompressed = (2 * u32::from(self.value) * u32::from(Self::MODULUS)
            + (1 << to_bit_size))
            >> (to_bit_size + 1);

        decompressed.into()
    }
}

impl KyberPolynomialRingElement {
    ///
    /// According to the Kyber Round 3 specification, compressing a polynomial
    /// ring element is accomplished by `compress()`ing its constituent field
    /// coefficients.
    ///
    /// The Kyber Round 3 specification can be found at:
    /// httpsa/kyber-specification-round3-20210131.pdf
    ///
    pub fn compress(&self, bits_per_compressed_coefficient: usize) -> Self {
        KyberPolynomialRingElement {
            coefficients: self
                .coefficients
                .map(|coefficient| coefficient.compress(bits_per_compressed_coefficient)),
        }
    }

    ///
    /// According to the Kyber Round 3 specification, decompressing a polynomial
    /// ring element is accomplished by `decompress()`ing its constituent field
    /// coefficients.
    ///
    /// The Kyber Round 3 specification can be found at:
    /// httpsa/kyber-specification-round3-20210131.pdf
    ///
    pub fn decompress(&self, bits_per_compressed_coefficient: usize) -> Self {
        KyberPolynomialRingElement {
            coefficients: self
                .coefficients
                .map(|coefficient| coefficient.decompress(bits_per_compressed_coefficient)),
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::helpers::testing::arb_field_element;

    use proptest::prelude::*;

    /*proptest! {
        #[test]
        fn distance_between_decompressed_and_original(bit_size in 10u8..13, field_element in arb_field_element()) {
            let original : i32 = field_element.value.into();
            let decompressed : i32 = field_element.compress(bit_size).decompress(bit_size).value.into();

            let diff = original.abs_diff(decompressed);
        }
    }*/
}
