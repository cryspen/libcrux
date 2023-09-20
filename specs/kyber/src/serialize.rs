use crate::parameters::{KyberFieldElement, KyberPolynomialRingElement, BITS_PER_COEFFICIENT};
use hacspec_lib::{
    bit_vector::{BitSlice, BitVector},
    PanickingIntegerCasts};

/// Converts a bit string `bits` into an array of bytes. This function asserts
/// that `bits.len()` is a multiple of 8.
///
/// This function implements <strong>Algorithm 2</strong> of the NIST FIPS 203
/// standard, which is reproduced below:
///
/// ```plaintext
/// Input: bit array b ∈ {0,1}⁸ˡ.
/// Output: byte array B ∈ 𝔹ˡ.
///
/// B ← (0,...,0)
/// for (i ← 0; i < 8l; i++)
///     B[⌊i/8⌋] ← B[⌊i/8⌋] + b[i]·2^{i} mod 8
/// end for
/// return B
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub(crate) fn bits_to_bytes(bits: BitVector) -> Vec<u8> {
    assert!(bits.len() % 8 == 0);

    // B ← (0,...,0)
    let mut bytes = Vec::new();

    // for (i ← 0; i < 8l; i++)
    for bit_chunk in bits.chunks(8) {
        let mut byte_value = 0u8;
        for (i, bit) in bit_chunk.into_iter().enumerate() {
            // B[⌊i/8⌋] ← B[⌊i/8⌋] + b[i]·2^{i} mod 8
            byte_value += bit * 2u8.pow(i as u32);
        }

        bytes.push(byte_value);
    }

    bytes
}

/// Converts a set of bytes in `bytes` into a set of bits.
///
/// This function implements <strong>Algorithm 3</strong> of the NIST FIPS 203
/// standard, which is reproduced below:
///
/// ```plaintext
/// Input: byte array B ∈ 𝔹ˡ.
/// Output: bit array b ∈ {0,1}⁸ˡ.
/// for (i ← 0; i < l; i++)
///     for(j ← 0; j < 8; j++)
///         b[8i + j] ← B[i] mod 2
///         B[i] ← ⌊B[i]/2⌋
///     end for
/// end for
/// return b
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub(crate) fn bytes_to_bits(bytes: &[u8]) -> BitVector {
    let mut bits = BitVector::new();

    // for (i ← 0; i < l; i++)
    for byte in bytes.iter() {
        let mut byte_value = *byte;

        // for(j ← 0; j < 8; j++)
        for _ in 0..u8::BITS {
            // b[8i + j] ← B[i] mod 2
            bits.push(byte_value % 2);

            // B[i] ← ⌊B[i]/2⌋
            byte_value /= 2;
        }
    }

    bits
}

/// Convert the associated ring element into a vector of
/// `COEFFICIENTS_IN_RING_ELEMENT * bits_per_coefficient`
/// bits, and output this vector as a byte array such that the first 8 bits of
/// the vector represent the first byte of the output, the next 8 bits the
/// next byte of the output, and so on ...
///
/// N.B.: `byte_encode` is only the inverse of `byte_decode` when:
///
/// - each ring coefficient can fit into `bits_per_coefficient` (otherwise
///   lossy compression takes place)
/// - `bits_per_coefficient < BITS_PER_COEFFICIENT`, since
///   otherwise when `byte_decode` operates on 12 bits at a time,
///   it is not injective: the values 3329 + 1 and 1 for example both fit into
///   12 bits and map to the same `KyberFieldElement`
///
/// Otherwise `byte_decode` is not injective and therefore has no left inverse.
///
/// N.B.: This function asserts that `bits_per_coefficient <= 12`
///
/// This function implements <strong>Algorithm 4</strong> of the NIST FIPS 203 standard, which is
/// reproduced below:
///
/// ```plaintext
/// Input: integer array F ∈ ℤₘ²⁵⁶, where m = 2ᵈ if d < 12 and m = q if d = 12.
/// Output: byte array B ∈ 𝔹^{32d}.
/// for(i ← 0; i < 256; i++)
///     a ← F[i]
///     for(j ← 0; j < d; j++)
///         b[i·d + j] ← a mod 2
///         a ← (a − b[i·d + j])/2
///     end for
/// B ← BitsToBytes(b)
/// return B
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub fn byte_encode(bits_per_coefficient: usize, re: KyberPolynomialRingElement) -> Vec<u8> {
    assert!(bits_per_coefficient <= BITS_PER_COEFFICIENT);

    let mut re_bits = BitVector::new();

    // for(i ← 0; i < 256; i++)
    for coefficient in re.coefficients() {
        // a ← F[i]
        let mut coefficient_value = coefficient.value;

        // for(j ← 0; j < d; j++)
        for _ in 0..bits_per_coefficient {
            let bit = coefficient_value % 2;

            // b[i·d + j] ← a mod 2
            re_bits.push(bit as u8);

            // a ← (a − b[i·d + j])/2
            coefficient_value = (coefficient_value - bit) / 2;
        }
    }

    bits_to_bytes(re_bits)
}

fn field_element_from_bits(bits: BitSlice) -> KyberFieldElement {
    assert!(bits.len() <= BITS_PER_COEFFICIENT);

    let modulus = 2u16.pow(bits.len().as_u32());
    let mut value: u16 = 0;

    for (i, bit) in bits.into_iter().enumerate() {
        value += ((*bit as u16) * (1 << i)) % modulus;
    }

    value.into()
}

/// Given a series of bytes representing a ring element in `re_bytes`,
/// first convert them into a vector of bits in little-endian order; i.e.
/// the least significant `bits_per_coefficient` of `re_bytes[0]`
/// are the first set of bits in the bitstream.
///
/// This vector is deserialized into a `KyberPolynomialRingElement` structure.
/// The first `bits_per_coefficient` represent the first coefficient of
/// the ring element, the second `bits_per_coefficient` the second coefficient,
/// and so on.
///
/// N.B.: This function asserts that `bits_per_coefficient <= 12`
///
/// This function implements <strong>Algorithm 5</strong> of the NIST FIPS 203
/// standard, which is reproduced below:
///
/// ```plaintext
/// Input: byte array B ∈ 𝔹^{32d}.
/// Output: integer array F ∈ ℤₘ²⁵⁶, where m = 2ᵈ if d < 12 and m = q if d = 12.
///
/// b ← BytesToBits(B)
/// for (i ← 0; i < 256; i++)
///     F[i] ← ∑(j = 0 to d−1) b[i·d + j] · 2ʲ mod m
/// end for
/// return F
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub fn byte_decode(bits_per_coefficient: usize, re_bytes: &[u8]) -> KyberPolynomialRingElement {
    assert!(bits_per_coefficient <= BITS_PER_COEFFICIENT);
    assert_eq!(re_bytes.len(), 32 * bits_per_coefficient);

    let re_bits = bytes_to_bits(re_bytes);
    let mut re_bit_chunks = re_bits.chunks(bits_per_coefficient);

    let mut re = KyberPolynomialRingElement::ZERO;

    // for (i ← 0; i < 256; i++)
    for i in 0..re.len() {
        // F[i] ← ∑(j = 0 to d−1) b[i·d + j] · 2ʲ mod m
        re[i] = field_element_from_bits(re_bit_chunks.next().unwrap());
    }

    re
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::compress::tests::arb_ring_element;

    proptest! {
        // TODO: Generalize this to sizes other than 12.
        #[test]
        fn deserialize_is_left_inverse_of_serialize_when_no_compression(ring_element in arb_ring_element(12)) {
            let ring_element_serialized = byte_encode(12, ring_element);
            assert_eq!(ring_element, byte_decode(12, &ring_element_serialized));
        }

        #[test]
        fn serialize_is_sometimes_left_inverse_of_deserialize_when_no_compression(ring_element in arb_ring_element(12)) {
            let ring_element_serialized = byte_encode(12, ring_element);
            assert_eq!(ring_element_serialized, byte_encode(12, byte_decode(12, &ring_element_serialized)));
        }
    }
}
