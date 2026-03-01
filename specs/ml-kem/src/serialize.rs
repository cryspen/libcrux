use crate::parameters::*;


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
#[hax_lib::requires(N8 == N * 8)]
pub(crate) fn bytes_to_bits<const N: usize, const N8: usize>(
    bytes: &[u8; N]) -> BitVector<N8> {
    createi(|i| (bytes[i/8] >> (i%8)) & 1 == 1)
}

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
#[hax_lib::requires(N8 == N * 8)]
#[hax_lib::ensures(bv == bytes_to_bits(result))]
pub(crate) fn bits_to_bytes<const N: usize, const N8: usize>(
    bv: &BitVector<N8>) -> [u8; N] {
    createi(|i| {
            bv[8*i] as u8
         | ((bv[8*i + 1] as u8) << 1)
         | ((bv[8*i + 2] as u8) << 2)
         | ((bv[8*i + 3] as u8) << 3)
         | ((bv[8*i + 4] as u8) << 4)
         | ((bv[8*i + 5] as u8) << 5)
         | ((bv[8*i + 6] as u8) << 6)
         | ((bv[8*i + 7] as u8) << 7)
    }   )
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

#[hax_lib::requires(Nd == N * d)]
pub(crate) fn bitvector_from_bounded_ints<const N: usize, const Nd: usize>(
    input: &[i16; N],
    d:usize) -> BitVector<Nd> {
    createi(|i| (input[i/d] >> (i%d)) & 1 == 1)
}

#[hax_lib::requires(d <= BITS_PER_COEFFICIENT && D32 == 32 * d && D256 == 256 * d)]
pub fn byte_encode<const D32: usize, const D256: usize>(p: Polynomial, d: usize) -> [u8; D32] {
    let bv = bitvector_from_bounded_ints::<256, D256>(&p, d);
    bits_to_bytes(&bv)
}


/// Given a series of bytes representing a ring element in `re_bytes`,
/// first convert them into a vector of bits in little-endian order; i.e.
/// the least significant `bits_per_coefficient` of `re_bytes[0]`
/// are the first set of bits in the bitstream.
///
/// This vector is deserialized into a `Polynomial` structure.
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
#[hax_lib::requires(Nd == N * d)]
#[hax_lib::ensures(input == bitvector_from_bounded_ints(result, d))]
pub(crate) fn bitvector_to_bounded_ints<const N: usize, const Nd: usize>(
    input: &BitVector<Nd>,
    d:usize) -> [i16; N] {
    createi(|i| {
        let mut coefficient = 0;
        for j in 0..d {
            if input[i*d + j] {
                coefficient |= 1 << j;
            }
        }
        coefficient
    })
}

#[hax_lib::requires(d <= BITS_PER_COEFFICIENT && b.len() == 32 * d && D32 == 32 * d && D256 == 256 * d)]
pub fn byte_decode_generic<const N:usize, const N8: usize, const Nd: usize, const Nd8: usize>(b: &[u8; Nd], d: usize) -> [i16; N8] {
    let bv: [bool; Nd8] = bytes_to_bits(&b);
    bitvector_to_bounded_ints(&bv, d)
}

#[hax_lib::requires(d <= BITS_PER_COEFFICIENT && b.len() == 32 * d && D32 == 32 * d && D256 == 256 * d)]
pub fn byte_decode<const D32: usize, const D256: usize>(b: &[u8; D32], d: usize) -> Polynomial {
    let decoded = byte_decode_generic::<32, 256, D32, D256>(b, d);
    createi(|i| decoded[i] % FIELD_MODULUS as i16)
}

// pub(crate) fn vector_encode_12(vector: KyberVector) -> [u8; RANK * BYTES_PER_RING_ELEMENT] {
//     let mut out = [0u8; RANK * BYTES_PER_RING_ELEMENT];

//     for (i, re) in vector.into_iter().enumerate() {
//         out[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT]
//             .copy_from_slice(&byte_encode(12, re));
//     }

//     out
// }

// pub(crate) fn vector_decode_12(encoded: &[u8; RANK * BYTES_PER_RING_ELEMENT]) -> KyberVector {
//     let mut out = KyberVector::ZERO;

//     for (i, bytes) in encoded.chunks(BYTES_PER_RING_ELEMENT).enumerate() {
//         out[i] = byte_decode(12, bytes);
//     }

//     out
// }

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::compress::tests::arb_ring_element;
    use crate::parameters::FIELD_MODULUS;

    #[test]
    fn bytes_to_bits_known_vector() {
        // 0xA5 = 10100101 -> bits in LE: [1,0,1,0,0,1,0,1]
        // 0x3C = 00111100 -> bits in LE: [0,0,1,1,1,1,0,0]
        let bytes = [0xA5u8, 0x3C];
        let bits: [bool; 16] = bytes_to_bits(&bytes);
        assert_eq!(bits[0..8], [true, false, true, false, false, true, false, true]);
        assert_eq!(bits[8..16], [false, false, true, true, true, true, false, false]);
    }

    #[test]
    fn bits_to_bytes_known_vector() {
        let mut bits = [false; 16];
        // Encode 0xA5 = LE bits [1,0,1,0,0,1,0,1]
        bits[0] = true;
        bits[2] = true;
        bits[5] = true;
        bits[7] = true;
        // Encode 0x3C = LE bits [0,0,1,1,1,1,0,0]
        bits[10] = true;
        bits[11] = true;
        bits[12] = true;
        bits[13] = true;

        let bytes: [u8; 2] = bits_to_bytes(&bits);
        assert_eq!(bytes, [0xA5, 0x3C]);
    }

    #[test]
    fn bytes_to_bits_all_zeros() {
        let bytes = [0u8; 4];
        let bits: [bool; 32] = bytes_to_bits(&bytes);
        assert!(bits.iter().all(|&b| !b));
    }

    #[test]
    fn bytes_to_bits_all_ones() {
        let bytes = [0xFFu8; 4];
        let bits: [bool; 32] = bytes_to_bits(&bytes);
        assert!(bits.iter().all(|&b| b));
    }

    #[test]
    fn bitvector_from_bounded_ints_known_vector() {
        // d=4, integers [5, 11] -> bits for 5=0101 and 11=1011
        let ints: [i16; 2] = [5, 11];
        let bits: [bool; 8] = bitvector_from_bounded_ints(&ints, 4);
        // 5 in LE bits: [1,0,1,0]
        assert_eq!(bits[0..4], [true, false, true, false]);
        // 11 in LE bits: [1,1,0,1]
        assert_eq!(bits[4..8], [true, true, false, true]);
    }

    #[test]
    fn bitvector_to_bounded_ints_known_vector() {
        // Reverse of above: bits for 5 and 11 with d=4
        let bits = [true, false, true, false, true, true, false, true];
        let ints: [i16; 2] = bitvector_to_bounded_ints(&bits, 4);
        assert_eq!(ints, [5, 11]);
    }

    #[test]
    fn bitvector_roundtrip() {
        // from_bounded -> to_bounded should recover original values
        let ints: [i16; 4] = [0, 7, 15, 3];
        let bits: [bool; 16] = bitvector_from_bounded_ints(&ints, 4);
        let recovered: [i16; 4] = bitvector_to_bounded_ints(&bits, 4);
        assert_eq!(recovered, ints);
    }

    #[test]
    fn byte_encode_decode_roundtrip_d1() {
        // d=1: coefficients are 0 or 1
        let mut poly = [0i16; 256];
        for i in 0..256 {
            poly[i] = (i % 2) as i16;
        }
        let encoded: [u8; 32] = byte_encode::<32, 256>(poly, 1);
        let decoded: Polynomial = byte_decode::<32, 256>(&encoded, 1);
        assert_eq!(decoded, poly);
    }

    #[test]
    fn byte_encode_decode_roundtrip_d4() {
        let poly: Polynomial = createi(|i| (i % 16) as i16);
        let encoded: [u8; 128] = byte_encode::<128, 1024>(poly, 4);
        let decoded: Polynomial = byte_decode::<128, 1024>(&encoded, 4);
        assert_eq!(decoded, poly);
    }

    #[test]
    fn byte_encode_decode_roundtrip_d10() {
        let poly: Polynomial = createi(|i| (i % 1024) as i16);
        let encoded: [u8; 320] = byte_encode::<320, 2560>(poly, 10);
        let decoded: Polynomial = byte_decode::<320, 2560>(&encoded, 10);
        assert_eq!(decoded, poly);
    }

    #[test]
    fn byte_decode_d12_reduces_mod_q() {
        // Encode a polynomial with values in [0, q-1], decode it, verify reduction
        let poly: Polynomial = createi(|i| (i as i16 * 13) % FIELD_MODULUS);
        let encoded: [u8; 384] = byte_encode::<384, 3072>(poly, 12);
        let decoded: Polynomial = byte_decode::<384, 3072>(&encoded, 12);
        // All decoded values should be in [0, q-1]
        for (i, &coeff) in decoded.iter().enumerate() {
            assert!(
                coeff >= 0 && coeff < FIELD_MODULUS,
                "decoded[{}] = {} not in [0, q)", i, coeff
            );
        }
        assert_eq!(decoded, poly);
    }

    #[test]
    fn byte_encode_known_vector_d1() {
        // All zeros
        let poly = [0i16; 256];
        let encoded: [u8; 32] = byte_encode::<32, 256>(poly, 1);
        assert_eq!(encoded, [0u8; 32]);

        // All ones
        let poly = [1i16; 256];
        let encoded: [u8; 32] = byte_encode::<32, 256>(poly, 1);
        assert_eq!(encoded, [0xFFu8; 32]);
    }

    #[test]
    fn byte_decode_known_vector_d1() {
        let bytes = [0u8; 32];
        let decoded: Polynomial = byte_decode::<32, 256>(&bytes, 1);
        assert!(decoded.iter().all(|&c| c == 0));

        let bytes = [0xFFu8; 32];
        let decoded: Polynomial = byte_decode::<32, 256>(&bytes, 1);
        assert!(decoded.iter().all(|&c| c == 1));
    }

    proptest! {
        #[test]
        fn bytes_to_bits_and_back_roundtrip(b0 in any::<u8>(), b1 in any::<u8>(), b2 in any::<u8>(), b3 in any::<u8>()) {
            let bytes = [b0, b1, b2, b3];
            let bits: [bool; 32] = bytes_to_bits(&bytes);
            let recovered: [u8; 4] = bits_to_bytes(&bits);
            assert_eq!(recovered, bytes);
        }

        #[test]
        fn deserialize_is_left_inverse_of_serialize_when_no_compression(ring_element in arb_ring_element(12)) {
            let ring_element_serialized: [u8; 32 * 12]= byte_encode::<{32 * 12}, {256 * 12}>(ring_element, 12);
            assert_eq!(ring_element, byte_decode::<{32 * 12}, {256 * 12}>(&ring_element_serialized, 12));
        }

        #[test]
        fn serialize_is_sometimes_left_inverse_of_deserialize_when_no_compression(ring_element in arb_ring_element(12)) {
            let ring_element_serialized: [u8; 32 * 12]= byte_encode::<{32 * 12}, {256 * 12}>(ring_element, 12);
            assert_eq!(ring_element_serialized, byte_encode::<{32 * 12}, {256 * 12}>(byte_decode::<{32 * 12}, {256 * 12}>(&ring_element_serialized, 12), 12));
        }
    }
}
