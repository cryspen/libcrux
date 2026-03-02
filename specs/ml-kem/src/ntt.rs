use crate::parameters::*;

const ZETA: FieldElement = 17;

const INVERSE_OF_128: FieldElement = 3303;

const NTT_LAYERS: [usize; 7] = [2, 4, 8, 16, 32, 64, 128];

fn bit_rev_7(x: usize) -> usize {
    let mut result = 0;
    for i in 0..7 {
        if (x >> i) & 1 == 1 {
            result |= 1 << (6 - i);
        }
    }
    result
}

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `Polynomial`.
///
/// Given a `Polynomial` `f`, the NTT representation `f^` is:
///
/// ```plaintext
/// f^ := (f mod(X² - ζ^(2*BitRev₇(0) + 1), ..., f mod (X² − ζ^(2·BitRev₇(127) + 1))
/// ```
///
/// This function implements <strong>Algorithm 8</strong> of the NIST FIPS 203 standard, which
/// is reproduced below:
///
/// ```plaintext
/// Input: array f ∈ ℤ₂₅₆.
/// Output: array fˆ ∈ ℤ₂₅₆.
///
/// fˆ ← f
/// k ← 1
/// for (len ← 128; len ≥ 2; len ← len/2)
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
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.

const ZETAS: [i16; 128] = [
    1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797, 2786, 3260, 569, 1746, 296,
    2447, 1339, 1476, 3046, 56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2879, 1974, 821, 289, 331,
    3253, 1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915, 2319, 1435,
    807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227, 910, 17, 2761, 583,
    2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156, 3015, 3050, 1703, 1651, 2789,
    1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641, 1584, 2298, 2037,
    3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757, 2099, 561, 2466, 2594, 2804, 1092, 403,
    1026, 1143, 2150, 2775, 886, 1722, 1212, 1874, 1029, 2110, 2935, 885, 2154,
];

#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(layer >= 1 && layer <= 7)]
fn ntt_layer(p: Polynomial, layer: usize) -> Polynomial {
    hax_lib::debug_assert!(layer <= 7);
    let len = 1 << layer;
    hax_lib::fstar!("assert (v len == pow2 (v layer))");
    let k = 128 / len;
    hax_lib::fstar!("assert (v k == 128 / (v len))");
    createi(|i| {
        let round = i / (2 * len);
        hax_lib::fstar!("assert (v round < 128 / (v len))");
        hax_lib::fstar!("assert (v round + v k < 256 / (v len))");
        hax_lib::fstar!("assert (v len >= 2)");
        let idx = i % (2 * len);
        hax_lib::fstar!("assert(v (cast (v_ZETAS.[ round +! k <: usize ] <: i16) <: i32) == v (v_ZETAS.[ round +! k <: usize ] <: i16))");
        if idx < len {
            ((p[i] as i32 + ZETAS[round + k] as i32 * p[i + len] as i32)
                .rem_euclid(FIELD_MODULUS as i32)) as i16
        } else {
            ((p[i - len] as i32 - ZETAS[round + k] as i32 * p[i] as i32)
                .rem_euclid(FIELD_MODULUS as i32)) as i16
        }
    })
}

fn ntt(p: Polynomial) -> Polynomial {
    let p = ntt_layer(p, 7);
    let p = ntt_layer(p, 6);
    let p = ntt_layer(p, 5);
    let p = ntt_layer(p, 4);
    let p = ntt_layer(p, 3);
    let p = ntt_layer(p, 2);
    let p = ntt_layer(p, 1);
    p
}

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
        if idx < len {
            ((p[i] as i32 + p[i + len] as i32).rem_euclid(FIELD_MODULUS as i32)) as i16
        } else {
            (ZETAS[k - round] as i32 * (p[i] as i32 - p[i - len] as i32))
                .rem_euclid(FIELD_MODULUS as i32) as i16
        }
    })
}

pub(crate) fn ntt_inverse(p: Polynomial) -> Polynomial {
    let p = ntt_inverse_layer(p, 1);
    let p = ntt_inverse_layer(p, 2);
    let p = ntt_inverse_layer(p, 3);
    let p = ntt_inverse_layer(p, 4);
    let p = ntt_inverse_layer(p, 5);
    let p = ntt_inverse_layer(p, 6);
    let p = ntt_inverse_layer(p, 7);
    createi(|i| (p[i] as i32 * INVERSE_OF_128 as i32).rem_euclid(FIELD_MODULUS as i32) as i16)
}

/// Compute the product of two `KyberBinomial`s with respect to the
/// modulus `X² - zeta`.
///
/// This function implements <strong>Algorithm 11</strong> of the NIST FIPS 203 standard, which
/// is reproduced below:
///
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
///
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
fn base_case_multiply_even(a0: i16, a1: i16, b0: i16, b1: i16, zeta: FieldElement) -> i16 {
    (a0 as i64 * b0 as i64 + a1 as i64 * b1 as i64 * zeta as i64).rem_euclid(FIELD_MODULUS as i64)
        as i16
}

fn base_case_multiply_odd(a0: i16, a1: i16, b0: i16, b1: i16) -> i16 {
    (a0 as i64 * b1 as i64 + a1 as i64 * b0 as i64).rem_euclid(FIELD_MODULUS as i64) as i16
}

/// Given two `Polynomial`s in their NTT representations,
/// compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
/// the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:
///
/// ```plaintext
/// ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X² - ζ^(2·BitRev₇(i) + 1))
/// ```
///
/// This function implements <strong>Algorithm 10</strong> of the NIST FIPS 203 standard, which
/// is reproduced below:
///
/// ```plaintext
/// Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
/// Output: An array ĥ ∈ ℤq.
///
/// for(i ← 0; i < 128; i++)
///     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1], ζ^(2·BitRev₇(i) + 1))
/// end for
/// return ĥ
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub(crate) fn multiply_ntts(p1: &Polynomial, p2: &Polynomial) -> Polynomial {
    createi(|i| {
        let zeta_4 = ZETAS[64 + i / 4];
        let zeta = if i % 4 < 2 {
            zeta_4
        } else {
            (FIELD_MODULUS - zeta_4).rem_euclid(FIELD_MODULUS)
        };
        if i % 2 == 0 {
            base_case_multiply_even(p1[i], p1[i + 1], p2[i], p2[i + 1], zeta)
        } else {
            base_case_multiply_odd(p1[i - 1], p1[i], p2[i - 1], p2[i])
        }
    })
}

pub(crate) fn vector_ntt<const RANK: usize>(vector: Vector<RANK>) -> Vector<RANK> {
    createi(|i| ntt(vector[i]))
}

pub(crate) fn vector_inverse_ntt<const RANK: usize>(vector_as_ntt: Vector<RANK>) -> Vector<RANK> {
    createi(|i| ntt_inverse(vector_as_ntt[i]))
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    use crate::{compress::tests::arb_ring_element, parameters::FIELD_MODULUS};

    const Q: i32 = FIELD_MODULUS as i32;

    fn mod_q(x: i32) -> i16 {
        x.rem_euclid(Q) as i16
    }

    fn mod_pow(base: i32, exp: u32, modulus: i32) -> i32 {
        let mut result: i64 = 1;
        let mut b: i64 = (base as i64).rem_euclid(modulus as i64);
        let mut e = exp;
        while e > 0 {
            if e % 2 == 1 {
                result = (result * b).rem_euclid(modulus as i64);
            }
            b = (b * b).rem_euclid(modulus as i64);
            e /= 2;
        }
        result as i32
    }

    /// Reference NTT implementing FIPS 203 Algorithm 8 directly with loops.
    fn ref_ntt(f: &Polynomial) -> Polynomial {
        let mut fhat = *f;
        let mut k: usize = 1;
        let mut len: usize = 128;
        while len >= 2 {
            let mut start = 0;
            while start < 256 {
                let zeta = ZETAS[k];
                k += 1;
                for j in start..(start + len) {
                    let t = (zeta as i32 * fhat[j + len] as i32).rem_euclid(Q);
                    fhat[j + len] = mod_q(fhat[j] as i32 - t);
                    fhat[j] = mod_q(fhat[j] as i32 + t);
                }
                start += 2 * len;
            }
            len /= 2;
        }
        fhat
    }

    /// Reference inverse NTT implementing FIPS 203 Algorithm 9 directly with loops.
    fn ref_ntt_inverse(fhat: &Polynomial) -> Polynomial {
        let mut f = *fhat;
        let mut k: usize = 127;
        let mut len: usize = 2;
        while len <= 128 {
            let mut start = 0;
            while start < 256 {
                let zeta = ZETAS[k];
                k -= 1;
                for j in start..(start + len) {
                    let t = f[j];
                    f[j] = mod_q(t as i32 + f[j + len] as i32);
                    f[j + len] = mod_q(zeta as i32 * (f[j + len] as i32 - t as i32));
                }
                start += 2 * len;
            }
            len *= 2;
        }
        let inv128 = INVERSE_OF_128 as i32;
        for coeff in f.iter_mut() {
            *coeff = mod_q(*coeff as i32 * inv128);
        }
        f
    }

    /// Multiply polynomials in Z_q[X]/(X^256+1) using schoolbook, reducing mod q.
    fn poly_mul_schoolbook(a: &Polynomial, b: &Polynomial) -> Polynomial {
        let mut result = [0i64; 256];
        for i in 0..256 {
            for j in 0..256 {
                let prod = a[i] as i64 * b[j] as i64;
                if i + j < 256 {
                    result[i + j] += prod;
                } else {
                    result[i + j - 256] -= prod;
                }
            }
        }
        createi(|i| (result[i].rem_euclid(Q as i64)) as i16)
    }

    #[test]
    fn seven_bit_reverse() {
        assert_eq!(64, bit_rev_7(1));
        assert_eq!(127, bit_rev_7(255));
        assert_eq!(78, bit_rev_7(185));
    }

    #[test]
    fn zetas_are_correct() {
        for i in 0..128 {
            let expected = mod_pow(ZETA as i32, bit_rev_7(i) as u32, Q);
            assert_eq!(
                ZETAS[i] as i32, expected,
                "ZETAS[{}] = {} but expected 17^BitRev7({}) = {}",
                i, ZETAS[i], i, expected
            );
        }
    }

    #[test]
    fn ntt_of_zero_is_zero() {
        let zero = [0i16; 256];
        assert_eq!(ntt(zero), zero);
    }

    #[test]
    fn ntt_matches_reference() {
        // Test with a simple input: f[0] = 1, rest zero (the constant polynomial 1)
        let mut f = [0i16; 256];
        f[0] = 1;
        let ntt_result = ntt(f);
        let ref_result = ref_ntt(&f);
        assert_eq!(
            ntt_result, ref_result,
            "NTT mismatch for constant polynomial 1"
        );

        // Test with f[1] = 1 (the polynomial X)
        let mut f = [0i16; 256];
        f[1] = 1;
        let ntt_result = ntt(f);
        let ref_result = ref_ntt(&f);
        assert_eq!(ntt_result, ref_result, "NTT mismatch for polynomial X");

        // Test with a more complex polynomial
        let f: Polynomial = createi(|i| (i as i16 * 7 + 3) % FIELD_MODULUS);
        let ntt_result = ntt(f);
        let ref_result = ref_ntt(&f);
        assert_eq!(
            ntt_result, ref_result,
            "NTT mismatch for complex polynomial"
        );
    }

    #[test]
    fn ntt_inverse_matches_reference() {
        let mut fhat = [0i16; 256];
        fhat[0] = 1;
        let inv_result = ntt_inverse(fhat);
        let ref_result = ref_ntt_inverse(&fhat);
        assert_eq!(
            inv_result, ref_result,
            "Inverse NTT mismatch for unit input"
        );

        let fhat: Polynomial = createi(|i| (i as i16 * 13 + 5) % FIELD_MODULUS);
        let inv_result = ntt_inverse(fhat);
        let ref_result = ref_ntt_inverse(&fhat);
        assert_eq!(
            inv_result, ref_result,
            "Inverse NTT mismatch for complex input"
        );
    }

    #[test]
    fn base_case_multiply_known_values() {
        // (a0 + a1*X) * (b0 + b1*X) mod (X^2 - zeta) = c0 + c1*X
        // c0 = a0*b0 + a1*b1*zeta
        // c1 = a0*b1 + a1*b0
        let a0: i16 = 5;
        let a1: i16 = 3;
        let b0: i16 = 7;
        let b1: i16 = 2;
        let zeta: i16 = 17;

        // c0 = 5*7 + 3*2*17 = 35 + 102 = 137
        let c0 = base_case_multiply_even(a0, a1, b0, b1, zeta);
        assert_eq!(c0, 137);

        // c1 = 5*2 + 3*7 = 10 + 21 = 31
        let c1 = base_case_multiply_odd(a0, a1, b0, b1);
        assert_eq!(c1, 31);
    }

    #[test]
    fn base_case_multiply_reduces_mod_q() {
        let a0: i16 = 3000;
        let a1: i16 = 3000;
        let b0: i16 = 3000;
        let b1: i16 = 3000;
        let zeta: i16 = 1729;

        let c0 = base_case_multiply_even(a0, a1, b0, b1, zeta);
        assert!(c0 >= 0 && c0 < FIELD_MODULUS, "c0 = {} not in [0, q)", c0);

        let c1 = base_case_multiply_odd(a0, a1, b0, b1);
        assert!(c1 >= 0 && c1 < FIELD_MODULUS, "c1 = {} not in [0, q)", c1);
    }

    #[test]
    fn multiply_ntts_known_vector() {
        // Multiply NTT(1) * NTT(X) and verify result
        let mut f = [0i16; 256];
        f[0] = 1;
        let mut g = [0i16; 256];
        g[1] = 1;

        let f_ntt = ntt(f);
        let g_ntt = ntt(g);
        let product_ntt = multiply_ntts(&f_ntt, &g_ntt);
        let product = ntt_inverse(product_ntt);

        // f*g = 1*X = X, so product should be [0, 1, 0, 0, ...]
        let mut expected = [0i16; 256];
        expected[1] = 1;
        assert_eq!(product, expected, "1 * X should equal X");
    }

    #[test]
    fn ntt_multiply_corresponds_to_polynomial_multiply() {
        // f = 1 + 2X + 3X^2
        let mut f = [0i16; 256];
        f[0] = 1;
        f[1] = 2;
        f[2] = 3;

        // g = 4 + 5X
        let mut g = [0i16; 256];
        g[0] = 4;
        g[1] = 5;

        // f*g = 4 + 13X + 22X^2 + 15X^3 (schoolbook)
        let expected = poly_mul_schoolbook(&f, &g);

        let f_ntt = ntt(f);
        let g_ntt = ntt(g);
        let product_ntt = multiply_ntts(&f_ntt, &g_ntt);
        let product = ntt_inverse(product_ntt);

        assert_eq!(
            product, expected,
            "NTT multiplication should correspond to polynomial multiplication"
        );
    }

    #[test]
    fn ntt_multiply_with_reduction() {
        // Test multiplication where X^256 + 1 reduction matters
        // f = X^200, g = X^100
        // f*g = X^300 = X^300 mod (X^256+1) = -X^44
        let mut f = [0i16; 256];
        f[200] = 1;
        let mut g = [0i16; 256];
        g[100] = 1;

        let expected = poly_mul_schoolbook(&f, &g);
        // expected[44] should be -1 mod q = 3328
        assert_eq!(expected[44], (FIELD_MODULUS - 1));

        let f_ntt = ntt(f);
        let g_ntt = ntt(g);
        let product_ntt = multiply_ntts(&f_ntt, &g_ntt);
        let product = ntt_inverse(product_ntt);

        assert_eq!(product, expected);
    }

    proptest! {
        #[test]
        fn to_ntt_and_back(ring_element in arb_ring_element(12)) {
            assert_eq!(ring_element, ntt_inverse(ntt(ring_element)));
        }

        #[test]
        fn ntt_matches_reference_proptest(ring_element in arb_ring_element(12)) {
            assert_eq!(ntt(ring_element), ref_ntt(&ring_element));
        }

        #[test]
        fn ntt_inverse_matches_reference_proptest(ring_element in arb_ring_element(12)) {
            assert_eq!(ntt_inverse(ring_element), ref_ntt_inverse(&ring_element));
        }

        #[test]
        fn ntt_multiply_is_poly_multiply(f_elem in arb_ring_element(8), g_elem in arb_ring_element(8)) {
            let expected = poly_mul_schoolbook(&f_elem, &g_elem);
            let f_ntt = ntt(f_elem);
            let g_ntt = ntt(g_elem);
            let product = ntt_inverse(multiply_ntts(&f_ntt, &g_ntt));
            assert_eq!(product, expected);
        }
    }
}
