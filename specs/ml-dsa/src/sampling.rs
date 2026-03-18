/// Pseudorandom sampling — FIPS 204, Section 7.3 (Algorithms 29–34).
///
/// These functions generate polynomials and matrices from seeds using
/// SHAKE128 (G) and SHAKE256 (H). They are marked opaque for F*
/// extraction since they use dynamic allocation.

use crate::parameters::{Polynomial, ZERO_POLY, Q};
use crate::encoding::{coeff_from_three_bytes, coeff_from_half_byte};
use crate::hash_functions::h;

/// SampleInBall(ρ) — FIPS 204, Algorithm 29.
///
/// Samples a polynomial c ∈ R with coefficients in {-1, 0, 1}
/// and Hamming weight exactly τ, using a Fisher-Yates shuffle.
#[hax_lib::opaque]
pub(crate) fn sample_in_ball(rho: &[u8], tau: usize) -> Polynomial {
    // Generate enough SHAKE256 output for the shuffle.
    // We need 8 bytes for sign bits + enough bytes for position sampling.
    // 1024 bytes is far more than sufficient.
    let buf: [u8; 1024] = h(rho);
    let mut c = ZERO_POLY;

    // First 8 bytes encode the signs of the τ nonzero coefficients.
    let signs = u64::from_le_bytes([
        buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7],
    ]);

    let mut byte_offset = 8usize;
    for counter in 0..tau {
        let i = 256 - tau + counter;
        // Rejection-sample a position j ≤ i
        let mut j = buf[byte_offset] as usize;
        byte_offset += 1;
        // Bounded rejection loop (at most ~200 extra bytes needed)
        for _scan in 0..256 {
            if j <= i { break; }
            if byte_offset < 1024 {
                j = buf[byte_offset] as usize;
                byte_offset += 1;
            }
        }
        // Fisher-Yates swap
        c[i] = c[j];
        let sign_bit = (signs >> counter) & 1;
        c[j] = if sign_bit == 1 { Q - 1 } else { 1 }; // (-1)^sign = q-1 for sign=1
    }
    c
}

/// RejNTTPoly(ρ) — FIPS 204, Algorithm 30.
///
/// Samples a polynomial in T_q (NTT domain) using rejection sampling
/// from SHAKE128 output. Each coefficient is uniformly in [0, q-1].
#[hax_lib::opaque]
pub(crate) fn rej_ntt_poly(seed: &[u8]) -> Polynomial {
    // Generate SHAKE128 output. 840 bytes ≈ 280 triples, which is
    // more than enough for 256 coefficients (acceptance rate ≈ 99.75%).
    let buf: [u8; 1024] = crate::hash_functions::g(seed);
    let mut a = ZERO_POLY;
    let mut j = 0usize;
    for i in 0..(1024 / 3) {
        if j < 256 {
            if let Some(coeff) = coeff_from_three_bytes(buf[3 * i], buf[3 * i + 1], buf[3 * i + 2]) {
                a[j] = coeff;
                j += 1;
            }
        }
    }
    a
}

/// RejBoundedPoly(ρ) — FIPS 204, Algorithm 31.
///
/// Samples a polynomial with coefficients in [-η, η] using rejection
/// sampling from SHAKE256 output.
#[hax_lib::opaque]
pub(crate) fn rej_bounded_poly(seed: &[u8], eta: usize) -> Polynomial {
    let buf: [u8; 512] = h(seed);
    let mut a = ZERO_POLY;
    let mut j = 0usize;
    for i in 0..512 {
        if j < 256 {
            let z0 = coeff_from_half_byte(buf[i] & 0x0F, eta);
            if let Some(c) = z0 {
                a[j] = c; // keep in [-eta, eta] for bit_pack encoding
                j += 1;
            }
        }
        if j < 256 {
            let z1 = coeff_from_half_byte(buf[i] >> 4, eta);
            if let Some(c) = z1 {
                a[j] = c;
                j += 1;
            }
        }
    }
    a
}

/// ExpandA(ρ) — FIPS 204, Algorithm 32.
///
/// Samples a k × ℓ matrix Â of polynomials in T_q from a 32-byte seed ρ.
#[hax_lib::opaque]
pub(crate) fn expand_a<const K: usize, const L: usize>(
    rho: &[u8; 32],
) -> [[Polynomial; L]; K] {
    let mut a_hat = [[ZERO_POLY; L]; K];
    for r in 0..K {
        for s in 0..L {
            // ρ' = ρ || IntegerToBytes(s, 1) || IntegerToBytes(r, 1)
            let mut seed = rho.to_vec();
            seed.push(s as u8);
            seed.push(r as u8);
            a_hat[r][s] = rej_ntt_poly(&seed);
        }
    }
    a_hat
}

/// ExpandS(ρ') — FIPS 204, Algorithm 33.
///
/// Samples vectors s1 ∈ R^ℓ and s2 ∈ R^k with coefficients in [-η, η].
#[hax_lib::opaque]
pub(crate) fn expand_s<const K: usize, const L: usize>(
    rho_prime: &[u8; 64],
    eta: usize,
) -> ([Polynomial; L], [Polynomial; K]) {
    let mut s1 = [ZERO_POLY; L];
    for r in 0..L {
        let mut seed = rho_prime.to_vec();
        // IntegerToBytes(r, 2)
        seed.push(r as u8);
        seed.push(0u8);
        s1[r] = rej_bounded_poly(&seed, eta);
    }
    let mut s2 = [ZERO_POLY; K];
    for r in 0..K {
        let mut seed = rho_prime.to_vec();
        // IntegerToBytes(r + ℓ, 2)
        let idx = r + L;
        seed.push(idx as u8);
        seed.push((idx >> 8) as u8);
        s2[r] = rej_bounded_poly(&seed, eta);
    }
    (s1, s2)
}

/// ExpandMask(ρ'', κ) — FIPS 204, Algorithm 34.
///
/// Samples a vector y ∈ R^ℓ with coefficients in [-γ1+1, γ1].
#[hax_lib::opaque]
pub(crate) fn expand_mask<const L: usize>(
    rho_pp: &[u8; 64],
    kappa: usize,
    gamma1: i32,
) -> [Polynomial; L] {
    let c = 1 + crate::parameters::bitlen(gamma1 as usize - 1); // bitlen(γ1 - 1) + 1
    let out_bytes = 32 * c; // bytes of SHAKE256 output per polynomial
    let mut y = [ZERO_POLY; L];
    for r in 0..L {
        let mut seed = rho_pp.to_vec();
        // IntegerToBytes(κ + r, 2)
        let idx = kappa + r;
        seed.push(idx as u8);
        seed.push((idx >> 8) as u8);
        // v = H(seed, 32c)
        // We need out_bytes of SHAKE256 output. Use fixed-size calls.
        // γ1 = 2^17 → c=18, out_bytes=576; γ1 = 2^19 → c=20, out_bytes=640.
        if gamma1 == (1 << 17) {
            let buf: [u8; 576] = h(&seed);
            y[r] = crate::encoding::bit_unpack(&buf[..out_bytes], gamma1 as usize - 1, gamma1 as usize);
        } else {
            let buf: [u8; 640] = h(&seed);
            y[r] = crate::encoding::bit_unpack(&buf[..out_bytes], gamma1 as usize - 1, gamma1 as usize);
        };
    }
    y
}
