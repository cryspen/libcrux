/// ML-DSA internal functions — FIPS 204, Section 6 (Algorithms 6–8).

use crate::parameters::{Polynomial, MlDsaParams, ZERO_POLY, Q, D};
use crate::hash_functions::{h, h2, h3};
use crate::ntt::ntt;
use crate::polynomial::*;
use crate::matrix::matrix_vector_ntt;
use crate::encoding::*;
use crate::sampling::*;
use crate::arithmetic::mod_q;
use crate::createi;

/// ML-DSA.KeyGen_internal(ξ) — FIPS 204, Algorithm 6.
///
/// Generates a public-private key pair from a 32-byte seed ξ.
pub fn keygen_internal<
    const K: usize, const L: usize,
    const PK_SIZE: usize, const SK_SIZE: usize,
>(
    xi: &[u8; 32],
    params: &MlDsaParams,
) -> ([u8; PK_SIZE], [u8; SK_SIZE]) {
    // 1. (ρ, ρ', K) ∈ B^32 × B^64 × B^32 ← H(ξ || IntegerToBytes(k,1) || IntegerToBytes(ℓ,1), 128)
    let mut seed_input = [0u8; 34];
    seed_input[..32].copy_from_slice(xi);
    seed_input[32] = params.k as u8;
    seed_input[33] = params.l as u8;
    let expanded: [u8; 128] = h(&seed_input);
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&expanded[..32]);
    let mut rho_prime = [0u8; 64];
    rho_prime.copy_from_slice(&expanded[32..96]);
    let mut key = [0u8; 32];
    key.copy_from_slice(&expanded[96..128]);

    // 3. Â ← ExpandA(ρ)
    let a_hat: [[Polynomial; L]; K] = expand_a(&rho);

    // 4. (s1, s2) ← ExpandS(ρ')
    let (s1, s2): ([Polynomial; L], [Polynomial; K]) = expand_s(&rho_prime, params.eta);

    // 5. t ← NTT⁻¹(Â ∘ NTT(s1)) + s2
    let s1_hat = vector_ntt(&s1);
    let as1_hat = matrix_vector_ntt(&a_hat, &s1_hat);
    let as1 = vector_intt(&as1_hat);
    let t = vector_add(&as1, &s2);

    // 6. (t1, t0) ← Power2Round(t)
    let (t1, t0) = vector_power2round(&t);

    // 8. pk ← pkEncode(ρ, t1)
    let pk: [u8; PK_SIZE] = pk_encode::<K, PK_SIZE>(&rho, &t1);

    // 9. tr ← H(pk, 64)
    let tr: [u8; 64] = h(&pk);

    // 10. sk ← skEncode(ρ, K, tr, s1, s2, t0)
    let sk: [u8; SK_SIZE] = sk_encode::<K, L, SK_SIZE>(&rho, &key, &tr, &s1, &s2, &t0, params);

    // 11. return (pk, sk)
    (pk, sk)
}

/// ML-DSA.Sign_internal(sk, M', rnd) — FIPS 204, Algorithm 7.
///
/// Generates a signature for formatted message M' using private key sk.
/// Returns None if all rejection sampling attempts fail (probability < 2⁻¹²⁸).
#[hax_lib::opaque]
pub fn sign_internal<const K: usize, const L: usize, const SIG_SIZE: usize>(
    sk: &[u8],
    m_prime: &[u8],
    rnd: &[u8; 32],
    params: &MlDsaParams,
) -> Option<[u8; SIG_SIZE]> {
    // 1. (ρ, K, tr, s1, s2, t0) ← skDecode(sk)
    let (rho, key, tr, s1, s2, t0) = sk_decode::<K, L>(sk, params);

    // 2–4. NTT of secret vectors
    let s1_hat = vector_ntt(&s1);
    let s2_hat = vector_ntt(&s2);
    let t0_hat = vector_ntt(&t0);

    // 5. Â ← ExpandA(ρ)
    let a_hat: [[Polynomial; L]; K] = expand_a(&rho);

    // 6. μ ← H(BytesToBits(tr) || M', 64)
    let mu: [u8; 64] = h2(&tr, m_prime);

    // 7. ρ'' ← H(K || rnd || μ, 64)
    let rho_pp: [u8; 64] = h3(&key, rnd, &mu);

    // 8–9. Initialize rejection sampling loop
    let mut kappa = 0usize;

    // 10. Rejection sampling loop (bounded by 1000 iterations)
    for _attempt in 0..1000 {
        // 11. y ← ExpandMask(ρ'', κ)
        let y: [Polynomial; L] = expand_mask(&rho_pp, kappa, params.gamma1);

        // 12. w ← NTT⁻¹(Â ∘ NTT(y))
        let y_hat = vector_ntt(&y);
        let w_hat = matrix_vector_ntt(&a_hat, &y_hat);
        let w: [Polynomial; K] = vector_intt(&w_hat);

        // 13. w1 ← HighBits(w)
        let w1: [Polynomial; K] = vector_high_bits(&w, params.gamma2);

        // 15. c̃ ← H(μ || w1Encode(w1), λ/4)
        let w1_encoded = w1_encode(&w1, params);
        let c_tilde_len = params.lambda / 4;
        let mut hash_input = mu.to_vec();
        hash_input.extend(&w1_encoded);
        let c_tilde_full: [u8; 64] = h(&hash_input);
        let c_tilde = &c_tilde_full[..c_tilde_len];

        // 16. c ← SampleInBall(c̃)
        let c = sample_in_ball(c_tilde, params.tau);

        // 17. ĉ ← NTT(c)
        let c_hat = ntt(c);

        // 18. ⟨⟨cs1⟩⟩ ← NTT⁻¹(ĉ ∘ ŝ1)
        let cs1_hat: [Polynomial; L] = scalar_vector_ntt(&c_hat, &s1_hat);
        let cs1: [Polynomial; L] = vector_intt(&cs1_hat);

        // 19. ⟨⟨cs2⟩⟩ ← NTT⁻¹(ĉ ∘ ŝ2)
        let cs2_hat: [Polynomial; K] = scalar_vector_ntt(&c_hat, &s2_hat);
        let cs2: [Polynomial; K] = vector_intt(&cs2_hat);

        // 20. z ← y + ⟨⟨cs1⟩⟩
        let z: [Polynomial; L] = vector_add(&y, &cs1);

        // 21. r0 ← LowBits(w - ⟨⟨cs2⟩⟩)
        let w_minus_cs2: [Polynomial; K] = vector_sub(&w, &cs2);
        let r0: [Polynomial; K] = vector_low_bits(&w_minus_cs2, params.gamma2);

        // 23. Validity checks
        if vector_infinity_norm(&z) >= params.gamma1 - params.beta {
            kappa += params.l;
            continue;
        }
        if vector_infinity_norm(&r0) >= params.gamma2 - params.beta {
            kappa += params.l;
            continue;
        }

        // 25. ⟨⟨ct0⟩⟩ ← NTT⁻¹(ĉ ∘ t̂0)
        let ct0_hat: [Polynomial; K] = scalar_vector_ntt(&c_hat, &t0_hat);
        let ct0: [Polynomial; K] = vector_intt(&ct0_hat);

        // 26. h ← MakeHint(−⟨⟨ct0⟩⟩, w − ⟨⟨cs2⟩⟩ + ⟨⟨ct0⟩⟩)
        let neg_ct0: [Polynomial; K] = createi(|i| {
            let mut p = ZERO_POLY;
            for j in 0..256 {
                p[j] = if ct0[i][j] == 0 { 0 } else { Q - ct0[i][j] };
            }
            p
        });
        let w_cs2_ct0: [Polynomial; K] = vector_add(&w_minus_cs2, &ct0);
        let (hint, hint_count) = vector_make_hint(&neg_ct0, &w_cs2_ct0, params.gamma2);

        // 28. Check ||⟨⟨ct0⟩⟩||∞ < γ2 and hint count ≤ ω
        if vector_infinity_norm(&ct0) >= params.gamma2 {
            kappa += params.l;
            continue;
        }
        if hint_count > params.omega {
            kappa += params.l;
            continue;
        }

        // 33. Encode signature — z must be in centered form for bit_pack
        let z_centered: [Polynomial; L] = createi(|i| poly_mod_pm(&z[i]));
        return Some(sig_encode::<K, L, SIG_SIZE>(c_tilde, &z_centered, &hint, params));
    }

    None
}

/// ML-DSA.Verify_internal(pk, M', σ) — FIPS 204, Algorithm 8.
///
/// Verifies signature σ for formatted message M' using public key pk.
#[hax_lib::opaque]
pub fn verify_internal<const K: usize, const L: usize>(
    pk: &[u8],
    m_prime: &[u8],
    sigma: &[u8],
    params: &MlDsaParams,
) -> bool {
    // 1. (ρ, t1) ← pkDecode(pk)
    let (rho, t1): ([u8; 32], [Polynomial; K]) = pk_decode(pk);

    // 2. (c̃, z, h) ← sigDecode(σ)
    let decoded = sig_decode::<K, L>(sigma, params);
    let (c_tilde, z, h_arr) = match decoded {
        Some(v) => v,
        None => return false, // 3. hint malformed
    };

    // Check ||z||∞ < γ1 - β
    if vector_infinity_norm(&z) >= params.gamma1 - params.beta {
        return false;
    }

    // 5. Â ← ExpandA(ρ)
    let a_hat: [[Polynomial; L]; K] = expand_a(&rho);

    // 6. tr ← H(pk, 64)
    let tr: [u8; 64] = h(pk);

    // 7. μ ← H(BytesToBits(tr) || M', 64)
    let mu: [u8; 64] = h2(&tr, m_prime);

    // 8. c ← SampleInBall(c̃)
    let c = sample_in_ball(&c_tilde, params.tau);

    // 9. w'_Approx ← NTT⁻¹(Â ∘ NTT(z) − NTT(c) ∘ NTT(t1 · 2^d))
    let z_hat = vector_ntt(&z);
    let az_hat = matrix_vector_ntt(&a_hat, &z_hat);

    let c_hat = ntt(c);
    let two_d = 1i32 << D;
    let t1_scaled: [Polynomial; K] = createi(|i| {
        createi(|j| mod_q(t1[i][j] as i64 * two_d as i64))
    });
    let t1_2d_hat = vector_ntt(&t1_scaled);
    let ct1_hat: [Polynomial; K] = createi(|i| {
        crate::polynomial::poly_pointwise_mul(&c_hat, &t1_2d_hat[i])
    });

    let w_approx_hat: [Polynomial; K] = createi(|i| {
        crate::polynomial::poly_sub(&az_hat[i], &ct1_hat[i])
    });
    let w_approx: [Polynomial; K] = vector_intt(&w_approx_hat);

    // 10. w'1 ← UseHint(h, w'_Approx)
    let w1_prime: [Polynomial; K] = vector_use_hint(&h_arr, &w_approx, params.gamma2);

    // 12. c̃' ← H(μ || w1Encode(w'1), λ/4)
    let w1_encoded = w1_encode(&w1_prime, params);
    let mut hash_input = mu.to_vec();
    hash_input.extend(&w1_encoded);
    let c_tilde_prime_full: [u8; 64] = h(&hash_input);
    let c_tilde_prime = &c_tilde_prime_full[..params.lambda / 4];

    // 13. Check ||z||∞ < γ1 - β AND c̃ = c̃' AND hint count ≤ ω
    // (z norm already checked above)
    let hint_count: usize = h_arr.iter().map(|hi| hi.iter().filter(|&&b| b).count()).sum();
    if hint_count > params.omega {
        return false;
    }

    c_tilde == c_tilde_prime
}
