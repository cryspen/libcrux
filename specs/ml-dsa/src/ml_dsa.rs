use crate::arithmetic::mod_q;
use crate::createi;
use crate::encoding::*;
use crate::error::MlDsaError;
use crate::hash_functions::{h, h2, h3};
use crate::matrix::matrix_vector_ntt;
use crate::ntt::ntt;
/// ML-DSA internal functions — FIPS 204, Section 6 (Algorithms 6–8).
use crate::parameters::{MlDsaParams, Polynomial, D, Q, ZERO_POLY};
use crate::polynomial::*;
use crate::sampling::*;

/// ML-DSA.KeyGen_internal(ξ) — FIPS 204, Algorithm 6.
///
/// Generates a public-private key pair from a 32-byte seed ξ.
#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(
    K <= 8 && L <= 8
    && PK_SIZE == 32 + 320 * K
    && (params.eta == 2 || params.eta == 4)
    && SK_SIZE >= 128 + (L + K) * 32 * (if params.eta == 2 { 3 } else { 4 }) + K * 416
)]
pub fn keygen_internal<
    const K: usize,
    const L: usize,
    const PK_SIZE: usize,
    const SK_SIZE: usize,
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
    hax_lib::fstar!(
        r#"assume(forall i. i < Seq.length t ==> (forall j. j < 256 ==> Rust_primitives.Integers.v (Seq.index (Seq.index t i) j) >= 0 /\ Rust_primitives.Integers.v (Seq.index (Seq.index t i) j) < Rust_primitives.Integers.v ${Q}))"#
    );
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
/// Returns `Err(RejectionSamplingExhausted)` if all rejection sampling
/// attempts fail (probability < 2⁻¹²⁸); `Err(SampleInBallExhausted)` is
/// folded into rejection-loop continuation rather than propagated as
/// a sign failure.
#[hax_lib::fstar::verification_status(lax)]
pub fn sign_internal<
    const K: usize,
    const L: usize,
    const SIG_SIZE: usize,
    const W1_BYTES: usize,
    const C_TILDE_LEN: usize,
>(
    sk: &[u8],
    m_prime: &[u8],
    rnd: &[u8; 32],
    params: &MlDsaParams,
) -> Result<[u8; SIG_SIZE], MlDsaError> {
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

    // 8–9. Rejection sampling loop
    let mut result: Result<[u8; SIG_SIZE], MlDsaError> =
        Err(MlDsaError::RejectionSamplingExhausted);
    let mut signed = false;
    let mut kappa = 0usize;

    for _attempt in 0..1000 {
        if !signed {
            // 11. y ← ExpandMask(ρ'', κ)
            let y: [Polynomial; L] = expand_mask(&rho_pp, kappa, params.gamma1);

            // 12. w ← NTT⁻¹(Â ∘ NTT(y))
            let y_hat = vector_ntt(&y);
            let w_hat = matrix_vector_ntt(&a_hat, &y_hat);
            let w: [Polynomial; K] = vector_intt(&w_hat);

            // 13. w1 ← HighBits(w)
            let w1: [Polynomial; K] = vector_high_bits(&w, params.gamma2);

            // 15. c̃ ← H(μ || w1Encode(w1), λ/4)
            let w1_encoded: [u8; W1_BYTES] = w1_encode(&w1, params);
            // Build hash input: μ (64 bytes) || w1_encoded (W1_BYTES bytes)
            // Max W1_BYTES = 1024, so 64 + 1024 = 1088 max.
            let mut hash_input = [0u8; 1088];
            hash_input[..64].copy_from_slice(&mu);
            hash_input[64..64 + W1_BYTES].copy_from_slice(&w1_encoded);
            let c_tilde_full: [u8; 64] = h(&hash_input[..64 + W1_BYTES]);
            let mut c_tilde = [0u8; C_TILDE_LEN];
            c_tilde.copy_from_slice(&c_tilde_full[..C_TILDE_LEN]);

            // 16. c ← SampleInBall(c̃).  On exhaustion (probabilistically
            // impossible per the spec's 1024-byte buffer) we treat this
            // attempt as a rejection and increment kappa.
            match sample_in_ball(&c_tilde, params.tau) {
                Err(_) => {
                    kappa += params.l;
                }
                Ok(c) => {
                    // 17. ĉ ← NTT(c)
                    let c_hat = ntt(c);

                    // 18–19. cs1, cs2
                    let cs1_hat: [Polynomial; L] = scalar_vector_ntt(&c_hat, &s1_hat);
                    let cs1: [Polynomial; L] = vector_intt(&cs1_hat);
                    let cs2_hat: [Polynomial; K] = scalar_vector_ntt(&c_hat, &s2_hat);
                    let cs2: [Polynomial; K] = vector_intt(&cs2_hat);

                    // 20. z ← y + cs1
                    let z: [Polynomial; L] = vector_add(&y, &cs1);

                    // 21. r0 ← LowBits(w - cs2)
                    let w_minus_cs2: [Polynomial; K] = vector_sub(&w, &cs2);
                    let r0: [Polynomial; K] = vector_low_bits(&w_minus_cs2, params.gamma2);

                    // 23. Validity checks
                    if vector_infinity_norm(&z) >= params.gamma1 - params.beta
                        || vector_infinity_norm(&r0) >= params.gamma2 - params.beta
                    {
                        kappa += params.l;
                    } else {
                        // 25. ct0
                        let ct0_hat: [Polynomial; K] = scalar_vector_ntt(&c_hat, &t0_hat);
                        let ct0: [Polynomial; K] = vector_intt(&ct0_hat);

                        // 26. h ← MakeHint(-ct0, w - cs2 + ct0)
                        let neg_ct0: [Polynomial; K] = createi(|i| {
                            let mut p = ZERO_POLY;
                            for j in 0..256 {
                                p[j] = if ct0[i][j] == 0 { 0 } else { Q - ct0[i][j] };
                            }
                            p
                        });
                        let w_cs2_ct0: [Polynomial; K] =
                            vector_add(&w_minus_cs2, &ct0);
                        let (hint, hint_count) =
                            vector_make_hint(&neg_ct0, &w_cs2_ct0, params.gamma2);

                        // 28. Check ||ct0||∞ < γ2 and hint count ≤ ω
                        if vector_infinity_norm(&ct0) >= params.gamma2
                            || hint_count > params.omega
                        {
                            kappa += params.l;
                        } else {
                            // 33. Encode signature
                            let z_centered: [Polynomial; L] =
                                createi(|i| poly_mod_pm(&z[i]));
                            result = Ok(sig_encode::<K, L, SIG_SIZE>(
                                &c_tilde,
                                &z_centered,
                                &hint,
                                params,
                            ));
                            signed = true;
                        }
                    }
                }
            }
        }
    }

    result
}

/// ML-DSA.Verify_internal(pk, M', σ) — FIPS 204, Algorithm 8.
///
/// Verifies signature σ for formatted message M' using public key pk.
#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(
    K <= 8 && L <= 8
    && C_TILDE_LEN <= 64 && W1_BYTES >= K * 192 && W1_BYTES <= 1024
    && params.tau <= 64
    && params.omega <= 256
    && params.beta >= 0 && params.gamma1 > params.beta && params.gamma2 > params.beta
    && (params.gamma1 == (1i32 << 17) || params.gamma1 == (1i32 << 19))
    && (params.gamma2 == (Q - 1) / 88 || params.gamma2 == (Q - 1) / 32)
    && pk.len() >= 32 + 320 * K
    && sigma.len() >= C_TILDE_LEN + L * 32 * (if params.gamma1 == (1i32 << 17) { 18 } else { 20 }) + params.omega + K
)]
pub fn verify_internal<
    const K: usize,
    const L: usize,
    const C_TILDE_LEN: usize,
    const W1_BYTES: usize,
>(
    pk: &[u8],
    m_prime: &[u8],
    sigma: &[u8],
    params: &MlDsaParams,
) -> Result<(), MlDsaError> {
    // 1. (ρ, t1) ← pkDecode(pk)
    let (rho, t1): ([u8; 32], [Polynomial; K]) = pk_decode(pk);

    // 2. (c̃, z, h) ← sigDecode(σ)
    match sig_decode::<K, L, C_TILDE_LEN>(sigma, params) {
        None => Err(MlDsaError::MalformedSignature),
        Some((c_tilde, z, h_arr)) => {
            // Check ||z||∞ < γ1 - β
            if vector_infinity_norm(&z) >= params.gamma1 - params.beta {
                Err(MlDsaError::InvalidSignature)
            } else {
                // 5. Â ← ExpandA(ρ)
                let a_hat: [[Polynomial; L]; K] = expand_a(&rho);

                // 6. tr ← H(pk, 64)
                let tr: [u8; 64] = h(pk);

                // 7. μ ← H(BytesToBits(tr) || M', 64)
                let mu: [u8; 64] = h2(&tr, m_prime);

                // 8. c ← SampleInBall(c̃).  The 1024-byte buffer
                // can in principle be exhausted (probabilistically
                // impossible per the spec); surface that as an error.
                match sample_in_ball(&c_tilde, params.tau) {
                    Err(e) => Err(e),
                    Ok(c) => {
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
                        hax_lib::fstar!(
                            r#"assume(forall i. i < Seq.length w_approx ==> (forall j. j < 256 ==> Rust_primitives.Integers.v (Seq.index (Seq.index w_approx i) j) >= 0 /\ Rust_primitives.Integers.v (Seq.index (Seq.index w_approx i) j) < Rust_primitives.Integers.v ${Q}))"#
                        );
                        let w1_prime: [Polynomial; K] =
                            vector_use_hint(&h_arr, &w_approx, params.gamma2);

                        // 12. c̃' ← H(μ || w1Encode(w'1), λ/4)
                        let w1_encoded: [u8; W1_BYTES] = w1_encode(&w1_prime, params);
                        let mut hash_input = [0u8; 1088];
                        hash_input[..64].copy_from_slice(&mu);
                        hash_input[64..64 + W1_BYTES].copy_from_slice(&w1_encoded);
                        let c_tilde_prime_full: [u8; 64] =
                            h(&hash_input[..64 + W1_BYTES]);
                        let mut c_tilde_prime = [0u8; C_TILDE_LEN];
                        c_tilde_prime.copy_from_slice(&c_tilde_prime_full[..C_TILDE_LEN]);

                        // 13. Check hint count ≤ ω and c̃ = c̃'
                        let hint_count = count_hints(&h_arr);
                        if hint_count > params.omega || c_tilde != c_tilde_prime {
                            Err(MlDsaError::InvalidSignature)
                        } else {
                            Ok(())
                        }
                    }
                }
            }
        }
    }
}
