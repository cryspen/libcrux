use crate::{
    compress::{compress, decompress},
    matrix::{
        add_polynomials, add_vectors, multiply_matrix_by_column, multiply_vectors, sub_polynomials,
        transpose,
    },
    ntt::{ntt_inverse, vector_inverse_ntt, vector_ntt},
    parameters::{hash_functions::*, *},
    sampling::{sample_ntt, sample_poly_cbd, BadRejectionSamplingRandomnessError},
    serialize::{
        byte_decode, byte_decode_dyn, byte_encode, byte_encode_into, vector_decode_12,
        vector_encode_12,
    },
};

/// Helper to sample a polynomial from CBD with dynamic eta.
#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(eta == 2 || eta == 3)]
fn sample_secret(eta: usize, prf_input: &[u8; 33]) -> Polynomial {
    match eta {
        2 => {
            let out: [u8; 128] = PRF(prf_input);
            sample_poly_cbd::<128, 1024>(2, &out)
        }
        3 => {
            let out: [u8; 192] = PRF(prf_input);
            sample_poly_cbd::<192, 1536>(3, &out)
        }
        _ => panic!("unsupported eta={}", eta),
    }
}

#[hax_lib::requires(N1 > 0 && N == N1 - 1)]
fn concat_byte<const N: usize, const N1:usize>(a: &[u8; N], b: u8) -> [u8; N1] {
    let mut result = [0u8; N1];
    result[..N].copy_from_slice(a);
    result[N] = b;
    result
}

/// Algorithm 13: K-PKE.KeyGen
///
/// Generates an encryption key and a corresponding decryption key.
///
/// ```plaintext
/// Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
///
/// d ←$ B
/// (ρ,σ) ← G(d)
/// N ← 0
/// for (i ← 0; i < k; i++)
///     for(j ← 0; j < k; j++)
///         Â[i,j] ← SampleNTT(XOF(ρ, j, i))
///     end for
/// end for
/// for(i ← 0; i < k; i++)
///     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
///     N ← N + 1
/// end for
/// for(i ← 0; i < k; i++)
///     e[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
///     N ← N + 1
/// end for
/// ŝ ← NTT(s)
/// ê ← NTT(e)
/// t̂ ← Â◦ŝ + ê
/// ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
/// dkₚₖₑ ← ByteEncode₁₂(ŝ)
/// ```
#[allow(non_snake_case)]
#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(
    RANK <= 4 && params.rank == RANK
    && EK_SIZE == RANK * BYTES_PER_RING_ELEMENT + 32
    && DK_PKE_SIZE == RANK * BYTES_PER_RING_ELEMENT
    && (params.eta1 == 2 || params.eta1 == 3)
)]
pub(crate) fn generate_keypair<
    const RANK: usize,
    const EK_SIZE: usize,
    const DK_PKE_SIZE: usize,
>(
    params: &MlKemParams,
    key_generation_seed: &[u8; 32],
) -> Result<([u8; EK_SIZE], [u8; DK_PKE_SIZE]), BadRejectionSamplingRandomnessError> {
    hax_lib::debug_assert!(
        EK_SIZE == RANK * BYTES_PER_RING_ELEMENT + 32
            && DK_PKE_SIZE == RANK * BYTES_PER_RING_ELEMENT
    );
    // (ρ,σ) ← G(d ‖ k)
    let mut g_input = [0u8; 33];
    g_input[..32].copy_from_slice(key_generation_seed);
    g_input[32] = RANK as u8;
    let hashed = G(&g_input);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    // Â[i,j] ← SampleNTT(XOF(ρ, i, j))
    let mut A_as_ntt: Matrix<RANK> = [[[0i16; 256]; RANK]; RANK];

    let mut xof_input = [0u8; 34];
    xof_input[..32].copy_from_slice(seed_for_A);

    for i in 0..RANK {
        for j in 0..RANK {
            xof_input[32] = i as u8;
            xof_input[33] = j as u8;
            let xof_bytes: [u8; REJECTION_SAMPLING_SEED_SIZE] = XOF(&xof_input);
            A_as_ntt[i][j] = sample_ntt::<70, 560, 840, 6720>(xof_bytes)?;
        }
    }

    // s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
    let mut secret: Vector<RANK> = [[0i16; 256]; RANK];

    let secret = createi(|i| {
        let prf_input= concat_byte::<32,33>(seed_for_secret_and_error.try_into().unwrap(), i as u8);
        sample_secret(params.eta1, &prf_input)
    });

    // e[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
    let error = createi(|i| {
        let prf_input : [u8; 33]= concat_byte::<32,33>(seed_for_secret_and_error.try_into().unwrap(), 
                                              (RANK + i) as u8);
        sample_secret(params.eta1, &prf_input)
    });

    // ŝ ← NTT(s)
    let secret_as_ntt = vector_ntt(secret);

    // ê ← NTT(e)
    let error_as_ntt = vector_ntt(error);

    // t̂ ← Â◦ŝ + ê
    let t_as_ntt = add_vectors(
        &multiply_matrix_by_column(&A_as_ntt, &secret_as_ntt),
        &error_as_ntt,
    );

    // ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
    let t_encoded: [u8; DK_PKE_SIZE] = vector_encode_12::<RANK, DK_PKE_SIZE>(&t_as_ntt);
    let mut ek = [0u8; EK_SIZE];
    ek[..DK_PKE_SIZE].copy_from_slice(&t_encoded);
    ek[DK_PKE_SIZE..].copy_from_slice(seed_for_A);

    // dkₚₖₑ ← ByteEncode₁₂(ŝ)
    let dk: [u8; DK_PKE_SIZE] = vector_encode_12::<RANK, DK_PKE_SIZE>(&secret_as_ntt);

    Ok((ek, dk))
}

/// Algorithm 14: K-PKE.Encrypt
///
/// Uses the encryption key to encrypt a plaintext message using the randomness r.
///
/// ```plaintext
/// Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Input: message m ∈ 𝔹^{32}.
/// Input: encryption randomness r ∈ 𝔹^{32}.
/// Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
///
/// N ← 0
/// t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
/// ρ ← ekₚₖₑ[384k: 384k + 32]
/// for (i ← 0; i < k; i++)
///     for(j ← 0; j < k; j++)
///         Â[i,j] ← SampleNTT(XOF(ρ, j, i))
///     end for
/// end for
/// for(i ← 0; i < k; i++)
///     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
///     N ← N + 1
/// end for
/// for(i ← 0; i < k; i++)
///     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
///     N ← N + 1
/// end for
/// e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
/// r̂ ← NTT(r)
/// u ← NTT⁻¹(Âᵀ ◦ r̂) + e₁
/// μ ← Decompress₁(ByteDecode₁(m))
/// v ← NTT⁻¹(t̂ᵀ ◦ r̂) + e₂ + μ
/// c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
/// c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
/// return c ← (c₁ ‖ c₂)
/// ```
#[allow(non_snake_case)]
#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(
    RANK <= 4 && params.rank == RANK
    && CT_SIZE == (RANK * COEFFICIENTS_IN_RING_ELEMENT * params.du + COEFFICIENTS_IN_RING_ELEMENT * params.dv) / 8
    && ek.len() == RANK * BYTES_PER_RING_ELEMENT + 32
    && (params.eta1 == 2 || params.eta1 == 3)
    && (params.eta2 == 2 || params.eta2 == 3)
)]
pub(crate) fn encrypt<const RANK: usize, const CT_SIZE: usize>(
    params: &MlKemParams,
    ek: &[u8],
    message: &[u8; 32],
    randomness: &[u8; 32],
) -> Result<[u8; CT_SIZE], BadRejectionSamplingRandomnessError> {
    hax_lib::debug_assert!(
        CT_SIZE
            == (RANK * COEFFICIENTS_IN_RING_ELEMENT * params.du
                + COEFFICIENTS_IN_RING_ELEMENT * params.dv)
                / 8
            && ek.len() == RANK * BYTES_PER_RING_ELEMENT + 32
    );

    let t_encoded_size = params.t_as_ntt_encoded_size();

    // t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
    let t_as_ntt: Vector<RANK> = vector_decode_12::<RANK>(&ek[..t_encoded_size]);

    // ρ ← ekₚₖₑ[384k: 384k + 32]
    let seed_for_A = &ek[t_encoded_size..];

    // Â[i,j] ← SampleNTT(XOF(ρ, j, i))
    let mut A_as_ntt = [[[0; 256]; RANK]; RANK];
    let mut xof_input = [0u8; 34];
    xof_input[..32].copy_from_slice(seed_for_A);

    for i in 0..RANK {
        for j in 0..RANK {
            xof_input[32] = j as u8;
            xof_input[33] = i as u8;
            let xof_bytes: [u8; REJECTION_SAMPLING_SEED_SIZE] = XOF(&xof_input);
            A_as_ntt[j][i] = sample_ntt::<70, 560, 840, 6720>(xof_bytes)?;
        }
    }
    // let A_as_ntt = createi(|i:usize| createi (|j:usize| {
    //      xof_input[32] = i as u8;
    //      xof_input[33] = j as u8;
    //      let xof_bytes: [u8; REJECTION_SAMPLING_SEED_SIZE] = XOF(&xof_input);
    //      sample_ntt::<70, 560, 840, 6720>(xof_bytes)?
    // }));
    

    // r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
    let r = createi(|i| {
        let prf_input : [u8; 33]= concat_byte(randomness.try_into().unwrap(), i as u8);
        sample_secret(params.eta1, &prf_input)
    });

    // e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
    let error_1 = createi(|i| {
        let prf_input : [u8; 33]= concat_byte(randomness.try_into().unwrap(), (RANK + i) as u8);
        sample_secret(params.eta2, &prf_input)
    });

    // e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
    let mut prf_input = [0u8; 33];
    prf_input[..32].copy_from_slice(randomness);
    prf_input[32] = (RANK * 2) as u8;
    let error_2 = sample_secret(params.eta2, &prf_input);

    // r̂ ← NTT(r)
    let r_as_ntt = vector_ntt(r);

    // u ← NTT⁻¹(Âᵀ ◦ r̂) + e₁
    let A_transpose = transpose(&A_as_ntt);
    let u = add_vectors(
        &vector_inverse_ntt(multiply_matrix_by_column(&A_transpose, &r_as_ntt)),
        &error_1,
    );

    // μ ← Decompress₁(ByteDecode₁(m))
    let message_as_ring_element = decompress(byte_decode::<32, 256>(message, 1), 1);

    // v ← NTT⁻¹(t̂ᵀ ◦ r̂) + e₂ + μ
    let v = add_polynomials(
        &add_polynomials(
            &ntt_inverse(multiply_vectors(&t_as_ntt, &r_as_ntt)),
            &error_2,
        ),
        &message_as_ring_element,
    );

    // c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
    let du_poly_size = (COEFFICIENTS_IN_RING_ELEMENT * params.du) / 8;
    let mut c = [0u8; CT_SIZE];
    for i in 0..RANK {
        byte_encode_into(
            compress(u[i], params.du),
            params.du,
            &mut c[i * du_poly_size..(i + 1) * du_poly_size],
        );
    }

    // c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
    let u_encoded_size = RANK * du_poly_size;
    byte_encode_into(compress(v, params.dv), params.dv, &mut c[u_encoded_size..]);

    Ok(c)
}

/// Algorithm 15: K-PKE.Decrypt
///
/// Uses the decryption key to decrypt a ciphertext.
///
/// ```plaintext
/// Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
/// Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
/// Output: message m ∈ 𝔹^{32}.
///
/// c₁ ← c[0 : 32dᵤk]
/// c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
/// u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
/// v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
/// ŝ ← ByteDecode₁₂(dkₚₖₑ)
/// w ← v - NTT⁻¹(ŝᵀ ◦ NTT(u))
/// m ← ByteEncode₁(Compress₁(w))
/// return m
/// ```
#[allow(non_snake_case)]
#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(
    RANK <= 4 && params.rank == RANK
    && dk.len() == RANK * BYTES_PER_RING_ELEMENT
    && ciphertext.len() == (RANK * COEFFICIENTS_IN_RING_ELEMENT * params.du + COEFFICIENTS_IN_RING_ELEMENT * params.dv) / 8
)]
pub(crate) fn decrypt<const RANK: usize>(
    params: &MlKemParams,
    dk: &[u8],
    ciphertext: &[u8],
) -> [u8; 32] {
    hax_lib::fstar!("admit()");
    hax_lib::debug_assert!(
        dk.len() == RANK * BYTES_PER_RING_ELEMENT
            && ciphertext.len()
                == (RANK * COEFFICIENTS_IN_RING_ELEMENT * params.du
                    + COEFFICIENTS_IN_RING_ELEMENT * params.dv)
                    / 8
    );
    let u_encoded_size = params.u_encoded_size();
    let du_poly_size = (COEFFICIENTS_IN_RING_ELEMENT * params.du) / 8;

    // u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
    let u: Vector<RANK> = createi(|i| {
        let start = i * du_poly_size;
        decompress(
            byte_decode_dyn(&ciphertext[start..start + du_poly_size], params.du),
            params.du,
        )
    });

    // v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
    let v = decompress(
        byte_decode_dyn(&ciphertext[u_encoded_size..], params.dv),
        params.dv,
    );

    // ŝ ← ByteDecode₁₂(dkₚₖₑ)
    let secret_as_ntt: Vector<RANK> = vector_decode_12::<RANK>(dk);

    // w ← v - NTT⁻¹(ŝᵀ ◦ NTT(u))
    let u_as_ntt = vector_ntt(u);
    let w = sub_polynomials(
        &v,
        &ntt_inverse(multiply_vectors(&secret_as_ntt, &u_as_ntt)),
    );

    // m ← ByteEncode₁(Compress₁(w))
    byte_encode::<32, 256>(compress(w, 1), 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encrypt_decrypt_roundtrip() {
        let seed = [42u8; 32];
        let (ek, dk) = generate_keypair::<3, { ML_KEM_768_EK_SIZE }, { ML_KEM_768_DK_PKE_SIZE }>(
            &ML_KEM_768,
            &seed,
        )
        .unwrap();

        let message = [0xABu8; 32];
        let randomness = [0xCDu8; 32];
        let ciphertext =
            encrypt::<3, { ML_KEM_768_CT_SIZE }>(&ML_KEM_768, &ek, &message, &randomness).unwrap();
        let decrypted = decrypt::<3>(&ML_KEM_768, &dk, &ciphertext);

        assert_eq!(decrypted, message);
    }

    #[test]
    fn encrypt_deterministic() {
        let seed = [1u8; 32];
        let (ek, _dk) = generate_keypair::<3, { ML_KEM_768_EK_SIZE }, { ML_KEM_768_DK_PKE_SIZE }>(
            &ML_KEM_768,
            &seed,
        )
        .unwrap();

        let message = [0x55u8; 32];
        let randomness = [0x77u8; 32];
        let c1 =
            encrypt::<3, { ML_KEM_768_CT_SIZE }>(&ML_KEM_768, &ek, &message, &randomness).unwrap();
        let c2 =
            encrypt::<3, { ML_KEM_768_CT_SIZE }>(&ML_KEM_768, &ek, &message, &randomness).unwrap();

        assert_eq!(c1, c2);
    }

    #[test]
    fn decrypt_with_wrong_key() {
        let seed1 = [1u8; 32];
        let seed2 = [2u8; 32];
        let (ek, _dk1) = generate_keypair::<3, { ML_KEM_768_EK_SIZE }, { ML_KEM_768_DK_PKE_SIZE }>(
            &ML_KEM_768,
            &seed1,
        )
        .unwrap();
        let (_ek2, dk2) =
            generate_keypair::<3, { ML_KEM_768_EK_SIZE }, { ML_KEM_768_DK_PKE_SIZE }>(
                &ML_KEM_768,
                &seed2,
            )
            .unwrap();

        let message = [0xAAu8; 32];
        let randomness = [0xBBu8; 32];
        let ciphertext =
            encrypt::<3, { ML_KEM_768_CT_SIZE }>(&ML_KEM_768, &ek, &message, &randomness).unwrap();
        let decrypted = decrypt::<3>(&ML_KEM_768, &dk2, &ciphertext);

        assert_ne!(decrypted, message);
    }
}
