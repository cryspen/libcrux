use super::{
    arithmetic::{to_unsigned_representative, PolynomialRingElement},
    constants::{BYTES_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT, SHARED_SECRET_SIZE},
    hash_functions::{G, PRF},
    helper::cloop,
    matrix::*,
    ntt::*,
    sampling::sample_from_binomial_distribution,
    serialize::{
        compress_then_serialize_message, compress_then_serialize_ring_element_u,
        compress_then_serialize_ring_element_v, deserialize_ring_elements_reduced,
        deserialize_then_decompress_message, deserialize_then_decompress_ring_element_u,
        deserialize_then_decompress_ring_element_v, deserialize_to_uncompressed_ring_element,
        serialize_uncompressed_ring_element,
    },
};

/// Pad the `slice` with `0`s at the end.
#[inline(always)]
pub(super) fn into_padded_array<const LEN: usize>(slice: &[u8]) -> [u8; LEN] {
    debug_assert!(slice.len() <= LEN);
    let mut out = [0u8; LEN];
    out[0..slice.len()].copy_from_slice(slice);
    out
}

/// Concatenate `t` and `ρ` into the public key.
#[inline(always)]
pub(super) fn serialize_public_key<
    const K: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
>(
    t_as_ntt: [PolynomialRingElement; K],
    seed_for_a: &[u8],
) -> [u8; PUBLIC_KEY_SIZE] {
    let mut public_key_serialized = [0u8; PUBLIC_KEY_SIZE];
    public_key_serialized[0..RANKED_BYTES_PER_RING_ELEMENT].copy_from_slice(
        &serialize_secret_key::<K, RANKED_BYTES_PER_RING_ELEMENT>(t_as_ntt),
    );
    public_key_serialized[RANKED_BYTES_PER_RING_ELEMENT..].copy_from_slice(seed_for_a);
    public_key_serialized
}

/// Call [`serialize_uncompressed_ring_element`] for each ring element.
#[inline(always)]
fn serialize_secret_key<const K: usize, const OUT_LEN: usize>(
    key: [PolynomialRingElement; K],
) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];

    cloop! {
        for (i, re) in key.into_iter().enumerate() {
            out[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT]
            .copy_from_slice(&serialize_uncompressed_ring_element(re));
        }
    }

    out
}

/// Sample a vector of ring elements from a centered binomial distribution.
#[inline(always)]
fn sample_ring_element_cbd<const K: usize, const ETA2_RANDOMNESS_SIZE: usize, const ETA2: usize>(
    prf_input: &mut [u8; 33],
    domain_separator: &mut u8,
) -> [PolynomialRingElement; K] {
    let mut error_1 = [PolynomialRingElement::ZERO; K];
    for i in 0..K {
        prf_input[32] = *domain_separator;
        *domain_separator += 1;

        let prf_output: [u8; ETA2_RANDOMNESS_SIZE] = PRF(prf_input);
        error_1[i] = sample_from_binomial_distribution::<ETA2>(&prf_output);
    }
    error_1
}

/// Sample a vector of ring elements from a centered binomial distribution and
/// convert them into their NTT representations.
#[inline(always)]
fn sample_vector_cbd_then_ntt<
    const K: usize,
    const ETA: usize,
    const ETA_RANDOMNESS_SIZE: usize,
>(
    mut prf_input: [u8; 33],
    mut domain_separator: u8,
) -> ([PolynomialRingElement; K], u8) {
    let mut re_as_ntt = [PolynomialRingElement::ZERO; K];
    for i in 0..K {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output: [u8; ETA_RANDOMNESS_SIZE] = PRF(&prf_input);

        let r = sample_from_binomial_distribution::<ETA>(&prf_output);
        re_as_ntt[i] = ntt_binomially_sampled_ring_element(r);
    }
    (re_as_ntt, domain_separator)
}

/// This function implements most of <strong>Algorithm 12</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation algorithm.
///
/// We say "most of" since Algorithm 12 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `key_generation_seed` parameter.
///
/// Algorithm 12 is reproduced below:
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
///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
///     end for
/// end for
/// for(i ← 0; i < k; i++)
///     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
///     N ← N + 1
/// end for
/// for(i ← 0; i < k; i++)
///     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
///     N ← N + 1
/// end for
/// ŝ ← NTT(s)
/// ê ← NTT(e)
/// t̂ ← Â◦ŝ + ê
/// ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
/// dkₚₖₑ ← ByteEncode₁₂(ŝ)
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[allow(non_snake_case)]
pub(super) fn generate_keypair_unpacked<
    const K: usize,
    const PUBLIC_KEY_SIZE: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    key_generation_seed: &[u8],
) -> (
    (
        [PolynomialRingElement; K],
        [PolynomialRingElement; K],
        [[PolynomialRingElement; K]; K],
    ),
    [u8; PUBLIC_KEY_SIZE],
) {
    // (ρ,σ) := G(d)
    let hashed = G(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    let a_transpose = sample_matrix_A(into_padded_array(seed_for_A), true);

    let prf_input: [u8; 33] = into_padded_array(seed_for_secret_and_error);
    let (mut secret_as_ntt, domain_separator) =
        sample_vector_cbd_then_ntt::<K, ETA1, ETA1_RANDOMNESS_SIZE>(prf_input, 0);
    let (error_as_ntt, _) =
        sample_vector_cbd_then_ntt::<K, ETA1, ETA1_RANDOMNESS_SIZE>(prf_input, domain_separator);

    // tˆ := Aˆ ◦ sˆ + eˆ
    let mut t_as_ntt = compute_As_plus_e(&a_transpose, &secret_as_ntt, &error_as_ntt);

    // pk := (Encode_12(tˆ mod^{+}q) || ρ)
    let public_key_serialized = serialize_public_key::<
        K,
        RANKED_BYTES_PER_RING_ELEMENT,
        PUBLIC_KEY_SIZE,
    >(t_as_ntt, &seed_for_A);

    // Need to do the following otherwise it violates invariants in NTT (the values are expected to be >=0 and <4096).
    // Maybe we can remove these reductions later if we make those constraints looser
    for i in 0..K {
        for j in 0..COEFFICIENTS_IN_RING_ELEMENT {
            secret_as_ntt[i].coefficients[j] =
                to_unsigned_representative(secret_as_ntt[i].coefficients[j]) as i32;
            t_as_ntt[i].coefficients[j] =
                to_unsigned_representative(t_as_ntt[i].coefficients[j]) as i32;
        }
    }

    // We also need to transpose the A array.
    let mut a_matrix = a_transpose;
    for i in 0..K {
        for j in 0..K {
            a_matrix[i][j] = a_transpose[j][i];
        }
    }

    ((secret_as_ntt, t_as_ntt, a_matrix), public_key_serialized)
}

#[allow(non_snake_case)]
pub(super) fn generate_keypair<
    const K: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    key_generation_seed: &[u8],
) -> ([u8; PRIVATE_KEY_SIZE], [u8; PUBLIC_KEY_SIZE]) {
    let ((secret_as_ntt, _t_as_ntt, _a_transpose), public_key_serialized) =
        generate_keypair_unpacked::<
            K,
            PUBLIC_KEY_SIZE,
            RANKED_BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(key_generation_seed);

    // sk := Encode_12(sˆ mod^{+}q)
    let secret_key_serialized = serialize_secret_key(secret_as_ntt);

    (secret_key_serialized, public_key_serialized)
}

/// Call [`compress_then_serialize_ring_element_u`] on each ring element.
fn compress_then_serialize_u<
    const K: usize,
    const OUT_LEN: usize,
    const COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
>(
    input: [PolynomialRingElement; K],
) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    cloop! {
        for (i, re) in input.into_iter().enumerate() {
            out[i * (OUT_LEN / K)..(i + 1) * (OUT_LEN / K)].copy_from_slice(
                &compress_then_serialize_ring_element_u::<COMPRESSION_FACTOR, BLOCK_LEN>(re),
            );
        }
    }

    out
}

/// This function implements <strong>Algorithm 13</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.
///
/// Algorithm 13 is reproduced below:
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
///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
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
/// u ← NTT-¹(Âᵀ ◦ r̂) + e₁
/// μ ← Decompress₁(ByteDecode₁(m)))
/// v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
/// c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
/// c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
/// return c ← (c₁ ‖ c₂)
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[allow(non_snake_case)]
pub(crate) fn encrypt_unpacked<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_LEN: usize,
    const C2_LEN: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
>(
    t_as_ntt: &[PolynomialRingElement; K],
    a_transpose: &[[PolynomialRingElement; K]; K],
    message: [u8; SHARED_SECRET_SIZE],
    randomness: &[u8],
) -> [u8; CIPHERTEXT_SIZE] {
    // for i from 0 to k−1 do
    //     r[i] := CBD{η1}(PRF(r, N))
    //     N := N + 1
    // end for
    // rˆ := NTT(r)
    let mut prf_input: [u8; 33] = into_padded_array(randomness);
    let (r_as_ntt, mut domain_separator) =
        sample_vector_cbd_then_ntt::<K, ETA1, ETA1_RANDOMNESS_SIZE>(prf_input, 0);

    // for i from 0 to k−1 do
    //     e1[i] := CBD_{η2}(PRF(r,N))
    //     N := N + 1
    // end for
    let error_1 = sample_ring_element_cbd::<K, ETA2_RANDOMNESS_SIZE, ETA2>(
        &mut prf_input,
        &mut domain_separator,
    );

    // e_2 := CBD{η2}(PRF(r, N))
    prf_input[32] = domain_separator;
    let prf_output: [u8; ETA2_RANDOMNESS_SIZE] = PRF(&prf_input);
    let error_2 = sample_from_binomial_distribution::<ETA2>(&prf_output);

    // u := NTT^{-1}(AˆT ◦ rˆ) + e_1
    let u = compute_vector_u(&a_transpose, &r_as_ntt, &error_1);

    // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
    let message_as_ring_element = deserialize_then_decompress_message(message);
    let v = compute_ring_element_v(&t_as_ntt, &r_as_ntt, &error_2, &message_as_ring_element);

    // c_1 := Encode_{du}(Compress_q(u,d_u))
    let c1 = compress_then_serialize_u::<K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN>(u);

    // c_2 := Encode_{dv}(Compress_q(v,d_v))
    let c2 = compress_then_serialize_ring_element_v::<V_COMPRESSION_FACTOR, C2_LEN>(v);

    let mut ciphertext: [u8; CIPHERTEXT_SIZE] = into_padded_array(&c1);
    ciphertext[C1_LEN..].copy_from_slice(c2.as_slice());

    ciphertext
}

#[allow(non_snake_case)]
pub(crate) fn encrypt<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_LEN: usize,
    const C2_LEN: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
>(
    public_key: &[u8],
    message: [u8; SHARED_SECRET_SIZE],
    randomness: &[u8],
) -> [u8; CIPHERTEXT_SIZE] {
    // tˆ := Decode_12(pk)
    let t_as_ntt = deserialize_ring_elements_reduced::<T_AS_NTT_ENCODED_SIZE, K>(
        &public_key[..T_AS_NTT_ENCODED_SIZE],
    );

    // ρ := pk + 12·k·n / 8
    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         AˆT[i][j] := Parse(XOF(ρ, i, j))
    //     end for
    // end for
    let seed = &public_key[T_AS_NTT_ENCODED_SIZE..];
    // ρ := pk + 12·k·n / 8
    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         AˆT[i][j] := Parse(XOF(ρ, i, j))
    //     end for
    // end for
    let a_transpose = sample_matrix_A(into_padded_array(seed), false);

    encrypt_unpacked::<
        K,
        CIPHERTEXT_SIZE,
        T_AS_NTT_ENCODED_SIZE,
        C1_LEN,
        C2_LEN,
        U_COMPRESSION_FACTOR,
        V_COMPRESSION_FACTOR,
        BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
    >(&t_as_ntt, &a_transpose, message, randomness)
}

/// Call [`deserialize_then_decompress_ring_element_u`] on each ring element
/// in the `ciphertext`.
#[inline(always)]
fn deserialize_then_decompress_u<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
>(
    ciphertext: &[u8; CIPHERTEXT_SIZE],
) -> [PolynomialRingElement; K] {
    let mut u_as_ntt = [PolynomialRingElement::ZERO; K];
    cloop! {
        for (i, u_bytes) in ciphertext
            .chunks_exact((COEFFICIENTS_IN_RING_ELEMENT * U_COMPRESSION_FACTOR) / 8)
            .enumerate()
        {
            let u = deserialize_then_decompress_ring_element_u::<U_COMPRESSION_FACTOR>(u_bytes);
            u_as_ntt[i] = ntt_vector_u::<U_COMPRESSION_FACTOR>(u);
        }
    }
    u_as_ntt
}

/// Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
#[inline(always)]
fn deserialize_secret_key<const K: usize>(secret_key: &[u8]) -> [PolynomialRingElement; K] {
    let mut secret_as_ntt = [PolynomialRingElement::ZERO; K];
    cloop! {
        for (i, secret_bytes) in secret_key.chunks_exact(BYTES_PER_RING_ELEMENT).enumerate() {
            secret_as_ntt[i] = deserialize_to_uncompressed_ring_element(secret_bytes);
        }
    }
    secret_as_ntt
}

/// This function implements <strong>Algorithm 14</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.
///
/// Algorithm 14 is reproduced below:
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
/// w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
/// m ← ByteEncode₁(Compress₁(w))
/// return m
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[allow(non_snake_case)]
pub(super) fn decrypt_unpacked<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const VECTOR_U_ENCODED_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
>(
    secret_as_ntt: &[PolynomialRingElement; K],
    ciphertext: &[u8; CIPHERTEXT_SIZE],
) -> [u8; SHARED_SECRET_SIZE] {
    // u := Decompress_q(Decode_{d_u}(c), d_u)
    let u_as_ntt =
        deserialize_then_decompress_u::<K, CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR>(ciphertext);

    // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
    let v = deserialize_then_decompress_ring_element_v::<V_COMPRESSION_FACTOR>(
        &ciphertext[VECTOR_U_ENCODED_SIZE..],
    );

    // m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
    let message = compute_message(&v, &secret_as_ntt, &u_as_ntt);
    compress_then_serialize_message(message)
}

#[allow(non_snake_case)]
pub(super) fn decrypt<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const VECTOR_U_ENCODED_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
>(
    secret_key: &[u8],
    ciphertext: &[u8; CIPHERTEXT_SIZE],
) -> [u8; SHARED_SECRET_SIZE] {
    // sˆ := Decode_12(sk)
    let secret_as_ntt = deserialize_secret_key::<K>(secret_key);

    decrypt_unpacked::<
        K,
        CIPHERTEXT_SIZE,
        VECTOR_U_ENCODED_SIZE,
        U_COMPRESSION_FACTOR,
        V_COMPRESSION_FACTOR,
    >(&secret_as_ntt, ciphertext)
}
