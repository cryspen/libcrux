use core::array::from_fn;

use crate::{
    constants::{BYTES_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT, SHARED_SECRET_SIZE},
    hash_functions::Hash,
    helper::cloop,
    matrix::*,
    ntt::{ntt_binomially_sampled_ring_element, ntt_vector_u},
    polynomial::PolynomialRingElement,
    sampling::sample_from_binomial_distribution,
    serialize::{
        compress_then_serialize_message, compress_then_serialize_ring_element_u,
        compress_then_serialize_ring_element_v, deserialize_ring_elements_reduced,
        deserialize_then_decompress_message, deserialize_then_decompress_ring_element_u,
        deserialize_then_decompress_ring_element_v, deserialize_to_uncompressed_ring_element,
        serialize_uncompressed_ring_element,
    },
    utils::into_padded_array,
    variant::Variant,
    vector::Operations,
};

/// Types for the unpacked API.
#[allow(non_snake_case)]
pub mod unpacked {
    use crate::{polynomial::PolynomialRingElement, vector::traits::Operations};

    /// An unpacked ML-KEM IND-CPA Private Key
    pub(crate) struct IndCpaPrivateKeyUnpacked<const K: usize, Vector: Operations> {
        pub(crate) secret_as_ntt: [PolynomialRingElement<Vector>; K],
    }

    impl<const K: usize, Vector: Operations> Default for IndCpaPrivateKeyUnpacked<K, Vector> {
        fn default() -> Self {
            Self {
                secret_as_ntt: [PolynomialRingElement::<Vector>::ZERO(); K],
            }
        }
    }

    /// An unpacked ML-KEM IND-CPA Private Key
    #[derive(Clone)]
    pub(crate) struct IndCpaPublicKeyUnpacked<const K: usize, Vector: Operations> {
        pub(crate) t_as_ntt: [PolynomialRingElement<Vector>; K],
        pub(crate) seed_for_A: [u8; 32],
        pub(crate) A: [[PolynomialRingElement<Vector>; K]; K],
    }

    impl<const K: usize, Vector: Operations> Default for IndCpaPublicKeyUnpacked<K, Vector> {
        fn default() -> Self {
            Self {
                t_as_ntt: [PolynomialRingElement::<Vector>::ZERO(); K],
                seed_for_A: [0u8; 32],
                A: [[PolynomialRingElement::<Vector>::ZERO(); K]; K],
            }
        }
    }
}
use unpacked::*;

/// Concatenate `t` and `ρ` into the public key.
#[inline(always)]
pub(crate) fn serialize_public_key<
    const K: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
    Vector: Operations,
>(
    t_as_ntt: &[PolynomialRingElement<Vector>; K],
    seed_for_a: &[u8],
) -> [u8; PUBLIC_KEY_SIZE] {
    let mut public_key_serialized = [0u8; PUBLIC_KEY_SIZE];
    serialize_public_key_mut::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(
        t_as_ntt,
        seed_for_a,
        &mut public_key_serialized,
    );
    public_key_serialized
}

/// Concatenate `t` and `ρ` into the public key.
#[inline(always)]
pub(crate) fn serialize_public_key_mut<
    const K: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
    Vector: Operations,
>(
    t_as_ntt: &[PolynomialRingElement<Vector>; K],
    seed_for_a: &[u8],
    serialized: &mut [u8; PUBLIC_KEY_SIZE],
) {
    serialized[0..RANKED_BYTES_PER_RING_ELEMENT].copy_from_slice(&serialize_secret_key::<
        K,
        RANKED_BYTES_PER_RING_ELEMENT,
        Vector,
    >(t_as_ntt));
    serialized[RANKED_BYTES_PER_RING_ELEMENT..].copy_from_slice(seed_for_a);
}

/// Call [`serialize_uncompressed_ring_element`] for each ring element.
#[inline(always)]
pub(crate) fn serialize_secret_key<const K: usize, const OUT_LEN: usize, Vector: Operations>(
    key: &[PolynomialRingElement<Vector>; K],
) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];

    cloop! {
        for (i, re) in key.into_iter().enumerate() {
            out[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT]
            .copy_from_slice(&serialize_uncompressed_ring_element(&re));
        }
    }

    out
}

/// Sample a vector of ring elements from a centered binomial distribution.
#[inline(always)]
fn sample_ring_element_cbd<
    const K: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    Vector: Operations,
    Hasher: Hash<K>,
>(
    prf_input: [u8; 33],
    mut domain_separator: u8,
) -> ([PolynomialRingElement<Vector>; K], u8) {
    let mut error_1 = from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
    let mut prf_inputs = [prf_input; K];
    for i in 0..K {
        prf_inputs[i][32] = domain_separator;
        domain_separator += 1;
    }
    let prf_outputs: [[u8; ETA2_RANDOMNESS_SIZE]; K] = Hasher::PRFxN(&prf_inputs);
    for i in 0..K {
        error_1[i] = sample_from_binomial_distribution::<ETA2, Vector>(&prf_outputs[i]);
    }
    (error_1, domain_separator)
}

/// Sample a vector of ring elements from a centered binomial distribution and
/// convert them into their NTT representations.
#[inline(always)]
fn sample_vector_cbd_then_ntt<
    const K: usize,
    const ETA: usize,
    const ETA_RANDOMNESS_SIZE: usize,
    Vector: Operations,
    Hasher: Hash<K>,
>(
    re_as_ntt: &mut [PolynomialRingElement<Vector>; K],
    prf_input: [u8; 33],
    mut domain_separator: u8,
) -> u8 {
    let mut prf_inputs = [prf_input; K];
    for i in 0..K {
        prf_inputs[i][32] = domain_separator;
        domain_separator += 1;
    }
    let prf_outputs: [[u8; ETA_RANDOMNESS_SIZE]; K] = Hasher::PRFxN(&prf_inputs);
    for i in 0..K {
        re_as_ntt[i] = sample_from_binomial_distribution::<ETA, Vector>(&prf_outputs[i]);
        ntt_binomially_sampled_ring_element(&mut re_as_ntt[i]);
    }
    domain_separator
}

#[inline(always)]
fn sample_vector_cbd_then_ntt_out<
    const K: usize,
    const ETA: usize,
    const ETA_RANDOMNESS_SIZE: usize,
    Vector: Operations,
    Hasher: Hash<K>,
>(
    prf_input: [u8; 33],
    mut domain_separator: u8,
) -> ([PolynomialRingElement<Vector>; K], u8) {
    let mut re_as_ntt = from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
    domain_separator = sample_vector_cbd_then_ntt::<K, ETA, ETA_RANDOMNESS_SIZE, Vector, Hasher>(
        &mut re_as_ntt,
        prf_input,
        domain_separator,
    );
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
pub(crate) fn generate_keypair_unpacked<
    const K: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    Vector: Operations,
    Hasher: Hash<K>,
    Scheme: Variant,
>(
    key_generation_seed: &[u8],
    private_key: &mut IndCpaPrivateKeyUnpacked<K, Vector>,
    public_key: &mut IndCpaPublicKeyUnpacked<K, Vector>,
) {
    // (ρ,σ) := G(d) for Kyber, (ρ,σ) := G(d || K) for ML-KEM
    let hashed = Scheme::cpa_keygen_seed::<K, Hasher>(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    sample_matrix_A::<K, Vector, Hasher>(&mut public_key.A, into_padded_array(seed_for_A), true);

    let prf_input: [u8; 33] = into_padded_array(seed_for_secret_and_error);
    let domain_separator =
        sample_vector_cbd_then_ntt::<K, ETA1, ETA1_RANDOMNESS_SIZE, Vector, Hasher>(
            &mut private_key.secret_as_ntt,
            prf_input,
            0,
        );
    let (error_as_ntt, _) =
        sample_vector_cbd_then_ntt_out::<K, ETA1, ETA1_RANDOMNESS_SIZE, Vector, Hasher>(
            prf_input,
            domain_separator,
        );

    // tˆ := Aˆ ◦ sˆ + eˆ
    compute_As_plus_e(
        &mut public_key.t_as_ntt,
        &public_key.A,
        &private_key.secret_as_ntt,
        &error_as_ntt,
    );

    public_key.seed_for_A = seed_for_A.try_into().unwrap();

    // For encapsulation, we need to store A not Aˆ, and so we untranspose A
    // However, we pass A_transpose here and let the IND-CCA layer do the untranspose.
    // We could do it here, but then we would pay the performance cost (if any) for the packed API as well.
}

#[allow(non_snake_case)]
pub(crate) fn generate_keypair<
    const K: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    Vector: Operations,
    Hasher: Hash<K>,
    Scheme: Variant,
>(
    key_generation_seed: &[u8],
) -> ([u8; PRIVATE_KEY_SIZE], [u8; PUBLIC_KEY_SIZE]) {
    let mut private_key = IndCpaPrivateKeyUnpacked::default();
    let mut public_key = IndCpaPublicKeyUnpacked::default();

    generate_keypair_unpacked::<K, ETA1, ETA1_RANDOMNESS_SIZE, Vector, Hasher, Scheme>(
        key_generation_seed,
        &mut private_key,
        &mut public_key,
    );

    // pk := (Encode_12(tˆ mod^{+}q) || ρ)
    let public_key_serialized =
        serialize_public_key::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(
            &public_key.t_as_ntt,
            &public_key.seed_for_A,
        );

    // sk := Encode_12(sˆ mod^{+}q)
    let secret_key_serialized = serialize_secret_key(&private_key.secret_as_ntt);

    (secret_key_serialized, public_key_serialized)
}

/// Call [`compress_then_serialize_ring_element_u`] on each ring element.
fn compress_then_serialize_u<
    const K: usize,
    const OUT_LEN: usize,
    const COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    Vector: Operations,
>(
    input: [PolynomialRingElement<Vector>; K],
    out: &mut [u8],
) {
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    cloop! {
        for (i, re) in input.into_iter().enumerate() {
            out[i * (OUT_LEN / K)..(i + 1) * (OUT_LEN / K)].copy_from_slice(
                &compress_then_serialize_ring_element_u::<COMPRESSION_FACTOR, BLOCK_LEN, Vector>(&re),
            );
        }
    };
    ()
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
    Vector: Operations,
    Hasher: Hash<K>,
>(
    public_key: &IndCpaPublicKeyUnpacked<K, Vector>,
    message: [u8; SHARED_SECRET_SIZE],
    randomness: &[u8],
) -> [u8; CIPHERTEXT_SIZE] {
    // for i from 0 to k−1 do
    //     r[i] := CBD{η1}(PRF(r, N))
    //     N := N + 1
    // end for
    // rˆ := NTT(r)
    let mut prf_input: [u8; 33] = into_padded_array(randomness);
    let (r_as_ntt, domain_separator) =
        sample_vector_cbd_then_ntt_out::<K, ETA1, ETA1_RANDOMNESS_SIZE, Vector, Hasher>(
            prf_input, 0,
        );

    // for i from 0 to k−1 do
    //     e1[i] := CBD_{η2}(PRF(r,N))
    //     N := N + 1
    // end for
    let (error_1, domain_separator) =
        sample_ring_element_cbd::<K, ETA2_RANDOMNESS_SIZE, ETA2, Vector, Hasher>(
            prf_input,
            domain_separator,
        );

    // e_2 := CBD{η2}(PRF(r, N))
    prf_input[32] = domain_separator;
    let prf_output: [u8; ETA2_RANDOMNESS_SIZE] = Hasher::PRF(&prf_input);
    let error_2 = sample_from_binomial_distribution::<ETA2, Vector>(&prf_output);

    // u := NTT^{-1}(AˆT ◦ rˆ) + e_1
    let u = compute_vector_u(&public_key.A, &r_as_ntt, &error_1);

    // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
    let message_as_ring_element = deserialize_then_decompress_message(message);
    let v = compute_ring_element_v(
        &public_key.t_as_ntt,
        &r_as_ntt,
        &error_2,
        &message_as_ring_element,
    );

    let mut ciphertext = [0u8; CIPHERTEXT_SIZE];

    // c_1 := Encode_{du}(Compress_q(u,d_u))
    compress_then_serialize_u::<K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, Vector>(
        u,
        &mut ciphertext[0..C1_LEN],
    );

    // c_2 := Encode_{dv}(Compress_q(v,d_v))
    compress_then_serialize_ring_element_v::<V_COMPRESSION_FACTOR, C2_LEN, Vector>(
        v,
        &mut ciphertext[C1_LEN..],
    );

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
    Vector: Operations,
    Hasher: Hash<K>,
>(
    public_key: &[u8],
    message: [u8; SHARED_SECRET_SIZE],
    randomness: &[u8],
) -> [u8; CIPHERTEXT_SIZE] {
    let mut unpacked_public_key = IndCpaPublicKeyUnpacked::<K, Vector>::default();

    // tˆ := Decode_12(pk)
    deserialize_ring_elements_reduced::<T_AS_NTT_ENCODED_SIZE, K, Vector>(
        &public_key[..T_AS_NTT_ENCODED_SIZE],
        &mut unpacked_public_key.t_as_ntt,
    );

    // ρ := pk + 12·k·n / 8
    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         AˆT[i][j] := Parse(XOF(ρ, i, j))
    //     end for
    // end for
    let seed = &public_key[T_AS_NTT_ENCODED_SIZE..];
    sample_matrix_A::<K, Vector, Hasher>(
        &mut unpacked_public_key.A,
        into_padded_array(seed),
        false,
    );

    // After unpacking the public key we can now call the unpacked decryption.
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
        Vector,
        Hasher,
    >(&unpacked_public_key, message, randomness)
}

/// Call [`deserialize_then_decompress_ring_element_u`] on each ring element
/// in the `ciphertext`.
#[inline(always)]
fn deserialize_then_decompress_u<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    ciphertext: &[u8; CIPHERTEXT_SIZE],
) -> [PolynomialRingElement<Vector>; K] {
    let mut u_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
    cloop! {
        for (i, u_bytes) in ciphertext
            .chunks_exact((COEFFICIENTS_IN_RING_ELEMENT * U_COMPRESSION_FACTOR) / 8)
            .enumerate()
        {
            u_as_ntt[i]  = deserialize_then_decompress_ring_element_u::<U_COMPRESSION_FACTOR, Vector>(u_bytes);
            ntt_vector_u::<U_COMPRESSION_FACTOR, Vector>(&mut u_as_ntt[i]);
        }
    }
    u_as_ntt
}

/// Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
#[inline(always)]
fn deserialize_secret_key<const K: usize, Vector: Operations>(
    secret_key: &[u8],
) -> [PolynomialRingElement<Vector>; K] {
    let mut secret_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
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
pub(crate) fn decrypt_unpacked<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const VECTOR_U_ENCODED_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    secret_key: &IndCpaPrivateKeyUnpacked<K, Vector>,
    ciphertext: &[u8; CIPHERTEXT_SIZE],
) -> [u8; SHARED_SECRET_SIZE] {
    // u := Decompress_q(Decode_{d_u}(c), d_u)
    let u_as_ntt = deserialize_then_decompress_u::<K, CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR, Vector>(
        ciphertext,
    );

    // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
    let v = deserialize_then_decompress_ring_element_v::<V_COMPRESSION_FACTOR, Vector>(
        &ciphertext[VECTOR_U_ENCODED_SIZE..],
    );

    // m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
    let message = compute_message(&v, &secret_key.secret_as_ntt, &u_as_ntt);
    compress_then_serialize_message(message)
}

#[allow(non_snake_case)]
pub(crate) fn decrypt<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const VECTOR_U_ENCODED_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    secret_key: &[u8],
    ciphertext: &[u8; CIPHERTEXT_SIZE],
) -> [u8; SHARED_SECRET_SIZE] {
    // sˆ := Decode_12(sk)
    let secret_as_ntt = deserialize_secret_key::<K, Vector>(secret_key);
    let secret_key_unpacked = IndCpaPrivateKeyUnpacked { secret_as_ntt };

    decrypt_unpacked::<
        K,
        CIPHERTEXT_SIZE,
        VECTOR_U_ENCODED_SIZE,
        U_COMPRESSION_FACTOR,
        V_COMPRESSION_FACTOR,
        Vector,
    >(&secret_key_unpacked, ciphertext)
}
