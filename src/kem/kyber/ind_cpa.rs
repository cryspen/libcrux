use super::{
    arithmetic::KyberPolynomialRingElement,
    compress::{compress, decompress},
    constants::{
        BYTES_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT, REJECTION_SAMPLING_SEED_SIZE,
        SHARED_SECRET_SIZE,
    },
    conversions::into_padded_array,
    conversions::{UpdatableArray, UpdatingArray},
    hash_functions::{XOFx4, G, H, PRF},
    ntt::*,
    sampling::{sample_from_binomial_distribution, sample_from_uniform_distribution},
    serialize::{
        compress_then_serialize_message, deserialize_little_endian,
        deserialize_then_decompress_message, deserialize_to_uncompressed_ring_element,
        serialize_little_endian, serialize_uncompressed_ring_element,
    },
    BadRejectionSamplingRandomnessError, KyberPublicKey,
};

// The PKE Private Key
impl_generic_struct!(PrivateKey);
pub fn serialize_secret_key<const SERIALIZED_KEY_LEN: usize>(
    private_key: &[u8],
    public_key: &[u8],
    implicit_rejection_value: &[u8],
) -> [u8; SERIALIZED_KEY_LEN] {
    UpdatableArray::new([0u8; SERIALIZED_KEY_LEN])
        .push(private_key)
        .push(public_key)
        .push(&H(public_key))
        .push(implicit_rejection_value)
        .array()
}

#[inline(always)]
#[allow(non_snake_case)]
fn sample_matrix_A<const K: usize>(
    seed: [u8; 34],
    transpose: bool,
) -> (
    [[KyberPolynomialRingElement; K]; K],
    Option<BadRejectionSamplingRandomnessError>,
) {
    let mut A_transpose = [[KyberPolynomialRingElement::ZERO; K]; K];
    let mut sampling_A_error = None;

    for i in 0..K {
        let mut seeds = [seed; K];
        for j in 0..K {
            seeds[j][32] = i as u8;
            seeds[j][33] = j as u8;
        }
        let xof_bytes = XOFx4::<REJECTION_SAMPLING_SEED_SIZE, K>(seeds);

        for j in 0..K {
            let (sampled, error) = sample_from_uniform_distribution(xof_bytes[j]);
            if error.is_some() {
                sampling_A_error = error;
            }

            // A[i][j] = A_transpose[j][i]
            if transpose {
                A_transpose[j][i] = sampled;
            } else {
                A_transpose[i][j] = sampled;
            }
        }
    }

    (A_transpose, sampling_A_error)
}

#[inline(always)]
fn cbd<const K: usize, const ETA: usize, const ETA_RANDOMNESS_SIZE: usize>(
    mut prf_input: [u8; 33],
) -> ([KyberPolynomialRingElement; K], u8) {
    let mut domain_separator = 0;
    let mut re_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    for i in 0..K {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output: [u8; ETA_RANDOMNESS_SIZE] = PRF(&prf_input);

        let r = sample_from_binomial_distribution::<ETA>(&prf_output);
        re_as_ntt[i] = ntt_with_debug_asserts(r, ETA);
    }
    (re_as_ntt, domain_separator)
}

fn serialize_key<const K: usize, const OUT_LEN: usize>(
    key: [KyberPolynomialRingElement; K],
) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];

    for (i, re) in key.into_iter().enumerate() {
        out[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT]
            .copy_from_slice(&serialize_uncompressed_ring_element(re));
    }

    out
}

#[allow(non_snake_case)]
pub(crate) fn generate_keypair<
    const K: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    key_generation_seed: &[u8],
) -> (
    (
        PrivateKey<PRIVATE_KEY_SIZE>,
        KyberPublicKey<PUBLIC_KEY_SIZE>,
    ),
    Option<BadRejectionSamplingRandomnessError>,
) {
    let mut prf_input: [u8; 33] = [0; 33];

    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    let mut error_as_ntt = [KyberPolynomialRingElement::ZERO; K];

    // N := 0
    let mut domain_separator: u8 = 0;

    // (ρ,σ) := G(d)
    let hashed = G(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    let (A_transpose, sampling_A_error) = sample_matrix_A(into_padded_array(seed_for_A), true);

    // for i from 0 to k−1 do
    //     s[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // sˆ := NTT(s)
    prf_input[0..seed_for_secret_and_error.len()].copy_from_slice(seed_for_secret_and_error);

    for i in 0..K {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output: [u8; ETA1_RANDOMNESS_SIZE] = PRF(&prf_input);

        let secret = sample_from_binomial_distribution::<ETA1>(&prf_output);

        secret_as_ntt[i] = ntt_with_debug_asserts(secret, ETA1);
    }

    // for i from 0 to k−1 do
    //     e[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // eˆ := NTT(e)
    for i in 0..K {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output: [u8; ETA1_RANDOMNESS_SIZE] = PRF(&prf_input);

        let error = sample_from_binomial_distribution::<ETA1>(&prf_output);
        error_as_ntt[i] = ntt_with_debug_asserts(error, ETA1);
    }

    // tˆ := Aˆ ◦ sˆ + eˆ
    let t_as_ntt = compute_As_plus_e(&A_transpose, &secret_as_ntt, &error_as_ntt);

    // pk := (Encode_12(tˆ mod^{+}q) || ρ)
    let public_key_serialized = UpdatableArray::new([0u8; PUBLIC_KEY_SIZE]);
    let public_key_serialized =
        public_key_serialized.push(&serialize_key::<K, RANKED_BYTES_PER_RING_ELEMENT>(t_as_ntt));
    let public_key_serialized = public_key_serialized.push(seed_for_A).array();

    // sk := Encode_12(sˆ mod^{+}q)
    let secret_key_serialized = serialize_key(secret_as_ntt);

    (
        (secret_key_serialized.into(), public_key_serialized.into()),
        sampling_A_error,
    )
}

fn compress_then_encode_u<
    const K: usize,
    const OUT_LEN: usize,
    const COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
>(
    input: [KyberPolynomialRingElement; K],
) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    for (i, re) in input.into_iter().enumerate() {
        out[i * (OUT_LEN / K)..(i + 1) * (OUT_LEN / K)].copy_from_slice(
            &serialize_little_endian::<COMPRESSION_FACTOR, BLOCK_LEN>(
                compress::<COMPRESSION_FACTOR>(re),
            ),
        );
    }

    out
}

#[allow(non_snake_case)]
pub(crate) fn encrypt<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_LEN: usize,
    const C2_LEN: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
>(
    public_key: &[u8],
    message: [u8; SHARED_SECRET_SIZE],
    randomness: &[u8],
) -> (
    super::KyberCiphertext<CIPHERTEXT_SIZE>,
    Option<BadRejectionSamplingRandomnessError>,
) {
    // tˆ := Decode_12(pk)
    let mut t_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    for (i, t_as_ntt_bytes) in public_key[..T_AS_NTT_ENCODED_SIZE]
        .chunks_exact(BYTES_PER_RING_ELEMENT)
        .enumerate()
    {
        t_as_ntt[i] = deserialize_to_uncompressed_ring_element(t_as_ntt_bytes);
    }

    // ρ := pk + 12·k·n / 8
    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         AˆT[i][j] := Parse(XOF(ρ, i, j))
    //     end for
    // end for
    let seed = &public_key[T_AS_NTT_ENCODED_SIZE..];
    let (A_transpose, sampling_A_error) = sample_matrix_A(into_padded_array(seed), false);

    // for i from 0 to k−1 do
    //     r[i] := CBD{η1}(PRF(r, N))
    //     N := N + 1
    // end for
    // rˆ := NTT(r)
    let mut prf_input: [u8; 33] = into_padded_array(randomness);
    let (r_as_ntt, mut domain_separator) = cbd::<K, ETA1, ETA1_RANDOMNESS_SIZE>(prf_input);

    // for i from 0 to k−1 do
    //     e1[i] := CBD_{η2}(PRF(r,N))
    //     N := N + 1
    // end for
    let mut error_1 = [KyberPolynomialRingElement::ZERO; K];
    for i in 0..K {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output: [u8; ETA2_RANDOMNESS_SIZE] = PRF(&prf_input);
        error_1[i] = sample_from_binomial_distribution::<ETA2>(&prf_output);
    }

    // e_2 := CBD{η2}(PRF(r, N))
    prf_input[32] = domain_separator;
    let prf_output: [u8; ETA2_RANDOMNESS_SIZE] = PRF(&prf_input);
    let error_2 = sample_from_binomial_distribution::<ETA2>(&prf_output);

    // u := NTT^{-1}(AˆT ◦ rˆ) + e_1
    let mut u = multiply_matrix_by_column_montgomery(&A_transpose, &r_as_ntt);
    for i in 0..K {
        u[i] = invert_ntt_montgomery(u[i]) + error_1[i];
    }

    // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
    let message_as_ring_element = deserialize_then_decompress_message(message);
    let v = invert_ntt_montgomery(multiply_row_by_column_montgomery(&t_as_ntt, &r_as_ntt))
        + error_2
        + message_as_ring_element;

    // c_1 := Encode_{du}(Compress_q(u,d_u))
    let c1 = compress_then_encode_u::<K, C1_LEN, VECTOR_U_COMPRESSION_FACTOR, BLOCK_LEN>(u);

    // c_2 := Encode_{dv}(Compress_q(v,d_v))
    let c2 = serialize_little_endian::<VECTOR_V_COMPRESSION_FACTOR, C2_LEN>(compress::<
        VECTOR_V_COMPRESSION_FACTOR,
    >(v));

    let mut ciphertext: [u8; CIPHERTEXT_SIZE] = into_padded_array(&c1);
    ciphertext[C1_LEN..].copy_from_slice(c2.as_slice());
    (ciphertext.into(), sampling_A_error)
}

#[allow(non_snake_case)]
pub(crate) fn decrypt<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const VECTOR_U_ENCODED_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
>(
    secret_key: &[u8],
    ciphertext: &super::KyberCiphertext<CIPHERTEXT_SIZE>,
) -> [u8; SHARED_SECRET_SIZE] {
    let mut u_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; K];

    // u := Decompress_q(Decode_{d_u}(c), d_u)
    for (i, u_bytes) in ciphertext[..VECTOR_U_ENCODED_SIZE]
        .chunks_exact((COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8)
        .enumerate()
    {
        let u = decompress::<VECTOR_U_COMPRESSION_FACTOR>(deserialize_little_endian::<
            VECTOR_U_COMPRESSION_FACTOR,
        >(u_bytes));
        u_as_ntt[i] = ntt_representation(u);
    }

    // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
    let v = decompress::<VECTOR_V_COMPRESSION_FACTOR>(deserialize_little_endian::<
        VECTOR_V_COMPRESSION_FACTOR,
    >(&ciphertext[VECTOR_U_ENCODED_SIZE..]));

    // sˆ := Decode_12(sk)
    for (i, secret_bytes) in secret_key.chunks_exact(BYTES_PER_RING_ELEMENT).enumerate() {
        secret_as_ntt[i] = deserialize_to_uncompressed_ring_element(secret_bytes);
    }

    // m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
    let message =
        v - invert_ntt_montgomery(multiply_row_by_column_montgomery(&secret_as_ntt, &u_as_ntt));

    compress_then_serialize_message(message)
}
