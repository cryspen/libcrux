use crate::kem::kyber768::conversions::{UpdatableArray, UpdatingArray};

use crate::kem::kyber768::{
    arithmetic::KyberPolynomialRingElement,
    compress::{compress, decompress},
    ntt::{
        kyber_polynomial_ring_element_mod::{invert_ntt_montgomery, ntt_representation},
        *,
    },
    parameters::{
        hash_functions::{G, H, PRF, XOF},
        BYTES_PER_ENCODED_ELEMENT_OF_U, BYTES_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT,
        CPA_PKE_CIPHERTEXT_SIZE, CPA_PKE_MESSAGE_SIZE, CPA_PKE_PUBLIC_KEY_SIZE,
        CPA_PKE_SECRET_KEY_SIZE, CPA_SERIALIZED_KEY_LEN, RANK, REJECTION_SAMPLING_SEED_SIZE,
        T_AS_NTT_ENCODED_SIZE, VECTOR_U_COMPRESSION_FACTOR, VECTOR_U_ENCODED_SIZE,
        VECTOR_V_COMPRESSION_FACTOR,
    },
    sampling::{sample_from_binomial_distribution_2, sample_from_uniform_distribution},
    serialize::{
        deserialize_little_endian_1, deserialize_little_endian_10, deserialize_little_endian_12,
        deserialize_little_endian_4, serialize_little_endian_1, serialize_little_endian_10,
        serialize_little_endian_12, serialize_little_endian_4,
    },
    BadRejectionSamplingRandomnessError,
};

use super::conversions::into_padded_array;

pub type CiphertextCpa = [u8; CPA_PKE_CIPHERTEXT_SIZE];

/// A Kyber key pair
pub struct KeyPair {
    sk: [u8; CPA_PKE_SECRET_KEY_SIZE],
    pk: [u8; CPA_PKE_PUBLIC_KEY_SIZE],
}

impl KeyPair {
    /// Creates a new [`KeyPair`].
    pub fn new(sk: [u8; CPA_PKE_SECRET_KEY_SIZE], pk: [u8; CPA_PKE_PUBLIC_KEY_SIZE]) -> Self {
        Self { sk, pk }
    }

    pub fn serialize_secret_key(
        &self,
        implicit_rejection_value: &[u8],
    ) -> [u8; CPA_SERIALIZED_KEY_LEN] {
        UpdatableArray::new([0u8; CPA_SERIALIZED_KEY_LEN])
            .push(&self.sk)
            .push(&self.pk)
            .push(&H(&self.pk))
            .push(implicit_rejection_value)
            .array()
    }

    pub fn pk(&self) -> [u8; 1184] {
        self.pk
    }
}

#[inline(always)]
fn parse_a<const K: usize>(
    mut seed: [u8; 34],
    transpose: bool,
) -> Result<[[KyberPolynomialRingElement; K]; K], BadRejectionSamplingRandomnessError> {
    let mut a_transpose = [[KyberPolynomialRingElement::ZERO; K]; K];

    for i in 0..K {
        for j in 0..K {
            seed[32] = i as u8;
            seed[33] = j as u8;

            let xof_bytes: [u8; REJECTION_SAMPLING_SEED_SIZE] = XOF(&seed);

            // A[i][j] = A_transpose[j][i]
            if transpose {
                a_transpose[j][i] = sample_from_uniform_distribution(xof_bytes)?;
            } else {
                a_transpose[i][j] = sample_from_uniform_distribution(xof_bytes)?;
            }
        }
    }
    Ok(a_transpose)
}

#[inline(always)]
fn cbd(mut prf_input: [u8; 33]) -> ([KyberPolynomialRingElement; RANK], u8) {
    let mut domain_separator = 0;
    let mut re_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];
    for i in 0..RANK {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);

        let r = sample_from_binomial_distribution_2(prf_output);
        re_as_ntt[i] = ntt_representation(r);
    }
    (re_as_ntt, domain_separator)
}

fn encode_12<const K: usize>(
    input: [KyberPolynomialRingElement; K],
) -> [u8; K * BYTES_PER_RING_ELEMENT] {
    let mut out = [0u8; K * BYTES_PER_RING_ELEMENT];

    for (i, re) in input.into_iter().enumerate() {
        out[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT]
            .copy_from_slice(&serialize_little_endian_12(re));
    }

    out
}

#[allow(non_snake_case)]
pub(crate) fn generate_keypair<const K: usize>(
    key_generation_seed: &[u8],
) -> Result<KeyPair, BadRejectionSamplingRandomnessError> {
    let mut prf_input: [u8; 33] = [0; 33];

    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    let mut error_as_ntt = [KyberPolynomialRingElement::ZERO; K];

    // N := 0
    let mut domain_separator: u8 = 0;

    // (ρ,σ) := G(d)
    let hashed = G(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    let A_transpose = parse_a(into_padded_array(seed_for_A), true)?;

    // for i from 0 to k−1 do
    //     s[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // sˆ := NTT(s)
    prf_input[0..seed_for_secret_and_error.len()].copy_from_slice(seed_for_secret_and_error);

    for i in 0..K {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);

        let secret = sample_from_binomial_distribution_2(prf_output);
        secret_as_ntt[i] = ntt_representation(secret);
    }

    // for i from 0 to k−1 do
    //     e[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // eˆ := NTT(e)
    for i in 0..K {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);

        let error = sample_from_binomial_distribution_2(prf_output);
        error_as_ntt[i] = ntt_representation(error);
    }

    // tˆ := Aˆ ◦ sˆ + eˆ
    let mut t_as_ntt = multiply_matrix_by_column(&A_transpose, &secret_as_ntt);
    for i in 0..K {
        t_as_ntt[i] = t_as_ntt[i] + error_as_ntt[i];
    }

    // pk := (Encode_12(tˆ mod^{+}q) || ρ)
    let public_key_serialized = UpdatableArray::new([0u8; CPA_PKE_PUBLIC_KEY_SIZE])
        .push(&encode_12(t_as_ntt))
        .push(seed_for_A)
        .array();

    // sk := Encode_12(sˆ mod^{+}q)
    let secret_key_serialized = encode_12(secret_as_ntt);

    Ok(KeyPair::new(secret_key_serialized, public_key_serialized))
}

fn compress_then_encode_u<const K: usize, const DU: usize>(
    input: [KyberPolynomialRingElement; K],
) -> [u8; ((COEFFICIENTS_IN_RING_ELEMENT * DU) / 8) * K] {
    let mut out = [0u8; ((COEFFICIENTS_IN_RING_ELEMENT * DU) / 8) * K];
    for (i, re) in input.into_iter().enumerate() {
        out[i * ((COEFFICIENTS_IN_RING_ELEMENT * DU) / 8)
            ..(i + 1) * ((COEFFICIENTS_IN_RING_ELEMENT * DU) / 8)]
            .copy_from_slice(&serialize_little_endian_10(compress(re, DU)));
    }

    out
}

#[allow(non_snake_case)]
pub(crate) fn encrypt(
    public_key: &[u8],
    message: [u8; CPA_PKE_MESSAGE_SIZE],
    randomness: &[u8],
) -> Result<CiphertextCpa, BadRejectionSamplingRandomnessError> {
    // tˆ := Decode_12(pk)
    let mut t_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];
    for (i, t_as_ntt_bytes) in public_key[..T_AS_NTT_ENCODED_SIZE]
        .chunks_exact(BYTES_PER_RING_ELEMENT)
        .enumerate()
    {
        t_as_ntt[i] = deserialize_little_endian_12(t_as_ntt_bytes);
    }

    // ρ := pk + 12·k·n / 8
    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         AˆT[i][j] := Parse(XOF(ρ, i, j))
    //     end for
    // end for
    let seed = &public_key[T_AS_NTT_ENCODED_SIZE..];
    let A_transpose = parse_a(into_padded_array(seed), false)?;

    // for i from 0 to k−1 do
    //     r[i] := CBD{η1}(PRF(r, N))
    //     N := N + 1
    // end for
    // rˆ := NTT(r)
    let mut prf_input: [u8; 33] = into_padded_array(randomness);
    let (r_as_ntt, mut domain_separator) = cbd(prf_input);

    // for i from 0 to k−1 do
    //     e1[i] := CBD_{η2}(PRF(r,N))
    //     N := N + 1
    // end for
    let mut error_1 = [KyberPolynomialRingElement::ZERO; RANK];
    for i in 0..RANK {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);
        error_1[i] = sample_from_binomial_distribution_2(prf_output);
    }

    // e_2 := CBD{η2}(PRF(r, N))
    prf_input[32] = domain_separator;
    // 2 sampling coins * 64
    let prf_output: [u8; 128] = PRF(&prf_input);
    let error_2 = sample_from_binomial_distribution_2(prf_output);

    // u := NTT^{-1}(AˆT ◦ rˆ) + e_1
    let mut u = multiply_matrix_by_column_montgomery(&A_transpose, &r_as_ntt);
    for i in 0..RANK {
        u[i] = invert_ntt_montgomery(u[i]) + error_1[i];
    }

    // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
    let message_as_ring_element = deserialize_little_endian_1(&message);
    let v = invert_ntt_montgomery(multiply_row_by_column_montgomery(&t_as_ntt, &r_as_ntt))
        + error_2
        + decompress(message_as_ring_element, 1);

    // c_1 := Encode_{du}(Compress_q(u,d_u))
    let c1 = compress_then_encode_u(u);

    // c_2 := Encode_{dv}(Compress_q(v,d_v))
    let c2 = serialize_little_endian_4(compress(v, VECTOR_V_COMPRESSION_FACTOR));

    let mut ciphertext: CiphertextCpa = into_padded_array(&c1);
    ciphertext[VECTOR_U_ENCODED_SIZE..].copy_from_slice(c2.as_slice());

    Ok(ciphertext)
}

#[allow(non_snake_case)]
pub(crate) fn decrypt(
    secret_key: &[u8],
    ciphertext: &[u8; CPA_PKE_CIPHERTEXT_SIZE],
) -> [u8; CPA_PKE_MESSAGE_SIZE] {
    let mut u_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];
    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];

    // u := Decompress_q(Decode_{d_u}(c), d_u)
    for (i, u_bytes) in ciphertext[..VECTOR_U_ENCODED_SIZE]
        .chunks_exact((COEFFICIENTS_IN_RING_ELEMENT * 10) / 8)
        .enumerate()
    {
        let u = deserialize_little_endian_10(u_bytes);
        u_as_ntt[i] = ntt_representation(decompress(u, 10));
    }

    // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
    let v = decompress(
        deserialize_little_endian_4(&ciphertext[VECTOR_U_ENCODED_SIZE..]),
        VECTOR_V_COMPRESSION_FACTOR,
    );

    // sˆ := Decode_12(sk)
    for (i, secret_bytes) in secret_key.chunks_exact(BYTES_PER_RING_ELEMENT).enumerate() {
        secret_as_ntt[i] = deserialize_little_endian_12(secret_bytes);
    }

    // m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
    let message =
        v - invert_ntt_montgomery(multiply_row_by_column_montgomery(&secret_as_ntt, &u_as_ntt));

    serialize_little_endian_1(compress(message, 1))
}
