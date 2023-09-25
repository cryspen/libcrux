use std::ops::{Index, Range, RangeFrom, RangeTo};

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
        *,
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

pub enum CiphertextCpa {
    Kyber512([u8; CPA_PKE_CIPHERTEXT_SIZE_512]),
    Kyber768([u8; CPA_PKE_CIPHERTEXT_SIZE_768]),
    Kyber1024([u8; CPA_PKE_CIPHERTEXT_SIZE_1024]),
}

impl AsRef<[u8]> for CiphertextCpa {
    fn as_ref(&self) -> &[u8] {
        match self {
            CiphertextCpa::Kyber512(b) => b,
            CiphertextCpa::Kyber768(b) => b,
            CiphertextCpa::Kyber1024(b) => b,
        }
    }
}

impl Index<usize> for CiphertextCpa {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        match self {
            CiphertextCpa::Kyber512(ct) => &ct[index],
            CiphertextCpa::Kyber768(ct) => &ct[index],
            CiphertextCpa::Kyber1024(ct) => &ct[index],
        }
    }
}

impl Index<Range<usize>> for CiphertextCpa {
    type Output = [u8];

    fn index(&self, range: Range<usize>) -> &Self::Output {
        match self {
            CiphertextCpa::Kyber512(ct) => &ct[range],
            CiphertextCpa::Kyber768(ct) => &ct[range],
            CiphertextCpa::Kyber1024(ct) => &ct[range],
        }
    }
}

impl Index<RangeTo<usize>> for CiphertextCpa {
    type Output = [u8];

    fn index(&self, range: RangeTo<usize>) -> &Self::Output {
        match self {
            CiphertextCpa::Kyber512(ct) => &ct[range],
            CiphertextCpa::Kyber768(ct) => &ct[range],
            CiphertextCpa::Kyber1024(ct) => &ct[range],
        }
    }
}

impl Index<RangeFrom<usize>> for CiphertextCpa {
    type Output = [u8];

    fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
        match self {
            CiphertextCpa::Kyber512(ct) => &ct[range],
            CiphertextCpa::Kyber768(ct) => &ct[range],
            CiphertextCpa::Kyber1024(ct) => &ct[range],
        }
    }
}

/// A Kyber key pair
pub struct KeyPair {
    sk: [u8; CPA_PKE_SECRET_KEY_SIZE_768],
    pk: [u8; CPA_PKE_PUBLIC_KEY_SIZE_768],
}

impl KeyPair {
    /// Creates a new [`KeyPair`].
    pub fn new(
        sk: [u8; CPA_PKE_SECRET_KEY_SIZE_768],
        pk: [u8; CPA_PKE_PUBLIC_KEY_SIZE_768],
    ) -> Self {
        Self { sk, pk }
    }

    pub fn serialize_secret_key(
        &self,
        implicit_rejection_value: &[u8],
    ) -> [u8; CPA_SERIALIZED_KEY_LEN_768] {
        UpdatableArray::new([0u8; CPA_SERIALIZED_KEY_LEN_768])
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
fn cbd<const K: usize>(mut prf_input: [u8; 33]) -> ([KyberPolynomialRingElement; K], u8) {
    let mut domain_separator = 0;
    let mut re_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    for i in 0..K {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);

        let r = sample_from_binomial_distribution_2(prf_output);
        re_as_ntt[i] = ntt_representation(r);
    }
    (re_as_ntt, domain_separator)
}

fn encode_12<const K: usize, const OUT_LEN: usize>(
    input: [KyberPolynomialRingElement; K],
) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];

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
    let public_key_serialized = UpdatableArray::new([0u8; CPA_PKE_PUBLIC_KEY_SIZE_768]);
    let public_key_serialized = match K {
        RANK_512 => {
            public_key_serialized.push(&encode_12::<K, RANKED_BYTES_PER_RING_ELEMENT_512>(t_as_ntt))
        }
        RANK_768 => {
            public_key_serialized.push(&encode_12::<K, RANKED_BYTES_PER_RING_ELEMENT_768>(t_as_ntt))
        }
        RANK_1024 => public_key_serialized.push(
            &encode_12::<K, RANKED_BYTES_PER_RING_ELEMENT_1024>(t_as_ntt),
        ),
        _ => return Err(BadRejectionSamplingRandomnessError),
    };
    let public_key_serialized = public_key_serialized.push(seed_for_A).array();

    // sk := Encode_12(sˆ mod^{+}q)
    let secret_key_serialized = encode_12(secret_as_ntt);

    Ok(KeyPair::new(secret_key_serialized, public_key_serialized))
}

fn compress_then_encode_u<const K: usize, const OUT_LEN: usize, const COMPRESSION_FACTOR: usize>(
    input: [KyberPolynomialRingElement; K],
) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    for (i, re) in input.into_iter().enumerate() {
        out[i * (OUT_LEN / K)..(i + 1) * (OUT_LEN / K)].copy_from_slice(
            // FIXME: use 11 for 1024
            &serialize_little_endian_10(compress(re, COMPRESSION_FACTOR)),
        );
    }

    out
}

#[allow(non_snake_case)]
pub(crate) fn encrypt<const K: usize>(
    public_key: &[u8],
    message: [u8; CPA_PKE_MESSAGE_SIZE],
    randomness: &[u8],
) -> Result<CiphertextCpa, BadRejectionSamplingRandomnessError> {
    // tˆ := Decode_12(pk)
    let mut t_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    for (i, t_as_ntt_bytes) in public_key[..T_AS_NTT_ENCODED_SIZE_768]
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
    let seed = &public_key[T_AS_NTT_ENCODED_SIZE_768..];
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
    let mut error_1 = [KyberPolynomialRingElement::ZERO; K];
    for i in 0..K {
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
    for i in 0..K {
        u[i] = invert_ntt_montgomery(u[i]) + error_1[i];
    }

    // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
    let message_as_ring_element = deserialize_little_endian_1(&message);
    let v = invert_ntt_montgomery(multiply_row_by_column_montgomery(&t_as_ntt, &r_as_ntt))
        + error_2
        + decompress(message_as_ring_element, 1);

    let ciphertext = match K {
        RANK_512 => {
            // c_1 := Encode_{du}(Compress_q(u,d_u))
            let c1 = compress_then_encode_u::<
                K,
                VECTOR_U_ENCODED_SIZE_512,
                VECTOR_U_COMPRESSION_FACTOR_512,
            >(u);

            // c_2 := Encode_{dv}(Compress_q(v,d_v))
            let c2 = serialize_little_endian_4(compress(v, VECTOR_V_COMPRESSION_FACTOR_512));

            let mut ciphertext: [u8; CPA_PKE_CIPHERTEXT_SIZE_512] = into_padded_array(&c1);
            ciphertext[VECTOR_U_ENCODED_SIZE_512..].copy_from_slice(c2.as_slice());
            CiphertextCpa::Kyber512(ciphertext)
        }
        RANK_768 => {
            let c1 = compress_then_encode_u::<
                K,
                VECTOR_U_ENCODED_SIZE_768,
                VECTOR_U_COMPRESSION_FACTOR_768,
            >(u);

            // c_2 := Encode_{dv}(Compress_q(v,d_v))
            let c2 = serialize_little_endian_4(compress(v, VECTOR_V_COMPRESSION_FACTOR_768));

            let mut ciphertext: [u8; CPA_PKE_CIPHERTEXT_SIZE_768] = into_padded_array(&c1);
            ciphertext[VECTOR_U_ENCODED_SIZE_768..].copy_from_slice(c2.as_slice());
            CiphertextCpa::Kyber768(ciphertext)
        }
        RANK_1024 => {
            let c1 = compress_then_encode_u::<
                K,
                VECTOR_U_ENCODED_SIZE_1024,
                VECTOR_U_COMPRESSION_FACTOR_1024,
            >(u);

            // c_2 := Encode_{dv}(Compress_q(v,d_v))
            let c2 = serialize_little_endian_4(compress(v, VECTOR_V_COMPRESSION_FACTOR_1024));

            let mut ciphertext: [u8; CPA_PKE_CIPHERTEXT_SIZE_1024] = into_padded_array(&c1);
            ciphertext[VECTOR_U_ENCODED_SIZE_1024..].copy_from_slice(c2.as_slice());
            CiphertextCpa::Kyber1024(ciphertext)
        }
        _ => return Err(BadRejectionSamplingRandomnessError),
    };

    Ok(ciphertext)
}

#[allow(non_snake_case)]
pub(crate) fn decrypt<const K: usize>(
    secret_key: &[u8],
    ciphertext: &CiphertextCpa,
) -> [u8; CPA_PKE_MESSAGE_SIZE] {
    let mut u_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; K];

    let (vec_u_encoded_size, u_compression_factor, v_compression_factor) = match ciphertext {
        CiphertextCpa::Kyber512(_) => (
            VECTOR_U_ENCODED_SIZE_512,
            VECTOR_U_COMPRESSION_FACTOR_512,
            VECTOR_V_COMPRESSION_FACTOR_512,
        ),
        CiphertextCpa::Kyber768(_) => (
            VECTOR_U_ENCODED_SIZE_768,
            VECTOR_U_COMPRESSION_FACTOR_768,
            VECTOR_V_COMPRESSION_FACTOR_768,
        ),
        CiphertextCpa::Kyber1024(_) => (
            VECTOR_U_ENCODED_SIZE_1024,
            VECTOR_U_COMPRESSION_FACTOR_1024,
            VECTOR_V_COMPRESSION_FACTOR_1024,
        ),
    };

    // u := Decompress_q(Decode_{d_u}(c), d_u)
    for (i, u_bytes) in ciphertext[..vec_u_encoded_size]
        .chunks_exact((COEFFICIENTS_IN_RING_ELEMENT * u_compression_factor) / 8)
        .enumerate()
    {
        let u = deserialize_little_endian_10(u_bytes);
        u_as_ntt[i] = ntt_representation(decompress(u, 10));
    }

    // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
    let v = decompress(
        deserialize_little_endian_4(&ciphertext[vec_u_encoded_size..]),
        v_compression_factor,
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
