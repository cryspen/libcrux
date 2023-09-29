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

impl_generic_struct!(PublicKey);
impl_generic_struct!(PrivateKey);

/// A Kyber CPA key pair
pub struct KeyPair<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize> {
    pub(super) sk: PrivateKey<PRIVATE_KEY_SIZE>,
    pub(super) pk: PublicKey<PUBLIC_KEY_SIZE>,
}

impl<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize>
    KeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>
{
    /// Creates a new [`KeyPair`].
    pub fn new(sk: [u8; PRIVATE_KEY_SIZE], pk: [u8; PUBLIC_KEY_SIZE]) -> Self {
        Self {
            sk: sk.into(),
            pk: pk.into(),
        }
    }

    pub fn pk(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        self.pk.as_slice()
    }

    pub fn into_pk(self) -> PublicKey<PUBLIC_KEY_SIZE> {
        self.pk
    }

    pub fn into_raw_pk(self) -> [u8; PUBLIC_KEY_SIZE] {
        self.pk.value
    }

    pub fn sk(&self) -> &[u8; PRIVATE_KEY_SIZE] {
        self.sk.as_slice()
    }
}

#[inline(always)]
#[allow(non_snake_case)]
fn sample_matrix_A<const K: usize>(
    mut seed: [u8; 34],
    transpose: bool,
) -> (
    [[KyberPolynomialRingElement; K]; K],
    Option<BadRejectionSamplingRandomnessError>,
) {
    let mut A_transpose = [[KyberPolynomialRingElement::ZERO; K]; K];
    let mut sampling_A_error = None;

    for i in 0..K {
        for j in 0..K {
            seed[32] = i as u8;
            seed[33] = j as u8;

            let xof_bytes: [u8; REJECTION_SAMPLING_SEED_SIZE] = XOF(&seed);

            let (sampled, error) = sample_from_uniform_distribution(xof_bytes);
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
pub(crate) fn generate_keypair<
    const K: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
>(
    key_generation_seed: &[u8],
) -> (
    (PrivateKey<PRIVATE_KEY_SIZE>, PublicKey<PUBLIC_KEY_SIZE>),
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
    // sk := Encode_12(sˆ mod^{+}q)
    let public_key_serialized = UpdatableArray::new([0u8; PUBLIC_KEY_SIZE]);
    let public_key_serialized =
        public_key_serialized.push(&encode_12::<K, BYTES_PER_RING_ELEMENT>(t_as_ntt));
    let public_key_serialized = public_key_serialized.push(seed_for_A).array();
    let secret_key_serialized = encode_12(secret_as_ntt);
    (
        (secret_key_serialized.into(), public_key_serialized.into()),
        sampling_A_error,
    )
}

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

macro_rules! impl_encrypt {
    ($k:expr, $ctext_len:expr) => {};
}
impl_encrypt!(RANK_512, CIPHERTEXT_SIZE);

#[allow(non_snake_case)]
pub(crate) fn encrypt<const K: usize, const CIPHERTEXT_SIZE: usize>(
    public_key: &[u8],
    message: [u8; CPA_PKE_MESSAGE_SIZE],
    randomness: &[u8],
) -> (
    super::KyberCiphertext<CIPHERTEXT_SIZE>,
    Option<BadRejectionSamplingRandomnessError>,
) {
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
    let (A_transpose, sampling_A_error) = sample_matrix_A(into_padded_array(seed), false);

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

    match K {
        RANK_512 => {
            // c_1 := Encode_{du}(Compress_q(u,d_u))
            let c1 = compress_then_encode_u::<
                K,
                VECTOR_U_ENCODED_SIZE_512,
                VECTOR_U_COMPRESSION_FACTOR_512,
            >(u);

            // c_2 := Encode_{dv}(Compress_q(v,d_v))
            let c2 = serialize_little_endian_4(compress(v, VECTOR_V_COMPRESSION_FACTOR_512));

            let mut ciphertext: [u8; CIPHERTEXT_SIZE] = into_padded_array(&c1);
            ciphertext[VECTOR_U_ENCODED_SIZE_512..].copy_from_slice(c2.as_slice());
            (ciphertext.into(), sampling_A_error)
        }
        RANK_768 => {
            let c1 = compress_then_encode_u::<
                K,
                VECTOR_U_ENCODED_SIZE_768,
                VECTOR_U_COMPRESSION_FACTOR_768,
            >(u);

            // c_2 := Encode_{dv}(Compress_q(v,d_v))
            let c2 = serialize_little_endian_4(compress(v, VECTOR_V_COMPRESSION_FACTOR_768));

            let mut ciphertext: [u8; CIPHERTEXT_SIZE] = into_padded_array(&c1);
            ciphertext[VECTOR_U_ENCODED_SIZE_768..].copy_from_slice(c2.as_slice());
            (ciphertext.into(), sampling_A_error)
        }
        RANK_1024 => {
            let c1 = compress_then_encode_u::<
                K,
                VECTOR_U_ENCODED_SIZE_1024,
                VECTOR_U_COMPRESSION_FACTOR_1024,
            >(u);

            // c_2 := Encode_{dv}(Compress_q(v,d_v))
            let c2 = serialize_little_endian_4(compress(v, VECTOR_V_COMPRESSION_FACTOR_1024));

            let mut ciphertext: [u8; CIPHERTEXT_SIZE] = into_padded_array(&c1);
            ciphertext[VECTOR_U_ENCODED_SIZE_1024..].copy_from_slice(c2.as_slice());
            (ciphertext.into(), sampling_A_error)
        }
        _ => (
            [0u8; CIPHERTEXT_SIZE].into(),
            Some(BadRejectionSamplingRandomnessError),
        ),
    }
}

#[allow(non_snake_case)]
pub(crate) fn decrypt<const K: usize, const CIPHERTEXT_SIZE: usize>(
    secret_key: &[u8],
    ciphertext: &super::KyberCiphertext<CIPHERTEXT_SIZE>,
) -> [u8; CPA_PKE_MESSAGE_SIZE] {
    let mut u_as_ntt = [KyberPolynomialRingElement::ZERO; K];
    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; K];

    let (vec_u_encoded_size, u_compression_factor, v_compression_factor) = match K {
        RANK_512 => (
            VECTOR_U_ENCODED_SIZE_512,
            VECTOR_U_COMPRESSION_FACTOR_512,
            VECTOR_V_COMPRESSION_FACTOR_512,
        ),
        RANK_768 => (
            VECTOR_U_ENCODED_SIZE_768,
            VECTOR_U_COMPRESSION_FACTOR_768,
            VECTOR_V_COMPRESSION_FACTOR_768,
        ),
        RANK_1024 => (
            VECTOR_U_ENCODED_SIZE_1024,
            VECTOR_U_COMPRESSION_FACTOR_1024,
            VECTOR_V_COMPRESSION_FACTOR_1024,
        ),
        _ => unreachable!(),
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
