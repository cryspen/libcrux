use hacspec_lib::{
    ArrayConversion, ArrayPadding, PanickingIntegerCasts, UpdatableArray, UpdatingArray, VecUpdate,
};

use crate::{
    compress::{compress, decompress},
    ntt::{
        kyber_polynomial_ring_element_mod::{invert_ntt, ntt_representation},
        *,
    },
    parameters::{
        hash_functions::{G, H, PRF, XOF},
        KyberPolynomialRingElement, BITS_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT,
        CPA_PKE_CIPHERTEXT_SIZE, CPA_PKE_KEY_GENERATION_SEED_SIZE, CPA_PKE_MESSAGE_SIZE,
        CPA_PKE_PUBLIC_KEY_SIZE, CPA_PKE_SECRET_KEY_SIZE, CPA_SERIALIZED_KEY_LEN, RANK,
        REJECTION_SAMPLING_SEED_SIZE, T_AS_NTT_ENCODED_SIZE, VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_U_SIZE, VECTOR_V_COMPRESSION_FACTOR,
    },
    sampling::{sample_from_binomial_distribution, sample_from_uniform_distribution},
    serialize::{deserialize_little_endian, serialize_little_endian},
    BadRejectionSamplingRandomnessError,
};

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
        implicit_rejection_value: &[u8; CPA_PKE_MESSAGE_SIZE],
    ) -> [u8; CPA_SERIALIZED_KEY_LEN] {
        UpdatableArray::new([0u8; CPA_SERIALIZED_KEY_LEN])
            .push(&self.sk)
            .push(&self.pk)
            .push(&H(&self.pk))
            .push(implicit_rejection_value)
            .into()
    }

    pub fn pk(&self) -> [u8; 1184] {
        self.pk
    }
}

fn encode_12(input: [KyberPolynomialRingElement; RANK]) -> Vec<u8> {
    let mut out = Vec::new();
    for re in input.into_iter() {
        out.extend_from_slice(&serialize_little_endian(re, 12));
    }

    out
}

/// This function implements Algorithm 4 of the Kyber Round 3 specification;
/// This is the Kyber Round 3 CPA-PKE key generation algorithm, and is
/// reproduced below:
///
/// ```plaintext
/// Output: Secret key sk ∈ B^{12·k·n/8}
/// Output: Public key pk ∈ B^{12·k·n/8+32}
/// d←B^{32}
/// (ρ,σ) := G(d)
/// N := 0
/// for i from 0 to k−1 do
///     for j from 0 to k − 1 do
///         Aˆ [i][j] := Parse(XOF(ρ, j, i))
///     end for
/// end for
/// for i from 0 to k−1 do
///     s[i] := CBD_{η1}(PRF(σ, N))
///     N := N + 1
/// end for
/// for i from 0 to k−1 do
///     e[i] := CBD_{η1}(PRF(σ, N))
///     N := N + 1
/// end for
/// sˆ := NTT(s)
/// eˆ := NTT(e)
/// tˆ := Aˆ ◦ sˆ + eˆ
/// pk := Encode_12(tˆ mod^{+}q) || ρ
/// sk := Encode_12(sˆ mod^{+}q)
/// return (pk,sk)
/// ```
///
/// The Kyber Round 3 specification can be found at:
/// <https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf>
#[allow(non_snake_case)]
pub(crate) fn generate_keypair(
    key_generation_seed: &[u8; CPA_PKE_KEY_GENERATION_SEED_SIZE],
) -> Result<KeyPair, BadRejectionSamplingRandomnessError> {
    let mut prf_input: [u8; 33] = [0; 33];

    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];
    let mut error_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];

    // N := 0
    let mut domain_separator: u8 = 0;

    // (ρ,σ) := G(d)
    let hashed = G(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    let A_transpose = parse_a(seed_for_A.into_padded_array(), true)?;

    // for i from 0 to k−1 do
    //     s[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // sˆ := NTT(s)
    prf_input[0..seed_for_secret_and_error.len()].copy_from_slice(seed_for_secret_and_error);

    for i in 0..secret_as_ntt.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);

        let secret = sample_from_binomial_distribution(2, &prf_output[..]);
        secret_as_ntt[i] = ntt_representation(secret);
    }

    // for i from 0 to k−1 do
    //     e[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // eˆ := NTT(e)
    for i in 0..error_as_ntt.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);

        let error = sample_from_binomial_distribution(2, &prf_output[..]);
        error_as_ntt[i] = ntt_representation(error);
    }

    // tˆ := Aˆ ◦ sˆ + eˆ
    let mut t_as_ntt = multiply_matrix_by_column(&A_transpose, &secret_as_ntt);
    for i in 0..t_as_ntt.len() {
        t_as_ntt[i] = t_as_ntt[i] + error_as_ntt[i];
    }

    // pk := (Encode_12(tˆ mod^{+}q) || ρ)
    let public_key_serialized = encode_12(t_as_ntt).concat(seed_for_A);

    // sk := Encode_12(sˆ mod^{+}q)
    let secret_key_serialized = encode_12(secret_as_ntt);

    Ok(KeyPair::new(
        secret_key_serialized.into_array(),
        public_key_serialized.into_array(),
    ))
}

/// ```text
/// for i from 0 to k−1 do
///     for j from 0 to k − 1 do
///         Aˆ [i][j] := Parse(XOF(ρ, j, i))
///     end for
/// end for
/// ```
#[inline(always)]
fn parse_a(
    mut seed: [u8; 34],
    transpose: bool,
) -> Result<[[KyberPolynomialRingElement; RANK]; RANK], BadRejectionSamplingRandomnessError> {
    let mut a_transpose = [[KyberPolynomialRingElement::ZERO; RANK]; RANK];

    for i in 0..RANK {
        for j in 0..RANK {
            seed[32] = i.as_u8();
            seed[33] = j.as_u8();

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
    let mut r_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];
    for i in 0..r_as_ntt.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);

        let r = sample_from_binomial_distribution(2, &prf_output);
        r_as_ntt[i] = ntt_representation(r);
    }
    (r_as_ntt, domain_separator)
}

fn encode_and_compress_u(input: [KyberPolynomialRingElement; RANK]) -> Vec<u8> {
    let mut out = Vec::new();
    for re in input.into_iter() {
        out.extend_from_slice(&serialize_little_endian(
            compress(re, VECTOR_U_COMPRESSION_FACTOR),
            VECTOR_U_COMPRESSION_FACTOR,
        ));
    }

    out
}

/// This function implements Algorithm 5 of the Kyber Round 3 specification;
/// This is the Kyber Round 3 CPA-PKE encryption algorithm, and is reproduced
/// below:
///
/// ```plaintext
/// Input: Public key pk ∈ B^{12·k·n / 8 + 32}
/// Input: Message m ∈ B^{32}
/// Input: Random coins r ∈ B32
/// Output: Ciphertext c ∈ B^{d_u·k·n/8 + d_v·n/8}
/// N := 0
/// tˆ := Decode_12(pk)
/// ρ := pk + 12·k·n / 8
/// for i from 0 to k−1 do
///     for j from 0 to k − 1 do
///         AˆT[i][j] := Parse(XOF(ρ, i, j))
///     end for
/// end for
/// for i from 0 to k−1 do
///     r[i] := CBD{η1}(PRF(r, N))
///     N := N + 1
/// end for
/// for i from 0 to k−1 do
///     e_1[i] := CBD_{η2}(PRF(r,N))
///     N := N + 1
/// end for
/// e_2 := CBD{η2}(PRF(r, N))
/// rˆ := NTT(r)
/// u := NTT^{-1}(AˆT ◦ rˆ) + e_1
/// v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
/// c_1 := Encode_{du}(Compress_q(u,d_u))
/// c_2 := Encode_{dv}(Compress_q(v,d_v))
/// return c = c1 || c2
/// ```
///
/// The Kyber Round 3 specification can be found at:
/// <https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf>
#[allow(non_snake_case)]
pub(crate) fn encrypt(
    public_key: &[u8; CPA_PKE_PUBLIC_KEY_SIZE],
    message: [u8; CPA_PKE_MESSAGE_SIZE],
    randomness: &[u8; 32],
) -> Result<CiphertextCpa, BadRejectionSamplingRandomnessError> {
    // tˆ := Decode_12(pk)
    let mut t_as_ntt_ring_element_bytes = public_key.chunks(BITS_PER_RING_ELEMENT / 8);
    let mut t_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];
    for i in 0..t_as_ntt.len() {
        t_as_ntt[i] = deserialize_little_endian(
            12,
            t_as_ntt_ring_element_bytes.next().expect(
                "t_as_ntt_ring_element_bytes should have enough bytes to deserialize to t_as_ntt",
            ),
        );
    }

    // ρ := pk + 12·k·n / 8
    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         AˆT[i][j] := Parse(XOF(ρ, i, j))
    //     end for
    // end for
    let seed = &public_key[T_AS_NTT_ENCODED_SIZE..];
    let A_transpose = parse_a(seed.into_padded_array(), false)?;

    // for i from 0 to k−1 do
    //     r[i] := CBD{η1}(PRF(r, N))
    //     N := N + 1
    // end for
    // rˆ := NTT(r)
    let mut prf_input: [u8; 33] = randomness.into_padded_array();
    let (r_as_ntt, mut domain_separator) = cbd(prf_input);

    // for i from 0 to k−1 do
    //     e1[i] := CBD_{η2}(PRF(r,N))
    //     N := N + 1
    // end for
    let mut error_1 = [KyberPolynomialRingElement::ZERO; RANK];
    for i in 0..error_1.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // 2 sampling coins * 64
        let prf_output: [u8; 128] = PRF(&prf_input);
        error_1[i] = sample_from_binomial_distribution(2, &prf_output);
    }

    // e_2 := CBD{η2}(PRF(r, N))
    prf_input[32] = domain_separator;
    // 2 sampling coins * 64
    let prf_output: [u8; 128] = PRF(&prf_input);
    let error_2 = sample_from_binomial_distribution(2, &prf_output);

    // u := NTT^{-1}(AˆT ◦ rˆ) + e_1
    let mut u = multiply_matrix_by_column(&A_transpose, &r_as_ntt).map(|r| invert_ntt(r));
    for i in 0..u.len() {
        u[i] = u[i] + error_1[i];
    }

    // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
    let message_as_ring_element = deserialize_little_endian(1, &message);
    let v = invert_ntt(multiply_row_by_column(&t_as_ntt, &r_as_ntt))
        + error_2
        + decompress(message_as_ring_element, 1);

    // c_1 := Encode_{du}(Compress_q(u,d_u))
    let c1 = encode_and_compress_u(u);

    // c_2 := Encode_{dv}(Compress_q(v,d_v))
    let c2 = serialize_little_endian(
        compress(v, VECTOR_V_COMPRESSION_FACTOR),
        VECTOR_V_COMPRESSION_FACTOR,
    );

    let ciphertext = c1
        .into_iter()
        .chain(c2.into_iter())
        .collect::<Vec<u8>>()
        .as_array();

    Ok(ciphertext)
}

/// This function implements Algorithm 6 of the Kyber Round 3 specification;
/// This is the Kyber Round 3 CPA-PKE decryption algorithm, and is reproduced
/// below:
///
/// ```plaintext
/// Input: Secret key sk ∈ B^{12·k·n} / 8
/// Input: Ciphertext c ∈ B^{d_u·k·n / 8} + d_v·n / 8
/// Output: Message m ∈ B^{32}
/// u := Decompress_q(Decode_{d_u}(c), d_u)
/// v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
/// sˆ := Decode_12(sk)
/// m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
/// return m
/// ```
///
/// The Kyber Round 3 specification can be found at:
/// <https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf>
#[allow(non_snake_case)]
pub(crate) fn decrypt(
    secret_key: &[u8; CPA_PKE_SECRET_KEY_SIZE],
    ciphertext: &[u8; CPA_PKE_CIPHERTEXT_SIZE],
) -> [u8; CPA_PKE_MESSAGE_SIZE] {
    let mut u_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];
    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; RANK];

    // u := Decompress_q(Decode_{d_u}(c), d_u)
    for (i, u_bytes) in
        (0..u_as_ntt.len()).zip(ciphertext.chunks((COEFFICIENTS_IN_RING_ELEMENT * 10) / 8))
    {
        let u = deserialize_little_endian(10, u_bytes);
        u_as_ntt[i] = ntt_representation(decompress(u, 10));
    }

    // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
    let v = decompress(
        deserialize_little_endian(VECTOR_V_COMPRESSION_FACTOR, &ciphertext[VECTOR_U_SIZE..]),
        VECTOR_V_COMPRESSION_FACTOR,
    );

    // sˆ := Decode_12(sk)
    let mut secret_as_ntt_ring_element_bytes = secret_key.chunks(BITS_PER_RING_ELEMENT / 8);
    for i in 0..secret_as_ntt.len() {
        secret_as_ntt[i] = deserialize_little_endian(
            12,
            secret_as_ntt_ring_element_bytes.next().expect("secret_as_ntt_ring_element_bytes should have enough bytes to deserialize to secret_as_ntt"),
        );
    }

    // m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
    let message = v - invert_ntt(multiply_row_by_column(&secret_as_ntt, &u_as_ntt));

    // FIXME: remove conversion
    serialize_little_endian(compress(message, 1), 1).as_array()
}
