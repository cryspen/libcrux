use hacspec_lib::{
    ArrayConversion, ArrayPadding, PanickingIntegerCasts, UpdatableArray, UpdatingArray, VecUpdate,
};

use crate::{
    compress::{compress, decompress},
    matrix::{multiply_column_by_row, multiply_matrix_transpose_by_column, transpose},
    ntt::{ntt_inverse, ntt_inverse_vector, ntt_vector},
    parameters::{
        hash_functions::{G, H, PRF, XOF},
        KyberMatrix, KyberVector, BYTES_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT,
        CPA_PKE_CIPHERTEXT_SIZE, CPA_PKE_KEY_GENERATION_SEED_SIZE, CPA_PKE_MESSAGE_SIZE,
        CPA_PKE_PUBLIC_KEY_SIZE, CPA_PKE_SECRET_KEY_SIZE, CPA_SERIALIZED_KEY_LEN, RANK,
        REJECTION_SAMPLING_SEED_SIZE, T_AS_NTT_ENCODED_SIZE, VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_U_ENCODED_SIZE, VECTOR_V_COMPRESSION_FACTOR,
    },
    sampling::{sample_ntt, sample_poly_cbd},
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

fn encode_12(input: KyberVector) -> Vec<u8> {
    let mut out = Vec::new();
    for re in input.into_iter() {
        out.extend_from_slice(&serialize_little_endian(re, 12));
    }

    out
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
/// d $← B
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
pub(crate) fn generate_keypair(
    key_generation_seed: &[u8; CPA_PKE_KEY_GENERATION_SEED_SIZE],
) -> Result<KeyPair, BadRejectionSamplingRandomnessError> {
    // (ρ,σ) ← G(d)
    let hashed = G(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    // N := 0
    let mut domain_separator: u8 = 0;

    // for (i ← 0; i < k; i++)
    //     for(j ← 0; j < k; j++)
    //         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
    //     end for
    // end for
    let mut A_as_ntt = [KyberVector::new(), KyberVector::new(), KyberVector::new()];

    let mut xof_input: [u8; 34] = seed_for_A.into_padded_array();

    for i in 0..RANK {
        for j in 0..RANK {
            xof_input[32] = i.as_u8();
            xof_input[33] = j.as_u8();
            let xof_bytes: [u8; REJECTION_SAMPLING_SEED_SIZE] = XOF(&xof_input);

            A_as_ntt[i][j] = sample_ntt(xof_bytes)?;
        }
    }

    // for(i ← 0; i < k; i++)
    //     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
    //     N ← N + 1
    // end for
    let mut secret = KyberVector::new();
    let mut prf_input: [u8; 33] = seed_for_secret_and_error.into_padded_array();

    for i in 0..RANK {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // η₁ * 64 = 2 * 64 sampling coins
        let prf_output: [u8; 128] = PRF(&prf_input);
        secret[i] = sample_poly_cbd(2, &prf_output[..]);
    }

    // for(i ← 0; i < k; i++)
    //     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
    //     N ← N + 1
    // end for
    let mut error = KyberVector::new();

    for i in 0..error.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // η₂ * 64 = 2 * 64 sampling coins
        let prf_output: [u8; 128] = PRF(&prf_input);

        error[i] = sample_poly_cbd(2, &prf_output[..]);
    }

    // ŝ ← NTT(s)
    let secret_as_ntt = ntt_vector(secret);

    // ê ← NTT(e)
    let error_as_ntt = ntt_vector(error);

    // t̂ ← Â◦ŝ + ê
    let mut t_as_ntt = multiply_matrix_transpose_by_column(&A_as_ntt, &secret_as_ntt);
    t_as_ntt = t_as_ntt + error_as_ntt;
    // for i in 0..t_as_ntt.len() {
    //     t_as_ntt[i] = t_as_ntt[i] + error_as_ntt[i];
    // }

    // ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
    let public_key_serialized = encode_12(t_as_ntt).concat(seed_for_A);

    // dkₚₖₑ ← ByteEncode₁₂(ŝ)
    let secret_key_serialized = encode_12(secret_as_ntt);

    Ok(KeyPair::new(
        secret_key_serialized.into_array(),
        public_key_serialized.into_array(),
    ))
}

fn encode_and_compress_u(input: KyberVector) -> Vec<u8> {
    let mut out = Vec::new();
    for re in input.into_iter() {
        out.extend_from_slice(&serialize_little_endian(
            compress(re, VECTOR_U_COMPRESSION_FACTOR),
            VECTOR_U_COMPRESSION_FACTOR,
        ));
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
pub(crate) fn encrypt(
    public_key: &[u8; CPA_PKE_PUBLIC_KEY_SIZE],
    message: [u8; CPA_PKE_MESSAGE_SIZE],
    randomness: &[u8; 32],
) -> Result<CiphertextCpa, BadRejectionSamplingRandomnessError> {
    let t_as_ntt = byte_decode_12(&public_key[..T_AS_NTT_ENCODED_SIZE]);
    let seed_for_A = &public_key[T_AS_NTT_ENCODED_SIZE..];

    /// ```text
    /// for (i ← 0; i < k; i++)
    ///     for(j ← 0; j < k; j++)
    ///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
    ///     end for
    /// end for
    /// ```
    fn sample_ntt_matrix(
        mut xof_input: [u8; 34],
    ) -> Result<KyberMatrix, BadRejectionSamplingRandomnessError> {
        let mut A_as_ntt = [KyberVector::new(), KyberVector::new(), KyberVector::new()];
        for i in 0..RANK {
            for j in 0..RANK {
                xof_input[32] = i.as_u8();
                xof_input[33] = j.as_u8();
                let xof_bytes: [u8; REJECTION_SAMPLING_SEED_SIZE] = XOF(&xof_input);

                A_as_ntt[i][j] = sample_ntt(xof_bytes)?;
            }
        }
        Ok(A_as_ntt)
    }

    let A_as_ntt = sample_ntt_matrix(seed_for_A.into_padded_array())?;

    // ```text
    // for(i ← 0; i < k; i++)
    //     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
    //     N ← N + 1
    // end for
    // ```
    fn sample_poly_cbd_(mut prf_input: [u8; 33], domain_separator: u8) -> KyberVector {
        let mut r = KyberVector::new();

        for i in 0..r.len() {
            prf_input[32] = i as u8 + domain_separator;

            // η₁ * 64 = 2 * 64 sampling coins
            let prf_output: [u8; 128] = PRF(&prf_input);

            r[i] = sample_poly_cbd(2, &prf_output);
        }

        r
    }
    let mut prf_input = randomness.into_padded_array();
    let r = sample_poly_cbd_(prf_input, 0);
    let error_1 = sample_poly_cbd_(prf_input, RANK as u8);

    // e_2 := CBD{η₂}(PRF(r, N))
    prf_input[32] = (2 * RANK) as u8;
    // η₂ * 64 = 2 * 64 sampling coins
    let prf_output: [u8; 128] = PRF(&prf_input);
    let error_2 = sample_poly_cbd(2, &prf_output);

    // r̂ ← NTT(r)
    let r_as_ntt = ntt_vector(r);

    // u ← NTT-¹(Âᵀ ◦ r̂) + e₁
    let A_as_ntt_transpose = transpose(&A_as_ntt);
    let u = multiply_matrix_transpose_by_column(&A_as_ntt_transpose, &r_as_ntt);
    let u = ntt_inverse_vector(u) + error_1;

    // μ ← Decompress₁(ByteDecode₁(m)))
    let message_as_ring_element = decompress(deserialize_little_endian(1, &message), 1);

    // v ← NTT-¹(t̂ᵀ ◦ r̂) + e₂ + μ
    let v = ntt_inverse(multiply_column_by_row(&t_as_ntt, &r_as_ntt));
    let v = v + error_2 + message_as_ring_element;

    // c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
    let c1 = encode_and_compress_u(u);

    // c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
    let c2 = serialize_little_endian(
        compress(v, VECTOR_V_COMPRESSION_FACTOR),
        VECTOR_V_COMPRESSION_FACTOR,
    );

    // return c ← (c₁ ‖ c₂)
    let mut ciphertext: CiphertextCpa = (&c1).into_padded_array();
    ciphertext[VECTOR_U_ENCODED_SIZE..].copy_from_slice(c2.as_slice());

    Ok(ciphertext)
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
pub(crate) fn decrypt(
    secret_key: &[u8; CPA_PKE_SECRET_KEY_SIZE],
    ciphertext: &[u8; CPA_PKE_CIPHERTEXT_SIZE],
) -> [u8; CPA_PKE_MESSAGE_SIZE] {
    let u = decompress_du(ciphertext);
    let v = decompress(
        deserialize_little_endian(
            VECTOR_V_COMPRESSION_FACTOR,
            &ciphertext[VECTOR_U_ENCODED_SIZE..],
        ),
        VECTOR_V_COMPRESSION_FACTOR,
    );
    let secret_as_ntt = byte_decode_12(secret_key);

    // w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
    let u_as_ntt = ntt_vector(u);
    let message = v - ntt_inverse(multiply_column_by_row(&secret_as_ntt, &u_as_ntt));

    // m ← ByteEncode₁(Compress₁(w))
    // return m
    // FIXME: remove conversion
    serialize_little_endian(compress(message, 1), 1).as_array()
}

/// Decode
///
/// Input has to be of length CPA_PKE_SECRET_KEY_SIZE or T_AS_NTT_ENCODED_SIZE
fn byte_decode_12(secret_key: &[u8]) -> KyberVector {
    let mut secret_as_ntt = KyberVector::new();
    for (i, secret_bytes) in secret_key.chunks_exact(BYTES_PER_RING_ELEMENT).enumerate() {
        secret_as_ntt[i] = deserialize_little_endian(12, secret_bytes);
    }
    secret_as_ntt
}

fn decompress_du(ciphertext: &[u8; CPA_PKE_CIPHERTEXT_SIZE]) -> KyberVector {
    let mut u = KyberVector::new();
    for (i, u_bytes) in ciphertext[..VECTOR_U_ENCODED_SIZE]
        .chunks((COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8)
        .enumerate()
    {
        u[i] = decompress(
            deserialize_little_endian(VECTOR_U_COMPRESSION_FACTOR, u_bytes),
            VECTOR_U_COMPRESSION_FACTOR,
        );
    }
    u
}
