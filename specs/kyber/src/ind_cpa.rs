use crate::ntt::*;
use crate::parameters;
use crate::parameters::KyberPolynomialRingElement;
use crate::BadRejectionSamplingRandomnessError;

///
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
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
#[allow(non_snake_case)]
pub(crate) fn generate_keypair(
    key_generation_seed: &[u8; parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE],
) -> Result<
    (
        [u8; parameters::CPA_PKE_PUBLIC_KEY_SIZE],
        [u8; parameters::CPA_PKE_SECRET_KEY_SIZE],
    ),
    BadRejectionSamplingRandomnessError,
> {
    let mut xof_input: [u8; 34] = [0; 34];
    let mut prf_input: [u8; 33] = [0; 33];

    let mut A_transpose = [[KyberPolynomialRingElement::ZERO; parameters::RANK]; parameters::RANK];
    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];
    let mut error_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];

    // N := 0
    let mut domain_separator: u8 = 0;

    // (ρ,σ) := G(d)
    let hashed = parameters::hash_functions::G(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         Aˆ [i][j] := Parse(XOF(ρ, j, i))
    //     end for
    // end for
    xof_input[0..seed_for_A.len()].copy_from_slice(seed_for_A);

    for i in 0..parameters::RANK {
        for j in 0..parameters::RANK {
            xof_input[32] = i.try_into().expect(
                "usize -> u8 conversion should succeed since 0 <= i < parameters::RANK <= 4.",
            );
            xof_input[33] = j.try_into().expect(
                "usize -> u8 conversion should succeed since 0 <= j < parameters::RANK <= 4.",
            );

            let xof_bytes = parameters::hash_functions::XOF::<
                { parameters::REJECTION_SAMPLING_SEED_SIZE },
            >(&xof_input);

            // A[i][j] = A_transpose[j][i]
            A_transpose[j][i] =
                KyberPolynomialRingElement::sample_from_uniform_distribution(xof_bytes)?;
        }
    }

    // for i from 0 to k−1 do
    //     s[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // sˆ := NTT(s)
    prf_input[0..seed_for_secret_and_error.len()].copy_from_slice(seed_for_secret_and_error);

    for i in 0..secret_as_ntt.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output = parameters::hash_functions::PRF::<
            128, // 2 sampling coins * 64
        >(&prf_input);

        let secret =
            KyberPolynomialRingElement::sample_from_binomial_distribution(2, &prf_output[..]);
        secret_as_ntt[i] = secret.ntt_representation();
    }

    // for i from 0 to k−1 do
    //     e[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // eˆ := NTT(e)
    for i in 0..error_as_ntt.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output = parameters::hash_functions::PRF::<
            128, // 2 sampling coins * 64
        >(&prf_input);

        let error =
            KyberPolynomialRingElement::sample_from_binomial_distribution(2, &prf_output[..]);
        error_as_ntt[i] = error.ntt_representation();
    }

    // tˆ := Aˆ ◦ sˆ + eˆ
    let mut t_as_ntt = multiply_matrix_by_vector(&A_transpose, &secret_as_ntt);
    for i in 0..t_as_ntt.len() {
        t_as_ntt[i] = t_as_ntt[i] + error_as_ntt[i];
    }

    // pk := (Encode_12(tˆ mod^{+}q) || ρ)
    let mut public_key_serialized = t_as_ntt
        .iter()
        .flat_map(|r| r.serialize(12))
        .collect::<Vec<u8>>();
    public_key_serialized.extend_from_slice(seed_for_A);

    // sk := Encode_12(sˆ mod^{+}q)
    let secret_key_serialized = secret_as_ntt
        .iter()
        .flat_map(|r| r.serialize(12))
        .collect::<Vec<u8>>();

    Ok((
        public_key_serialized.try_into().unwrap_or_else(|_| {
            panic!(
                "public_key_serialized should have length {}.",
                parameters::CPA_PKE_PUBLIC_KEY_SIZE
            )
        }),
        secret_key_serialized.try_into().unwrap_or_else(|_| {
            panic!(
                "secret_key_serialized should have length {}.",
                parameters::CPA_PKE_SECRET_KEY_SIZE
            )
        }),
    ))
}

///
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
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
#[allow(non_snake_case)]
pub(crate) fn encrypt(
    public_key: &[u8; parameters::CPA_PKE_PUBLIC_KEY_SIZE],
    message: [u8; parameters::CPA_PKE_MESSAGE_SIZE],
    randomness: &[u8; 32],
) -> Result<[u8; parameters::CPA_PKE_CIPHERTEXT_SIZE], BadRejectionSamplingRandomnessError> {
    let mut xof_input: [u8; 34] = [0; 34];
    let mut prf_input: [u8; 33] = [0; 33];

    let mut A_transpose = [[KyberPolynomialRingElement::ZERO; parameters::RANK]; parameters::RANK];
    let mut r_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];
    let mut error_1 = [KyberPolynomialRingElement::ZERO; parameters::RANK];

    let mut domain_separator: u8 = 0;

    let message_as_ring_element = KyberPolynomialRingElement::new_from_bytes(1, &message);

    // tˆ := Decode_12(pk)
    let mut t_as_ntt_ring_element_bytes = public_key.chunks(parameters::BITS_PER_RING_ELEMENT / 8);
    let mut t_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];
    for i in 0..t_as_ntt.len() {
        t_as_ntt[i] = KyberPolynomialRingElement::new_from_bytes(
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
    let seed_for_A = &public_key[parameters::T_AS_NTT_ENCODED_SIZE..];
    xof_input[0..seed_for_A.len()].copy_from_slice(seed_for_A);

    for i in 0..parameters::RANK {
        for j in 0..parameters::RANK {
            xof_input[32] = i
                .try_into()
                .expect("usize -> u8 conversion should succeed since 0 <= i < parameters::RANK.");
            xof_input[33] = j
                .try_into()
                .expect("usize -> u8 conversion should succeed since 0 <= j < parameters::RANK.");

            let xof_bytes = parameters::hash_functions::XOF::<
                { parameters::REJECTION_SAMPLING_SEED_SIZE },
            >(&xof_input);

            A_transpose[i][j] =
                KyberPolynomialRingElement::sample_from_uniform_distribution(xof_bytes)?;
        }
    }

    // for i from 0 to k−1 do
    //     r[i] := CBD{η1}(PRF(r, N))
    //     N := N + 1
    // end for
    // rˆ := NTT(r)
    prf_input[0..randomness.len()].copy_from_slice(randomness);

    for i in 0..r_as_ntt.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output = parameters::hash_functions::PRF::<
            128, // 2 sampling coins * 64
        >(&prf_input);

        let r = KyberPolynomialRingElement::sample_from_binomial_distribution(2, &prf_output[..]);
        r_as_ntt[i] = r.ntt_representation();
    }

    // for i from 0 to k−1 do
    //     e1[i] := CBD_{η2}(PRF(r,N))
    //     N := N + 1
    // end for
    for i in 0..error_1.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        let prf_output = parameters::hash_functions::PRF::<
            128, // 2 sampling coins * 64
        >(&prf_input);
        error_1[i] =
            KyberPolynomialRingElement::sample_from_binomial_distribution(2, &prf_output[..]);
    }

    // e_2 := CBD{η2}(PRF(r, N))
    prf_input[32] = domain_separator;
    let prf_output = parameters::hash_functions::PRF::<
        128, // 2 sampling coins * 64
    >(&prf_input);
    let error_2 = KyberPolynomialRingElement::sample_from_binomial_distribution(2, &prf_output[..]);

    // u := NTT^{-1}(AˆT ◦ rˆ) + e_1
    let mut u = multiply_matrix_by_vector(&A_transpose, &r_as_ntt).map(|r| r.invert_ntt());
    for i in 0..u.len() {
        u[i] = u[i] + error_1[i];
    }

    // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
    let v = multiply_row_by_column(&t_as_ntt, &r_as_ntt).invert_ntt()
        + error_2
        + message_as_ring_element.decompress(1);

    // c_1 := Encode_{du}(Compress_q(u,d_u))
    let c1 = u
        .iter()
        .map(|r| r.compress(parameters::VECTOR_U_COMPRESSION_FACTOR))
        .flat_map(|r| r.serialize(parameters::VECTOR_U_COMPRESSION_FACTOR));

    // c_2 := Encode_{dv}(Compress_q(v,d_v))
    let c2 = v
        .compress(parameters::VECTOR_V_COMPRESSION_FACTOR)
        .serialize(parameters::VECTOR_V_COMPRESSION_FACTOR);

    let ciphertext = c1.chain(c2.into_iter()).collect::<Vec<u8>>();

    Ok(ciphertext.try_into().unwrap_or_else(|_| {
        panic!(
            "ciphertext should have length {}.",
            parameters::CPA_PKE_CIPHERTEXT_SIZE
        )
    }))
}

///
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
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
#[allow(non_snake_case)]
pub(crate) fn decrypt(
    secret_key: &[u8; parameters::CPA_PKE_SECRET_KEY_SIZE],
    ciphertext: &[u8; parameters::CPA_PKE_CIPHERTEXT_SIZE],
) -> [u8; parameters::CPA_PKE_MESSAGE_SIZE] {
    let mut u_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];
    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];

    // u := Decompress_q(Decode_{d_u}(c), d_u)
    let mut u_as_ntt_ring_element_bytes =
        ciphertext.chunks((u_as_ntt[0].coefficients.len() * 10) / 8);
    for i in 0..u_as_ntt.len() {
        let u = KyberPolynomialRingElement::new_from_bytes(
            10,
            u_as_ntt_ring_element_bytes.next().expect(
                "u_as_ntt_ring_element_bytes should have enough bytes to deserialize to u_as_ntt",
            ),
        );
        u_as_ntt[i] = u.decompress(10).ntt_representation();
    }

    // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
    let v = KyberPolynomialRingElement::new_from_bytes(
        parameters::VECTOR_V_COMPRESSION_FACTOR,
        &ciphertext[parameters::VECTOR_U_SIZE..],
    )
    .decompress(parameters::VECTOR_V_COMPRESSION_FACTOR);

    // sˆ := Decode_12(sk)
    let mut secret_as_ntt_ring_element_bytes =
        secret_key.chunks((secret_as_ntt[0].coefficients.len() * 12) / 8);
    for i in 0..secret_as_ntt.len() {
        secret_as_ntt[i] = KyberPolynomialRingElement::new_from_bytes(
            12,
            secret_as_ntt_ring_element_bytes.next().expect("secret_as_ntt_ring_element_bytes should have enough bytes to deserialize to secret_as_ntt"),
        );
    }

    // m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
    let message = v - multiply_row_by_column(&secret_as_ntt, &u_as_ntt).invert_ntt();
    message
        .compress(1)
        .serialize(1)
        .try_into()
        .expect("Message should be 32 bytes long.")
}
