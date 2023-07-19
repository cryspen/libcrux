use crate::parameters;
use crate::parameters::KyberPolynomialRingElement;
use crate::BadRejectionSamplingRandomnessError;
use crate::ntt::*;

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
/// pk := (Encode12(tˆ mod^{+}q) || ρ)
/// sk := Encode12(sˆ mod^{+}q)
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
    let hashed = parameters::hash_functions::G!(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         Aˆ [i][j] := Parse(XOF(ρ, j, i))
    //     end for
    // end for
    for (i, seed_for_A_ith_element) in seed_for_A.iter().enumerate() {
        // Can't use copy_from_slice due to:
        // https://github.com/hacspec/hacspec-v2/issues/151
        xof_input[i] = *seed_for_A_ith_element;
    }
    for i in 0..parameters::RANK {
        for j in 0..parameters::RANK {
            xof_input[32] = i
                .try_into()
                .expect("usize -> u8 conversion should succeed since 0 <= i < parameters::RANK.");
            xof_input[33] = j
                .try_into()
                .expect("usize -> u8 conversion should succeed since 0 <= j < parameters::RANK.");

            // Using constant due to:
            // https://github.com/hacspec/hacspec-v2/issues/27
            let xof_bytes = parameters::hash_functions::XOF!(2304, xof_input);

            // A[i][j] = A_transpose[j][i]
            A_transpose[j][i] = KyberPolynomialRingElement::sample_from_uniform_distribution(xof_bytes)?;
        }
    }

    // for i from 0 to k−1 do
    //     s[i] := CBD_{η1}(PRF(σ, N))
    //     N := N + 1
    // end for
    // sˆ := NTT(s)
    for (i, seed_for_secret_and_error_ith_element) in seed_for_secret_and_error.iter().enumerate() {
        // Can't use copy_from_slice due to:
        // https://github.com/hacspec/hacspec-v2/issues/151
        prf_input[i] = *seed_for_secret_and_error_ith_element;
    }
    for i in 0..secret_as_ntt.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // Using constant due to:
        // https://github.com/hacspec/hacspec-v2/issues/27
        let prf_output = parameters::hash_functions::PRF!(128, prf_input);

        let secret = KyberPolynomialRingElement::sample_from_binomial_distribution(prf_output);
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

        // Using constant due to:
        // https://github.com/hacspec/hacspec-v2/issues/27
        let prf_output = parameters::hash_functions::PRF!(128, prf_input);

        let error = KyberPolynomialRingElement::sample_from_binomial_distribution(prf_output);
        error_as_ntt[i] = error.ntt_representation();
    }

    // tˆ := Aˆ ◦ sˆ + eˆ
    let mut t_as_ntt = multiply_matrix_by_vector(&A_transpose, &secret_as_ntt);
    for i in 0..t_as_ntt.len() {
        t_as_ntt[i] = t_as_ntt[i] + error_as_ntt[i];
    }


    // pk := (Encode12(tˆ mod^{+}q) || ρ)
    let public_key_serialized = t_as_ntt
        .iter()
        .flat_map(|r| r.serialize())
        .chain(seed_for_A.iter().cloned())
        .collect::<Vec<u8>>();

    // sk := Encode12(sˆ mod^{+}q)
    let secret_key_serialized = secret_as_ntt
        .iter()
        .flat_map(|r| r.serialize())
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

#[allow(non_snake_case)]
pub(crate) fn encrypt(
    public_key: &[u8; parameters::CPA_PKE_PUBLIC_KEY_SIZE],
    message: [u8; 32],
    randomness: &[u8; 32],
) -> Result<[u8; parameters::CPA_PKE_CIPHERTEXT_SIZE], BadRejectionSamplingRandomnessError> {

    let mut xof_input: [u8; 34] = [0; 34];
    let mut prf_input: [u8; 33] = [0; 33];

    let mut A_transpose = [[KyberPolynomialRingElement::ZERO; parameters::RANK]; parameters::RANK];
    let mut r_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];
    let mut error_1 = [KyberPolynomialRingElement::ZERO; parameters::RANK];

    let mut domain_separator : u8 = 0;

    let message_as_ring_element = KyberPolynomialRingElement::new_from_bytes(1, &message);

    let mut t_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];
    for i in 0..t_as_ntt.len() {
        t_as_ntt[i] = KyberPolynomialRingElement::new_from_bytes(parameters::BITS_PER_COEFFICIENT, public_key[i*(parameters::BITS_PER_RING_ELEMENT / 8)..(i+1)*(parameters::BITS_PER_RING_ELEMENT) / 8].try_into().unwrap());
    }

    let seed_for_A = &public_key[parameters::T_AS_NTT_ENCODED_SIZE..];

    // for i from 0 to k−1 do
    //     for j from 0 to k − 1 do
    //         AˆT [i][j] := Parse(XOF(ρ, j, i))
    //     end for
    // end for
    for (i, seed_for_A_ith_element) in seed_for_A.iter().enumerate() {
        // Can't use copy_from_slice due to:
        // https://github.com/hacspec/hacspec-v2/issues/151
        xof_input[i] = *seed_for_A_ith_element;
    }
    for i in 0..parameters::RANK {
        for j in 0..parameters::RANK {
            xof_input[32] = i
                .try_into()
                .expect("usize -> u8 conversion should succeed since 0 <= i < parameters::RANK.");
            xof_input[33] = j
                .try_into()
                .expect("usize -> u8 conversion should succeed since 0 <= j < parameters::RANK.");

            // Using constant due to:
            // https://github.com/hacspec/hacspec-v2/issues/27
            let xof_bytes = parameters::hash_functions::XOF!(2304, xof_input);

            A_transpose[i][j] = KyberPolynomialRingElement::sample_from_uniform_distribution(xof_bytes)?;
        }
    }

    for (i, randomness_ith_element) in randomness.iter().enumerate() {
        // Can't use copy_from_slice due to:
        // https://github.com/hacspec/hacspec-v2/issues/151
        prf_input[i] = *randomness_ith_element;
    }
    for i in 0..r_as_ntt.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // Using constant due to:
        // https://github.com/hacspec/hacspec-v2/issues/27
        let prf_output = parameters::hash_functions::PRF!(128, prf_input);

        let r = KyberPolynomialRingElement::sample_from_binomial_distribution(prf_output);
        r_as_ntt[i] = r.ntt_representation();
    }

    for i in 0..error_1.len() {
        prf_input[32] = domain_separator;
        domain_separator += 1;

        // Using constant due to:
        // https://github.com/hacspec/hacspec-v2/issues/27
        let prf_output = parameters::hash_functions::PRF!(128, prf_input);

        error_1[i] = KyberPolynomialRingElement::sample_from_binomial_distribution(prf_output);
    }

    prf_input[32] = domain_separator;
    let prf_output = parameters::hash_functions::PRF!(128, prf_input);
    let error_2 = KyberPolynomialRingElement::sample_from_binomial_distribution(prf_output);

    let mut u = multiply_matrix_by_vector(&A_transpose, &r_as_ntt).map(|r| r.invert_ntt());
    for i in 0..u.len() {
        u[i] = u[i] + error_1[i];
    }

    let v = multiply_row_by_column(&t_as_ntt, &r_as_ntt).invert_ntt()
              + error_2
              + message_as_ring_element.decompress(1);

    let c1 = u
        .iter()
        .map(|r| r.compress(parameters::U_COMPRESSION_FACTOR.try_into().unwrap()))
        .flat_map(|r| r.serialize())
        .collect::<Vec<u8>>();

    let c2 = v.compress(parameters::V_COMPRESSION_FACTOR.try_into().unwrap()).serialize();

    let ciphertext = c1.into_iter()
        .chain(c2.into_iter())
        .collect::<Vec<u8>>();

    Ok(ciphertext.try_into().unwrap())
}

#[allow(non_snake_case)]
pub(crate) fn decrypt(
    secret_key: &[u8; parameters::CPA_PKE_SECRET_KEY_SIZE],
    ciphertext: &[u8; parameters::CPA_PKE_CIPHERTEXT_SIZE],
) -> [u8; 32] {
    let mut u_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];
    let mut secret_as_ntt = [KyberPolynomialRingElement::ZERO; parameters::RANK];

    for i in 0..u_as_ntt.len() {
        let u = KyberPolynomialRingElement::new_from_bytes(10, &ciphertext[i*(32 * 10)..(i+1)*(32*10)]);
        u_as_ntt[i] = u.decompress(10).ntt_representation();
    }

    let v = KyberPolynomialRingElement::new_from_bytes(parameters::V_COMPRESSION_FACTOR, &ciphertext[parameters::U_VECTOR_SIZE..]).decompress(usize::from(parameters::V_COMPRESSION_FACTOR).try_into().unwrap());

    for i in 0..secret_as_ntt.len() {
        secret_as_ntt[i] = KyberPolynomialRingElement::new_from_bytes(12, &secret_key[i*(32 * 12)..(i+1)*(32*12)]);
    }

    let message = v - multiply_row_by_column(&secret_as_ntt, &u_as_ntt).invert_ntt();

    message.compress(1).serialize().try_into().unwrap()
}
