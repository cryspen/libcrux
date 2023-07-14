use crate::parameters;
use crate::ring::*;
use crate::sampling::*;
use crate::serialize::*;

///
/// This function implements Algorithm 4 of the Kyber Round 3 specification;
/// This is the Kyber Round 3 CPA-PKE key generation algorithm, and is
/// reproduced below:
///
/// ```plaintext
/// Output: Secret key sk ∈ B^{12·k·n/8}
/// Output: Public key pk ∈ B^{12·k·n/8+32}
/// d←B^{32}
/// (ρ,σ):=G(d)
/// N := 0
/// for i from 0 to k−1 do
///     for j from 0 to k − 1 do
///         Aˆ [i][j] := Parse(XOF(ρ, j, i))
///     end for
/// end for
/// for i from 0 to k−1 do
///     s[i] := CBD_{η1}(PRF(σ, N ))
///     N := N + 1
/// end for
/// for i from 0 to k−1 do
///     e[i] := CBD_{η1}(PRF(σ, N ))
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
) -> (
    [u8; parameters::CPA_PKE_PUBLIC_KEY_SIZE],
    [u8; parameters::CPA_PKE_SECRET_KEY_SIZE],
) {
    let mut xof_input: [u8; 34] = [0; 34];
    let mut prf_input: [u8; 33] = [0; 33];

    let mut A_transpose = [[RingElement::ZERO; parameters::RANK]; parameters::RANK];
    let mut secret_as_ntt = [RingElement::ZERO; parameters::RANK];
    let mut error_as_ntt = [RingElement::ZERO; parameters::RANK];

    let mut domain_separator: u8 = 0;

    let hashed = parameters::hash_functions::G!(key_generation_seed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    // Can't use copy_from_slice due to:
    // https://github.com/hacspec/hacspec-v2/issues/151
    for (i, seed_for_A_ith_element) in seed_for_A.iter().enumerate() {
        xof_input[i] = *seed_for_A_ith_element;
    }
    for (i, seed_for_secret_and_error_ith_element) in seed_for_secret_and_error.iter().enumerate() {
        prf_input[i] = *seed_for_secret_and_error_ith_element;
    }

    for i in 0..parameters::RANK {
        for j in 0..parameters::RANK {
            xof_input[32] = i.try_into().unwrap();
            xof_input[33] = j.try_into().unwrap();

            // Using constant due to:
            // https://github.com/hacspec/hacspec-v2/issues/27
            let xof_bytes = parameters::hash_functions::XOF!(2304, xof_input);

            A_transpose[j][i] = sample_ring_element_uniform(xof_bytes).unwrap();
        }
    }

    for i in 0..secret_as_ntt.len() {
        prf_input[32] = domain_separator;

        // Using constant due to:
        // https://github.com/hacspec/hacspec-v2/issues/27
        let prf_output = parameters::hash_functions::PRF!(128, prf_input);

        let secret = sample_ring_element_binomial(prf_output);
        secret_as_ntt[i] = secret.ntt_representation();

        domain_separator += 1;
    }

    for i in 0..error_as_ntt.len() {
        prf_input[32] = domain_separator;

        // Using constant due to:
        // https://github.com/hacspec/hacspec-v2/issues/27
        let prf_output = parameters::hash_functions::PRF!(128, prf_input);

        let error = sample_ring_element_binomial(prf_output);
        error_as_ntt[i] = error.ntt_representation();

        domain_separator += 1;
    }

    let mut t_as_ntt = multiply_matrix_by_vector(&A_transpose, &secret_as_ntt);
    for i in 0..t_as_ntt.len() {
        t_as_ntt[i] = t_as_ntt[i].add(&error_as_ntt[i]);
    }

    let public_key_serialized = t_as_ntt
        .iter()
        .flat_map(serialize_ring_element)
        .chain(seed_for_A.iter().cloned())
        .collect::<Vec<u8>>();

    let secret_key_serialized = secret_as_ntt
        .iter()
        .flat_map(serialize_ring_element)
        .collect::<Vec<u8>>();

    (
        public_key_serialized.try_into().unwrap(),
        secret_key_serialized.try_into().unwrap(),
    )
}
