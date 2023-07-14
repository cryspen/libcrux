mod parameters;
mod field;
mod ring;
mod bit_vector;
mod sampling;
mod serialize;
mod ind_cpa;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

pub const KYBER768_KEY_GENERATION_SEED_SIZE: usize =
    parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE + parameters::KEM_SHARED_SECRET_SIZE;
pub const KYBER768_PUBLIC_KEY_SIZE: usize = parameters::CPA_PKE_PUBLIC_KEY_SIZE;

pub const KYBER768_SECRET_KEY_SIZE: usize = parameters::CPA_PKE_SECRET_KEY_SIZE
    + parameters::CPA_PKE_PUBLIC_KEY_SIZE
    + parameters::hash_functions::H_DIGEST_SIZE
    + parameters::KEM_SHARED_SECRET_SIZE;

///
/// This function implements Algorithm 7 of the Kyber Round 3 specification;
/// This is the Kyber Round 3 CCA-KEM key generation algorithm, and is
/// reproduced below:
///
/// ```plaintext
/// Output: Public key pk ∈ B12·k·n/8+32
/// Output: Secret key sk ∈ B24·k·n/8+96
/// z←B32
/// (pk , sk′) := Kyber.CPAPKE.KeyGen()
/// sk := (sk′ || pk || H(pk) || z)
/// return (pk,sk)
/// ```
///
/// The Kyber Round 3 specification can be found at:
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
pub fn generate_keypair(
    key_generation_seed: [u8; KYBER768_KEY_GENERATION_SEED_SIZE],
) -> (
    [u8; KYBER768_PUBLIC_KEY_SIZE],
    [u8; KYBER768_SECRET_KEY_SIZE],
) {
    let ind_cpa_key_generation_seed =
        &key_generation_seed[0..parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value =
        &key_generation_seed[parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let (ind_cpa_public_key, ind_cpa_secret_key) =
        ind_cpa::generate_keypair(ind_cpa_key_generation_seed.try_into().unwrap());

    let secret_key_serialized = ind_cpa_secret_key
        .into_iter()
        .chain(ind_cpa_public_key.into_iter())
        .chain(parameters::hash_functions::H!(ind_cpa_public_key).into_iter())
        .chain(implicit_rejection_value.iter().cloned())
        .collect::<Vec<u8>>();

    (
        ind_cpa_public_key,
        secret_key_serialized.try_into().unwrap(),
    )
}
