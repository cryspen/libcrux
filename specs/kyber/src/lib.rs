mod compress;
mod ind_cpa;
mod ntt;
mod parameters;
mod sampling;
mod serialize;

mod helpers;

pub const KYBER768_SHARED_SECRET_SIZE: usize = parameters::CPA_PKE_MESSAGE_SIZE;

pub const KYBER768_KEY_GENERATION_RANDOMNESS_SIZE: usize =
    parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE + KYBER768_SHARED_SECRET_SIZE;

pub const KYBER768_PUBLIC_KEY_SIZE: usize = parameters::CPA_PKE_PUBLIC_KEY_SIZE;

pub const KYBER768_SECRET_KEY_SIZE: usize = parameters::CPA_PKE_SECRET_KEY_SIZE
    + parameters::CPA_PKE_PUBLIC_KEY_SIZE
    + parameters::hash_functions::H_DIGEST_SIZE
    + KYBER768_SHARED_SECRET_SIZE;

pub const KYBER768_CIPHERTEXT_SIZE: usize = parameters::CPA_PKE_CIPHERTEXT_SIZE;

#[derive(Debug)]
pub struct BadRejectionSamplingRandomnessError;

///
/// This function implements Algorithm 7 of the Kyber Round 3 specification;
/// This is the Kyber Round 3 CCA-KEM key generation algorithm, and is
/// reproduced below:
///
/// ```plaintext
/// Output: Public key pk ∈ B^{12·k·n/8+32}
/// Output: Secret key sk ∈ B^{24·k·n/8+96}
/// z←B^{32}
/// (pk , sk′) := Kyber.CPAPKE.KeyGen()
/// sk := (sk′ || pk || H(pk) || z)
/// return (pk,sk)
/// ```
///
/// The Kyber Round 3 specification can be found at:
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
pub fn generate_keypair(
    randomness: [u8; KYBER768_KEY_GENERATION_RANDOMNESS_SIZE],
) -> Result<
    (
        [u8; KYBER768_PUBLIC_KEY_SIZE],
        [u8; KYBER768_SECRET_KEY_SIZE],
    ),
    BadRejectionSamplingRandomnessError,
> {
    let ind_cpa_keypair_randomness = &randomness[0..parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let (ind_cpa_public_key, ind_cpa_secret_key) = ind_cpa::generate_keypair(
        ind_cpa_keypair_randomness
            .try_into()
            .expect("Key generation seed should be 32 bytes long."),
    )?;

    let mut secret_key_serialized = ind_cpa_secret_key.to_vec();
    secret_key_serialized.extend_from_slice(&ind_cpa_public_key);
    secret_key_serialized.extend_from_slice(&parameters::hash_functions::H(&ind_cpa_public_key));
    secret_key_serialized.extend_from_slice(implicit_rejection_value);

    Ok((
        ind_cpa_public_key,
        secret_key_serialized.try_into().unwrap_or_else(|_| {
            panic!(
                "secret_key_serialized should have length {}.",
                KYBER768_SECRET_KEY_SIZE
            )
        }),
    ))
}

pub fn encapsulate(
    public_key: [u8; KYBER768_PUBLIC_KEY_SIZE],
    message: [u8; KYBER768_SHARED_SECRET_SIZE],
) -> Result<
    (
        [u8; KYBER768_CIPHERTEXT_SIZE],
        [u8; KYBER768_SHARED_SECRET_SIZE],
    ),
    BadRejectionSamplingRandomnessError,
> {
    let message_hashed: [u8; 32] = parameters::hash_functions::H(&message);
    let public_key_hashed: [u8; 32] = parameters::hash_functions::H(&public_key);

    let mut to_hash = Vec::<u8>::new();
    to_hash.extend_from_slice(&message_hashed);
    to_hash.extend_from_slice(&public_key_hashed);

    let hashed = parameters::hash_functions::G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let ciphertext = ind_cpa::encrypt(
        &public_key,
        message_hashed,
        pseudorandomness[..].try_into().unwrap(),
    )?;
    let ciphertext_hashed = parameters::hash_functions::H(&ciphertext);

    to_hash = k_not.to_vec();
    to_hash.extend_from_slice(&ciphertext_hashed);

    let shared_secret = parameters::hash_functions::KDF::<32>(&to_hash);

    Ok((ciphertext, shared_secret))
}

pub fn decapsulate(
    secret_key: [u8; KYBER768_SECRET_KEY_SIZE],
    ciphertext: [u8; KYBER768_CIPHERTEXT_SIZE],
) -> [u8; KYBER768_SHARED_SECRET_SIZE] {
    let mut idx = 0;

    let ind_cpa_secret_key = &secret_key[idx..idx + parameters::CPA_PKE_SECRET_KEY_SIZE];
    idx += parameters::CPA_PKE_SECRET_KEY_SIZE;

    let ind_cpa_public_key = &secret_key[idx..idx + parameters::CPA_PKE_PUBLIC_KEY_SIZE];
    idx += parameters::CPA_PKE_PUBLIC_KEY_SIZE;

    let ind_cpa_public_key_hash = &secret_key[idx..idx + parameters::hash_functions::H_DIGEST_SIZE];
    idx += parameters::hash_functions::H_DIGEST_SIZE;

    let implicit_rejection_value = &secret_key[idx..];

    let decrypted = ind_cpa::decrypt(ind_cpa_secret_key.try_into().unwrap(), &ciphertext);

    let mut to_hash = decrypted.to_vec();
    to_hash.extend_from_slice(ind_cpa_public_key_hash);

    let hashed = parameters::hash_functions::G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let ciphertext_hashed = parameters::hash_functions::H(&ciphertext);

    let actual_ciphertext = ind_cpa::encrypt(
        ind_cpa_public_key.try_into().unwrap(),
        decrypted,
        pseudorandomness.try_into().unwrap(),
    );

    to_hash = if let Ok(actual_c) = actual_ciphertext {
        if ciphertext == actual_c {
            k_not.to_vec()
        } else {
            implicit_rejection_value.to_vec()
        }
    } else {
        implicit_rejection_value.to_vec()
    };

    to_hash.extend_from_slice(&ciphertext_hashed);

    parameters::hash_functions::KDF::<{ KYBER768_SHARED_SECRET_SIZE }>(&to_hash)
}
