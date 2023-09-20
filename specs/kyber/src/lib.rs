use hacspec_lib::{ArrayConversion, UpdatingArray2};
use parameters::{
    hash_functions::{G, H, H_DIGEST_SIZE, J},
    CPA_PKE_KEY_GENERATION_SEED_SIZE, CPA_PKE_MESSAGE_SIZE, CPA_PKE_PUBLIC_KEY_SIZE,
    CPA_PKE_SECRET_KEY_SIZE,
};

mod compress;
mod ind_cpa;
mod matrix;
mod ntt;
mod parameters;
mod sampling;
mod serialize;

pub const KYBER768_SHARED_SECRET_SIZE: usize = CPA_PKE_MESSAGE_SIZE;

pub const KYBER768_KEY_GENERATION_SEED_SIZE: usize =
    CPA_PKE_KEY_GENERATION_SEED_SIZE + KYBER768_SHARED_SECRET_SIZE;

pub const KYBER768_PUBLIC_KEY_SIZE: usize = CPA_PKE_PUBLIC_KEY_SIZE;

pub const KYBER768_SECRET_KEY_SIZE: usize =
    CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + KYBER768_SHARED_SECRET_SIZE;

pub const KYBER768_CIPHERTEXT_SIZE: usize = parameters::CPA_PKE_CIPHERTEXT_SIZE;

pub type PublicKey = [u8; KYBER768_PUBLIC_KEY_SIZE];
pub type PrivateKey = [u8; KYBER768_SECRET_KEY_SIZE];

pub type Ciphertext = [u8; KYBER768_CIPHERTEXT_SIZE];
pub type SharedSecret = [u8; KYBER768_SHARED_SECRET_SIZE];

#[derive(Debug)]
pub struct BadRejectionSamplingRandomnessError;

pub struct KeyPair {
    pk: PublicKey,
    sk: PrivateKey,
}

impl KeyPair {
    pub fn new(pk: PublicKey, sk: PrivateKey) -> Self {
        Self { pk, sk }
    }

    pub fn pk(&self) -> &PublicKey {
        &self.pk
    }

    pub fn sk(&self) -> &PrivateKey {
        &self.sk
    }
}

/// This function implements most of <strong>Algorithm 15</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CCA-KEM key generation algorithm.
///
/// We say "most of" since Algorithm 15 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `randomness` parameter.
///
/// Algorithm 15 is reproduced below:
///
/// ```plaintext
/// Output: encapsulation key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Output: decapsulation key dkₚₖₑ ∈ 𝔹^{768k+96}.
///
/// z ←$ 𝔹³²
/// (ekₚₖₑ, dkₚₖₑ) ← K-PKE.KeyGen()
/// ek ← ekₚₖₑ
/// dk ← (dkₚₖₑ ‖ ek ‖ H(ek) ‖ z)
/// return (ek, dk)
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub fn generate_keypair(
    randomness: [u8; KYBER768_KEY_GENERATION_SEED_SIZE],
) -> Result<KeyPair, BadRejectionSamplingRandomnessError> {
    let ind_cpa_keypair_randomness = &randomness[0..parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    // (ekₚₖₑ, dkₚₖₑ) ← K-PKE.KeyGen()
    let ind_cpa_key_pair = ind_cpa::generate_keypair(&ind_cpa_keypair_randomness.as_array())?;

    // dk ← (dkₚₖₑ ‖ ek ‖ H(ek) ‖ z)
    let secret_key_serialized =
        ind_cpa_key_pair.serialize_secret_key(&implicit_rejection_value.as_array());

    // return (ek, dk)
    let key_pair = KeyPair::new(ind_cpa_key_pair.pk(), secret_key_serialized);
    Ok(key_pair)
}

/// This function implements most of <strong>Algorithm 16</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CCA-KEM encapsulation algorithm.
///
/// We say "most of" since Algorithm 16 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `randomness` parameter.
///
/// Algorithm 16 is reproduced below:
///
/// ```plaintext
/// Validated input: encapsulation key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Output: shared key K ∈ 𝔹³².
/// Output: ciphertext c ∈ 𝔹^{dᵤk + dᵥ}.
///
/// Input validation step 1. (Type check.) If ek is not an array of bytes of length
/// 384k + 32 for the value of k specifed by the relevant parameter set, the input
/// is invalid.
///
/// Input validation step 2. (Modulus check.) Perform the computation
/// ek' ← ByteEncode₁₂(ByteDecode₁₂(ek)). If ek' ≠ ek, the input is invalid.
///
/// m ←$ 𝔹³²
/// (K,r) ← G(m ‖ H(ek))
/// c ← K-PKE.Encrypt(ek, m, r)
/// return(K,c)
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub fn encapsulate(
    // Input validation step 1 is performed by specifying the type of
    // |public_key| to be |PublicKey|
    public_key: PublicKey,
    randomness: [u8; KYBER768_SHARED_SECRET_SIZE],
) -> Result<(Ciphertext, SharedSecret), BadRejectionSamplingRandomnessError> {
    // Input validation step 2
    //assert_eq!(&public_key, serialize::byte_encode(12, serialize::byte_decode(12, &public_key)).as_slice());

    // (K,r) ← G(m ‖ H(ek))
    let to_hash: [u8; 2 * H_DIGEST_SIZE] = randomness.push(&H(&public_key));

    let hashed = G(&to_hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(32);

    // c ← K-PKE.Encrypt(ek, m, r)
    let ciphertext =
        ind_cpa::encrypt(&public_key, randomness, &pseudorandomness.as_array())?;

    // return(K,c)
    Ok((ciphertext, shared_secret.as_array()))
}

pub fn decapsulate(secret_key: PrivateKey, ciphertext: Ciphertext) -> SharedSecret {
    let (ind_cpa_secret_key, secret_key) = secret_key.split_at(CPA_PKE_SECRET_KEY_SIZE);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(CPA_PKE_PUBLIC_KEY_SIZE);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let decrypted = ind_cpa::decrypt(&ind_cpa_secret_key.as_array(), &ciphertext);

    let to_hash: [u8; CPA_PKE_MESSAGE_SIZE + H_DIGEST_SIZE] =
        decrypted.push(ind_cpa_public_key_hash);
    let hashed = G(&to_hash);
    let (success_shared_secret, pseudorandomness) = hashed.split_at(32);

    let to_hash: [u8; KYBER768_SHARED_SECRET_SIZE + KYBER768_CIPHERTEXT_SIZE] =
        implicit_rejection_value.push(&ciphertext);
    let failed_shared_secret : [u8; KYBER768_SHARED_SECRET_SIZE] = J(&to_hash);

    let reencrypted_ciphertext = ind_cpa::encrypt(
        &ind_cpa_public_key.as_array(),
        decrypted,
        &pseudorandomness.as_array(),
    );

    if let Ok(reencrypted) = reencrypted_ciphertext {
        if ciphertext == reencrypted {
            success_shared_secret.as_array()
        } else {
            failed_shared_secret
        }
    } else {
        failed_shared_secret
    }
}

#[cfg(test)]
mod tests {
    use proptest::collection::vec;
    use proptest::prelude::*;

    use super::*;

    const IMPLICIT_REJECTION_VALUE_POSITION: usize = parameters::CPA_PKE_SECRET_KEY_SIZE
        + parameters::CPA_PKE_PUBLIC_KEY_SIZE
        + parameters::hash_functions::H_DIGEST_SIZE;

    pub fn decapsulate_with_implicit_rejection_value(
        secret_key: PrivateKey,
        ciphertext: [u8; KYBER768_CIPHERTEXT_SIZE],
    ) -> SharedSecret {
        let mut to_hash = secret_key[IMPLICIT_REJECTION_VALUE_POSITION..].to_vec();
        to_hash.extend_from_slice(&parameters::hash_functions::H(&ciphertext));

        parameters::hash_functions::J(&to_hash)
    }

    proptest! {
        #[test]
        fn consistency(key_generation_randomness in vec(any::<u8>(), KYBER768_KEY_GENERATION_SEED_SIZE), encapsulation_randomness in vec(any::<u8>(), KYBER768_SHARED_SECRET_SIZE)) {
            if let Ok(key_pair) = generate_keypair(key_generation_randomness.try_into().unwrap()) {
                if let Ok((ciphertext, shared_secret)) = encapsulate(key_pair.pk, encapsulation_randomness.try_into().unwrap()) {
                    let shared_secret_decapsulated = decapsulate(key_pair.sk, ciphertext);

                    assert_eq!(shared_secret, shared_secret_decapsulated);
                }
            }
            // If the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }

        //#[test]
        fn modified_ciphertext(
            key_generation_randomness in vec(any::<u8>(), KYBER768_KEY_GENERATION_SEED_SIZE),
            encapsulation_randomness in vec(any::<u8>(), KYBER768_SHARED_SECRET_SIZE),

            ciphertext_position in 0usize..KYBER768_CIPHERTEXT_SIZE,
            random_byte in 1u8..u8::MAX
            ) {
            if let Ok(key_pair) = generate_keypair(key_generation_randomness.try_into().unwrap()) {
                if let Ok((mut ciphertext, shared_secret)) = encapsulate(key_pair.pk, encapsulation_randomness.try_into().unwrap()) {
                    ciphertext[ciphertext_position] ^= random_byte;
                    let shared_secret_decapsulated = decapsulate(key_pair.sk, ciphertext);

                    assert_ne!(shared_secret, shared_secret_decapsulated);

                    let implicit_rejection_shared_secret = decapsulate_with_implicit_rejection_value(key_pair.sk, ciphertext);
                    assert_eq!(shared_secret_decapsulated, implicit_rejection_shared_secret);

                }
            }
            // If the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }

        //#[test]
        fn modified_secret_key(
            key_generation_randomness in vec(any::<u8>(), KYBER768_KEY_GENERATION_SEED_SIZE),
            encapsulation_randomness in vec(any::<u8>(), KYBER768_SHARED_SECRET_SIZE),

            secret_key_position in 0usize..(KYBER768_SECRET_KEY_SIZE - KYBER768_SHARED_SECRET_SIZE),
            random_byte in 1u8..u8::MAX
            ) {
            if let Ok(mut key_pair) = generate_keypair(key_generation_randomness.try_into().unwrap()) {
                if let Ok((ciphertext, shared_secret)) = encapsulate(key_pair.pk, encapsulation_randomness.try_into().unwrap()) {
                    key_pair.sk[secret_key_position] ^= random_byte;
                    let shared_secret_decapsulated = decapsulate(key_pair.sk, ciphertext);

                    assert_ne!(shared_secret, shared_secret_decapsulated);
                }
            }
            // If the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }

        //#[test]
        fn modified_ciphertext_and_implicit_rejection_value(
            key_generation_randomness in vec(any::<u8>(), KYBER768_KEY_GENERATION_SEED_SIZE),
            encapsulation_randomness in vec(any::<u8>(), KYBER768_SHARED_SECRET_SIZE),

            secret_key_position in IMPLICIT_REJECTION_VALUE_POSITION..KYBER768_SECRET_KEY_SIZE,
            random_byte_for_secret_key in 1u8..u8::MAX,

            ciphertext_position in 0usize..KYBER768_CIPHERTEXT_SIZE,
            random_byte_for_ciphertext in 1u8..u8::MAX
            ) {
            if let Ok(mut key_pair) = generate_keypair(key_generation_randomness.try_into().unwrap()) {
                if let Ok((mut ciphertext, _)) = encapsulate(key_pair.pk, encapsulation_randomness.try_into().unwrap()) {
                    ciphertext[ciphertext_position] ^= random_byte_for_ciphertext;
                    let shared_secret_decapsulated = decapsulate(key_pair.sk, ciphertext);

                    key_pair.sk[secret_key_position] ^= random_byte_for_secret_key;
                    let shared_secret_decapsulated_2 = decapsulate(key_pair.sk, ciphertext);

                    assert_ne!(shared_secret_decapsulated, shared_secret_decapsulated_2);
                }
            }
            // If the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    }
}
