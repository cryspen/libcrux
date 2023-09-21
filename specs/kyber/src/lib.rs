use hacspec_lib::{ArrayConversion, UpdatingArray2};
use parameters::{
    hash_functions::{G, H, H_DIGEST_SIZE, KDF},
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
/// <https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf>
pub fn generate_keypair(
    randomness: [u8; KYBER768_KEY_GENERATION_SEED_SIZE],
) -> Result<KeyPair, BadRejectionSamplingRandomnessError> {
    let ind_cpa_keypair_randomness = &randomness[0..parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let ind_cpa_key_pair = ind_cpa::generate_keypair(&ind_cpa_keypair_randomness.as_array())?;

    let secret_key_serialized =
        ind_cpa_key_pair.serialize_secret_key(&implicit_rejection_value.as_array());

    let key_pair = KeyPair::new(ind_cpa_key_pair.pk(), secret_key_serialized);
    Ok(key_pair)
}

/// This function implements Algorithm 8 of the Kyber Round 3 specification;
/// This is the Kyber Round 3 CCA-KEM encapsulation algorithm, and is
/// reproduced below:
///
/// ```plaintext
/// Input: Public key pk ∈ B^{12·k·n / 8 + 32}
/// Output: Ciphertext c ∈ B^{d_u·k·n/8 + d_v·n/8}
/// Output: Shared key K ∈ B^{*}
/// m ← B^{32}
/// m ← H(m)
/// (K ̄, r) := G(m || H(pk))
/// c := Kyber.CPAPKE.Enc(pk,m,r)
/// K := KDF(K ̄ || H(c))
/// return(c,K)
/// ```
///
/// The Kyber Round 3 specification can be found at:
/// <https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf>
pub fn encapsulate(
    public_key: PublicKey,
    randomness: [u8; KYBER768_SHARED_SECRET_SIZE],
) -> Result<(Ciphertext, SharedSecret), BadRejectionSamplingRandomnessError> {
    let randomness_hashed = H(&randomness);

    let to_hash: [u8; 2 * H_DIGEST_SIZE] = randomness_hashed.push(&H(&public_key));

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let ciphertext =
        ind_cpa::encrypt(&public_key, randomness_hashed, &pseudorandomness.as_array())?;

    let to_hash: [u8; 2 * H_DIGEST_SIZE] = k_not.push(&H(&ciphertext));
    let shared_secret: SharedSecret = KDF(&to_hash);

    Ok((ciphertext, shared_secret))
}

/// This function implements Algorithm 9 of the Kyber Round 3 specification;
/// This is the Kyber Round 3 CCA-KEM decapsulation algorithm, and is
/// reproduced below:
///
/// ```plaintext
/// Input: Ciphertext c ∈ B^{d_u·k·n/8 + d_v·n/8}
/// Input: Secret key sk ∈ B^{24·k·n / 8 + 96}
/// Output: Shared key K ∈ B^{*}
/// pk := sk + 12·k·n/8
/// h := sk + 24·k·n / 8 + 32 ∈ B^{32}
/// z := sk + 24·k·n /8 + 64
/// m′ := Kyber.CPAPKE.Dec(s, (u, v))
/// (K ̄′, r′) := G(m′ || h)
/// c′ := Kyber.CPAPKE.Enc(pk, m′, r′)
/// if c = c′ then
///     return K := KDF(K ̄′ || H(c))
/// else
///     return K := KDF(z || H(c))
/// end if
/// return K
/// ```
///
/// The Kyber Round 3 specification can be found at:
/// <https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf>
pub fn decapsulate(secret_key: PrivateKey, ciphertext: Ciphertext) -> SharedSecret {
    let (ind_cpa_secret_key, secret_key) = secret_key.split_at(CPA_PKE_SECRET_KEY_SIZE);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(CPA_PKE_PUBLIC_KEY_SIZE);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let decrypted = ind_cpa::decrypt(&ind_cpa_secret_key.as_array(), &ciphertext);

    let to_hash: [u8; CPA_PKE_MESSAGE_SIZE + H_DIGEST_SIZE] =
        decrypted.push(ind_cpa_public_key_hash);

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let reencrypted_ciphertext = ind_cpa::encrypt(
        &ind_cpa_public_key.as_array(),
        decrypted,
        &pseudorandomness.as_array(),
    );

    let to_hash = if let Ok(reencrypted) = reencrypted_ciphertext {
        if ciphertext == reencrypted {
            k_not
        } else {
            implicit_rejection_value
        }
    } else {
        implicit_rejection_value
    };
    assert!(to_hash.len() == 32);
    let to_hash: [u8; 32 + H_DIGEST_SIZE] = to_hash.push(&H(&ciphertext));

    KDF(&to_hash)
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

        parameters::hash_functions::KDF(&to_hash)
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

        #[test]
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

        #[test]
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

        #[test]
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
