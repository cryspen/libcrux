// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:986 ~ libcrux[92b3]::kem::kyber768::parameters::COEFFICIENTS_IN_RING_ELEMENT)
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
pub(crate) mod parameters;

#[macro_use]
mod types;
mod arithmetic;
mod compress;
mod constant_time_ops;
mod conversions;
mod hash_functions;
mod ind_cpa;
mod ntt;
mod sampling;
mod serialize;

use constant_time_ops::{
    compare_ciphertexts_in_constant_time, select_shared_secret_in_constant_time,
};
use conversions::into_padded_array;
use hash_functions::{G, H, H_DIGEST_SIZE, KDF};
use parameters::*;

pub const SHARED_SECRET_SIZE: usize = CPA_PKE_MESSAGE_SIZE;

pub const KEY_GENERATION_SEED_SIZE: usize = CPA_PKE_KEY_GENERATION_SEED_SIZE + SHARED_SECRET_SIZE;

pub const PUBLIC_KEY_SIZE: usize = CPA_PKE_PUBLIC_KEY_SIZE_768;

pub const SECRET_KEY_SIZE_512: usize =
    CPA_PKE_SECRET_KEY_SIZE_512 + CPA_PKE_PUBLIC_KEY_SIZE_512 + H_DIGEST_SIZE + SHARED_SECRET_SIZE;
pub const SECRET_KEY_SIZE_768: usize =
    CPA_PKE_SECRET_KEY_SIZE_768 + CPA_PKE_PUBLIC_KEY_SIZE_768 + H_DIGEST_SIZE + SHARED_SECRET_SIZE;
pub const SECRET_KEY_SIZE_1024: usize = CPA_PKE_SECRET_KEY_SIZE_1024
    + CPA_PKE_PUBLIC_KEY_SIZE_1024
    + H_DIGEST_SIZE
    + SHARED_SECRET_SIZE;

pub const CIPHERTEXT_SIZE: usize = parameters::CPA_PKE_CIPHERTEXT_SIZE_768;

#[derive(Debug)]
pub struct BadRejectionSamplingRandomnessError;

use self::ind_cpa::serialize_secret_key;

impl_generic_struct!(KyberCiphertext);
impl_generic_struct!(KyberSharedSecret);
impl_generic_struct!(KyberPrivateKey);
impl_generic_struct!(KyberPublicKey);

/// A Kyber CPA key pair
pub struct CcaKeyPair<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize> {
    pub(crate) sk: KyberPrivateKey<PRIVATE_KEY_SIZE>,
    pub(crate) pk: KyberPublicKey<PUBLIC_KEY_SIZE>,
}

impl<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize>
    CcaKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>
{
    /// Creates a new [`KeyPair`].
    pub fn new(sk: [u8; PRIVATE_KEY_SIZE], pk: [u8; PUBLIC_KEY_SIZE]) -> Self {
        Self {
            sk: sk.into(),
            pk: pk.into(),
        }
    }

    pub fn from(
        sk: KyberPrivateKey<PRIVATE_KEY_SIZE>,
        pk: KyberPublicKey<PUBLIC_KEY_SIZE>,
    ) -> Self {
        Self { sk, pk }
    }

    pub fn public_key(&self) -> &KyberPublicKey<PUBLIC_KEY_SIZE> {
        &self.pk
    }

    pub fn private_key(&self) -> &KyberPrivateKey<PRIVATE_KEY_SIZE> {
        &self.sk
    }

    pub fn pk(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        self.pk.as_slice()
    }

    pub fn sk(&self) -> &[u8; PRIVATE_KEY_SIZE] {
        self.sk.as_slice()
    }
}

pub fn generate_key_pair_768(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<
    CcaKeyPair<{ SECRET_KEY_SIZE_768 }, { parameters::CPA_PKE_PUBLIC_KEY_SIZE_768 }>,
    BadRejectionSamplingRandomnessError,
> {
    generate_keypair::<
        { parameters::RANK_768 },
        { parameters::CPA_PKE_SECRET_KEY_SIZE_768 },
        { SECRET_KEY_SIZE_768 },
        { parameters::CPA_PKE_PUBLIC_KEY_SIZE_768 },
        { parameters::RANKED_BYTES_PER_RING_ELEMENT_768 },
    >(randomness)
}

pub fn generate_keypair<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<CcaKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>, BadRejectionSamplingRandomnessError> {
    let ind_cpa_keypair_randomness = &randomness[0..parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let ((ind_cpa_private_key, public_key), sampling_a_error) = ind_cpa::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
    >(ind_cpa_keypair_randomness);

    let secret_key_serialized = serialize_secret_key(
        ind_cpa_private_key.as_slice(),
        public_key.as_slice(),
        implicit_rejection_value,
    );
    if let Some(error) = sampling_a_error {
        Err(error)
    } else {
        let private_key: KyberPrivateKey<PRIVATE_KEY_SIZE> =
            KyberPrivateKey::from(secret_key_serialized);

        Ok(CcaKeyPair::from(private_key, public_key))
    }
}

pub fn encapsulate_768(
    public_key: &KyberPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<
    (
        KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>,
        KyberSharedSecret<SHARED_SECRET_SIZE>,
    ),
    BadRejectionSamplingRandomnessError,
> {
    encapsulate::<
        RANK_768,
        SHARED_SECRET_SIZE,
        CPA_PKE_CIPHERTEXT_SIZE_768,
        CPA_PKE_PUBLIC_KEY_SIZE_768,
        T_AS_NTT_ENCODED_SIZE_768,
        C1_SIZE_768,
        C2_SIZE_768,
        VECTOR_U_COMPRESSION_FACTOR_768,
        VECTOR_V_COMPRESSION_FACTOR_768,
        C1_BLOCK_SIZE_768,
    >(public_key, randomness)
}

pub fn encapsulate<
    const K: usize,
    const SHARED_SECRET_SIZE: usize,
    const CIPHERTEXT_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_SIZE: usize,
    const C2_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    const VECTOR_U_BLOCK_LEN: usize,
>(
    public_key: &KyberPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<
    (
        KyberCiphertext<CIPHERTEXT_SIZE>,
        KyberSharedSecret<SHARED_SECRET_SIZE>,
    ),
    BadRejectionSamplingRandomnessError,
> {
    let randomness_hashed = H(&randomness);

    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&randomness_hashed);
    to_hash[H_DIGEST_SIZE..].copy_from_slice(&H(public_key.as_slice()));

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let (ciphertext, sampling_a_error) =
        ind_cpa::encrypt::<
            K,
            CIPHERTEXT_SIZE,
            T_AS_NTT_ENCODED_SIZE,
            C1_SIZE,
            C2_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            VECTOR_U_BLOCK_LEN,
        >(public_key.as_slice(), randomness_hashed, pseudorandomness);

    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&k_not);
    to_hash[H_DIGEST_SIZE..].copy_from_slice(&H(ciphertext.as_ref()));

    let shared_secret = KDF(&to_hash).into();

    if sampling_a_error.is_some() {
        Err(sampling_a_error.unwrap())
    } else {
        Ok((ciphertext, shared_secret))
    }
}

pub fn decapsulate_768(
    secret_key: &KyberPrivateKey<SECRET_KEY_SIZE_768>,
    ciphertext: &KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>,
) -> [u8; SHARED_SECRET_SIZE] {
    decapsulate::<
        RANK_768,
        SECRET_KEY_SIZE_768,
        CPA_PKE_CIPHERTEXT_SIZE_768,
        T_AS_NTT_ENCODED_SIZE_768,
        C1_SIZE_768,
        C2_SIZE_768,
        VECTOR_U_COMPRESSION_FACTOR_768,
        VECTOR_V_COMPRESSION_FACTOR_768,
        C1_BLOCK_SIZE_768,
    >(secret_key, ciphertext)
}

pub fn decapsulate<
    const K: usize,
    const SECRET_KEY_SIZE: usize,
    const CIPHERTEXT_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_SIZE: usize,
    const C2_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    const C1_BLOCK_SIZE: usize,
>(
    secret_key: &KyberPrivateKey<SECRET_KEY_SIZE>,
    ciphertext: &KyberCiphertext<CIPHERTEXT_SIZE>,
) -> [u8; SHARED_SECRET_SIZE] {
    let (ind_cpa_secret_key, secret_key) = secret_key.split_at(CPA_PKE_SECRET_KEY_SIZE_768);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(CPA_PKE_PUBLIC_KEY_SIZE_768);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let decrypted = ind_cpa::decrypt::<
        K,
        CIPHERTEXT_SIZE,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
    >(ind_cpa_secret_key, ciphertext);

    let mut to_hash: [u8; CPA_PKE_MESSAGE_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
    to_hash[CPA_PKE_MESSAGE_SIZE..].copy_from_slice(ind_cpa_public_key_hash);

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    // If a ciphertext C is well-formed, setting aside the fact that a
    // decryption failure could (with negligible probability) occur, it must hold that:
    //
    // Encrypt(pk, Decrypt(sk, C)) = C
    //
    // Therefore, if |ind_cpa::encrypt| returns an error,
    // |expected_ciphertext| cannot equal |ciphertext|, thereby resulting in
    // implicit rejection.
    //
    // If C is ill-formed, due to the use of hashing to obtain |pseudorandomness|
    // as well as the fact that the Kyber CPA-PKE is sparse pseudo-random, it is
    // highly likely that |expected_ciphertext| will not equal |ciphertext|, thereby
    // also resulting in implicit rejection.
    //
    // Thus, we ignore the second return value of |ind_cpa::encrypt|.
    let (expected_ciphertext, _) = ind_cpa::encrypt::<
        K,
        CIPHERTEXT_SIZE,
        T_AS_NTT_ENCODED_SIZE,
        C1_SIZE,
        C2_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        C1_BLOCK_SIZE,
    >(ind_cpa_public_key, decrypted, pseudorandomness);

    let selector =
        compare_ciphertexts_in_constant_time(ciphertext.as_ref(), expected_ciphertext.as_ref());
    let to_hash = select_shared_secret_in_constant_time(k_not, implicit_rejection_value, selector);

    let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&to_hash);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(&H(ciphertext.as_ref()));

    KDF(&to_hash)
}
