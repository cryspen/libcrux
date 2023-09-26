// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:986 ~ libcrux[92b3]::kem::kyber768::parameters::COEFFICIENTS_IN_RING_ELEMENT)
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
mod parameters;

#[macro_use]
mod types;
mod arithmetic;
mod compress;
mod constant_time_ops;
mod conversions;
mod ind_cpa;
mod ntt;
mod sampling;
mod serialize;

use constant_time_ops::{
    compare_ciphertexts_in_constant_time, select_shared_secret_in_constant_time,
};
use conversions::into_padded_array;
use parameters::{
    hash_functions::{G, H, H_DIGEST_SIZE, KDF},
    CPA_PKE_KEY_GENERATION_SEED_SIZE, CPA_PKE_MESSAGE_SIZE, CPA_PKE_PUBLIC_KEY_SIZE_768,
    CPA_PKE_SECRET_KEY_SIZE_768,
};

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

// pub type Kyber768PublicKey = [u8; PUBLIC_KEY_SIZE];
// pub type Kyber768PrivateKey = [u8; SECRET_KEY_SIZE];

// pub type Kyber768Ciphertext = [u8; CIPHERTEXT_SIZE];
// pub type Kyber768SharedSecret = [u8; SHARED_SECRET_SIZE];

#[derive(Debug)]
pub struct BadRejectionSamplingRandomnessError;

use parameters::*;

use self::ind_cpa::{serialize_secret_key, CiphertextCpa, CpaKeyPair};

impl_generic_struct!(KyberCiphertext);
impl_generic_struct!(KyberSharedSecret);
impl_generic_struct!(KyberPrivateKey);

// // impl_types!(Kyber512Ciphertext, CPA_PKE_CIPHERTEXT_SIZE_512);
// // pub type Kyber512PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>;
// // pub type Kyber512PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_512>;
// impl_types!(Kyber512SharedSecret, SHARED_SECRET_SIZE);

// impl_types!(Kyber768Ciphertext, CPA_PKE_CIPHERTEXT_SIZE_768);
// // pub type Kyber768PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>;
// // pub type Kyber768PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_1024>;
// impl_types!(Kyber768SharedSecret, SHARED_SECRET_SIZE);

// impl_types!(Kyber1024Ciphertext, CPA_PKE_CIPHERTEXT_SIZE_1024);
// // pub type Kyber1024PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_1024>;
// // pub type Kyber1024PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_1024>;
// impl_types!(Kyber1024SharedSecret, SHARED_SECRET_SIZE);

/// A Kyber CPA key pair
pub struct CcaKeyPair<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize> {
    pub(super) sk: KyberPrivateKey<PRIVATE_KEY_SIZE>,
    pub(super) pk: ind_cpa::PublicKey<PUBLIC_KEY_SIZE>,
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
        pk: ind_cpa::PublicKey<PUBLIC_KEY_SIZE>,
    ) -> Self {
        Self { sk, pk }
    }

    pub fn pk(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        self.pk.as_slice()
    }

    pub fn sk(&self) -> &[u8; PRIVATE_KEY_SIZE] {
        self.sk.as_slice()
    }
}

pub type CcaKeyPair512 = CcaKeyPair<CPA_PKE_SECRET_KEY_SIZE_512, CPA_PKE_PUBLIC_KEY_SIZE_512>;
pub type CcaKeyPair768 = CcaKeyPair<CPA_PKE_SECRET_KEY_SIZE_768, CPA_PKE_PUBLIC_KEY_SIZE_768>;
pub type CcaKeyPair1024 = CcaKeyPair<CPA_PKE_SECRET_KEY_SIZE_1024, CPA_PKE_PUBLIC_KEY_SIZE_1024>;

/// A Kyber key pair
pub enum KyberKeyPair {
    Kyber512(
        KyberPrivateKey<CPA_PKE_SECRET_KEY_SIZE_512>,
        ind_cpa::PublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>,
    ),
    Kyber768(
        KyberPrivateKey<CPA_PKE_SECRET_KEY_SIZE_768>,
        ind_cpa::PublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>,
    ),
    Kyber1024(
        KyberPrivateKey<CPA_PKE_SECRET_KEY_SIZE_1024>,
        ind_cpa::PublicKey<CPA_PKE_PUBLIC_KEY_SIZE_1024>,
    ),
}

impl KyberKeyPair {
    pub fn pk(&self) -> &[u8] {
        match self {
            KyberKeyPair::Kyber512(_, pk) => pk.as_ref(),
            KyberKeyPair::Kyber768(_, pk) => pk.as_ref(),
            KyberKeyPair::Kyber1024(_, pk) => pk.as_ref(),
        }
    }

    pub fn sk(&self) -> &[u8] {
        match self {
            KyberKeyPair::Kyber512(sk, _) => sk.as_ref(),
            KyberKeyPair::Kyber768(sk, _) => sk.as_ref(),
            KyberKeyPair::Kyber1024(sk, _) => sk.as_ref(),
        }
    }
}

// impl From<()>

// pub struct Ciphersuite {
//     public_key_size: usize,
//     private_key_size: usize,
// }

// pub const KYBER512: Ciphersuite = Ciphersuite {
//     public_key_size: CPA_PKE_PUBLIC_KEY_SIZE_512,
//     private_key_size: SECRET_KEY_SIZE_512,
// };

// pub fn generate_key_pair_512(
//     randomness: [u8; KEY_GENERATION_SEED_SIZE],
// ) -> Result<CcaKeyPair512, BadRejectionSamplingRandomnessError> {
//     generate_keypair::<SECRET_KEY_SIZE_512, CPA_PKE_PUBLIC_KEY_SIZE_512>(randomness).map(|key| {
//         match key {
//             KyberKeyPair::Kyber512(key) => key,
//             KyberKeyPair::Kyber768(_, _) => unreachable!(),
//             KyberKeyPair::Kyber1024(_, _) => unreachable!(),
//         }
//     })
// }

pub fn generate_keypair<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<CcaKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>, BadRejectionSamplingRandomnessError> {
    let ind_cpa_keypair_randomness = &randomness[0..parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let (ind_cpa_private_key, public_key) =
        ind_cpa::generate_keypair::<RANK_768, PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>(
            ind_cpa_keypair_randomness,
        )?;

    let secret_key_serialized = serialize_secret_key(
        ind_cpa_private_key.as_slice(),
        public_key.as_slice(),
        implicit_rejection_value,
    );
    let private_key: KyberPrivateKey<PRIVATE_KEY_SIZE> =
        KyberPrivateKey::from(secret_key_serialized);

    Ok(CcaKeyPair::from(private_key, public_key))
}

pub fn encapsulate<
    const SHARED_SECRET_SIZE: usize,
    const CIPHERTEXT_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
>(
    public_key: &ind_cpa::PublicKey<PUBLIC_KEY_SIZE>,
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

    let ciphertext =
        ind_cpa::encrypt::<RANK_768>(public_key.as_slice(), randomness_hashed, pseudorandomness)?;

    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&k_not);
    to_hash[H_DIGEST_SIZE..].copy_from_slice(&H(ciphertext.as_ref()));

    let shared_secret = KDF(&to_hash).into();

    // let ciphertext = if let CiphertextCpa::Kyber768(b) = ciphertext {
    //     b
    // } else {
    //     unimplemented!()
    // };
    Ok((ciphertext, shared_secret))
}

pub fn decapsulate(
    secret_key: &Kyber768PrivateKey,
    ciphertext: &Kyber768Ciphertext,
) -> Kyber768SharedSecret {
    let (ind_cpa_secret_key, secret_key) = secret_key.split_at(CPA_PKE_SECRET_KEY_SIZE_768);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(CPA_PKE_PUBLIC_KEY_SIZE_768);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let ciphertext = CiphertextCpa::Kyber768(ciphertext);
    let decrypted = ind_cpa::decrypt::<RANK_768>(ind_cpa_secret_key, &ciphertext);

    let mut to_hash: [u8; CPA_PKE_MESSAGE_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
    to_hash[CPA_PKE_MESSAGE_SIZE..].copy_from_slice(ind_cpa_public_key_hash);

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let expected_ciphertext_result =
        ind_cpa::encrypt::<RANK_768>(ind_cpa_public_key, decrypted, pseudorandomness);

    // Since we decrypt the ciphertext and hash this decrypted value in
    // to obtain the pseudorandomness, it is in theory possible that a modified
    // ciphertext could result in a set of pseudorandom bytes that are insufficient
    // to rejection-sample the ring elements we need.
    //
    // In that case, the 'else' branch of this if-else block will be taken; notice
    // that it performs less operations than the 'if' branch. The resulting timing
    // difference would let an observer know that implicit rejection has taken
    // place. We do not think this poses a security issue since such information
    // would be conveyed anyway at a higher level (e.g. a key-exchange protocol
    // would no longer proceed).
    let to_hash = if let Ok(expected_ciphertext) = expected_ciphertext_result {
        let selector =
            compare_ciphertexts_in_constant_time(ciphertext.as_ref(), expected_ciphertext.as_ref());
        select_shared_secret_in_constant_time(k_not, implicit_rejection_value, selector)
    } else {
        let mut out = [0u8; 32];
        out[..].copy_from_slice(implicit_rejection_value);
        out
    };

    let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&to_hash);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(&H(ciphertext.as_ref()));

    KDF(&to_hash)
}
