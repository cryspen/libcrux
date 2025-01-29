use core::array::from_fn;

use ind_cpa::unpacked::IndCpaPublicKeyUnpacked;

use super::*;
use crate::{
    ind_cca::unpacked::MlKemKeyPairUnpacked,
    polynomial::{vec_from_bytes, vec_to_bytes},
};

/// Errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// Invalid input byte length
    InvalidInputLength,

    /// Invalid output byte length
    InvalidOutputLength,
}

/// Incremental trait for unpacked key pairs.
//<const K: usize, Vector: Operations>
pub trait IncrementalKeyPair {
    /// Get the [`PublicKey1`] from this key pair as bytes.
    ///
    /// The output `bytes` have to be at least 64 bytes long.
    ///
    /// **PANICS:** if the output `bytes` are too short.
    fn pk1_bytes(&self, bytes: &mut [u8]);

    /// Get the [`PublicKey2`] from this key pair as bytes.
    ///
    /// The output `bytes` have to be at least K * 16 * 32 bytes long.
    ///
    /// **PANICS:** if the output `bytes` are too short.
    fn pk2_bytes(&self, bytes: &mut [u8]);
}

impl<const K: usize, Vector: Operations> IncrementalKeyPair for MlKemKeyPairUnpacked<K, Vector> {
    fn pk1_bytes(&self, bytes: &mut [u8]) {
        bytes[0..32].copy_from_slice(&self.public_key().ind_cpa_public_key.seed_for_A);
        bytes[32..64].copy_from_slice(&self.public_key().public_key_hash);
    }

    #[allow(unsafe_code)]
    #[hax_lib::requires(bytes.len() >= K * 16 * 32)]
    fn pk2_bytes(&self, bytes: &mut [u8]) {
        vec_to_bytes(&self.public_key.ind_cpa_public_key.t_as_ntt, bytes);
    }
}

/// The incremental public key that allows generating [`Ciphertext1`].
#[derive(Default)]
pub struct PublicKey1 {
    pub(super) seed: [u8; 32],
    pub(super) hash: [u8; 32],
}

impl PublicKey1 {
    /// Get the size of the first public key in bytes.
    pub const fn len() -> usize {
        32 + 32
    }
}

impl TryFrom<&[u8]> for PublicKey1 {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        if value.len() < 64 {
            return Err(Error::InvalidInputLength);
        }

        let mut seed = [0u8; 32];
        seed.copy_from_slice(&value[0..32]);
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&value[32..64]);
        Ok(Self { seed, hash })
    }
}

impl From<&[u8; 64]> for PublicKey1 {
    fn from(value: &[u8; 64]) -> Self {
        let mut seed = [0u8; 32];
        seed.copy_from_slice(&value[0..32]);
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&value[32..64]);
        Self { seed, hash }
    }
}

/// The incremental public key that allows generating [`Ciphertext2`].
#[repr(transparent)]
pub struct PublicKey2<const K: usize, Vector: Operations> {
    pub(super) t_as_ntt: [PolynomialRingElement<Vector>; K],
}

impl<const K: usize, Vector: Operations> PublicKey2<K, Vector> {
    /// Get the size of the second public key in bytes.
    pub const fn len() -> usize {
        vec_len_bytes::<K, Vector>()
    }
}

/// Trait container for multiplexing over platform dependent [`MlKemKeyPairUnpacked`].
pub trait Keys: IncrementalKeyPair {
    fn as_any(&self) -> &dyn Any;
}
impl<const K: usize, Vector: Operations + 'static> Keys for MlKemKeyPairUnpacked<K, Vector> {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// The partial ciphertext c1 - first part.
#[repr(transparent)]
pub struct Ciphertext1<const LEN: usize> {
    pub value: [u8; LEN],
}

impl<const LEN: usize> Ciphertext1<LEN> {
    /// The size of the ciphertext.
    pub const fn len() -> usize {
        LEN
    }
}

/// The partial ciphertext c2 - second part.
#[repr(transparent)]
pub struct Ciphertext2<const LEN: usize> {
    pub value: [u8; LEN],
}

impl<const LEN: usize> Ciphertext2<LEN> {
    /// The size of the ciphertext.
    pub const fn len() -> usize {
        LEN
    }
}

/// The incremental state for encapsulate.
pub struct EncapsState<const K: usize, Vector: Operations> {
    pub(super) shared_secret: MlKemSharedSecret,
    pub(super) r_as_ntt: [PolynomialRingElement<Vector>; K],
    pub(super) error2: PolynomialRingElement<Vector>,
    pub(super) randomness: [u8; 32],
}

impl<const K: usize, Vector: Operations> EncapsState<K, Vector> {
    /// Get the number of bytes, required for the state.
    pub const fn num_bytes() -> usize {
        SHARED_SECRET_SIZE
            + vec_len_bytes::<K, Vector>()
            + PolynomialRingElement::<Vector>::num_bytes()
            + 32
    }

    /// Get the state as bytes
    pub fn to_bytes(self, out: &mut [u8]) -> Result<(), Error> {
        debug_assert!(out.len() >= Self::num_bytes());
        if out.len() < Self::num_bytes() {
            return Err(Error::InvalidOutputLength);
        }

        out[..SHARED_SECRET_SIZE].copy_from_slice(&self.shared_secret);
        let mut offset = SHARED_SECRET_SIZE;

        vec_to_bytes(&self.r_as_ntt, &mut out[offset..]);
        offset += vec_len_bytes::<K, Vector>();

        self.error2.to_bytes(&mut out[offset..]);
        offset += PolynomialRingElement::<Vector>::num_bytes();

        out[offset..offset + 32].copy_from_slice(&self.randomness);

        Ok(())
    }

    /// Build a state from bytes
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        debug_assert!(bytes.len() >= Self::num_bytes());
        if bytes.len() < Self::num_bytes() {
            return Err(Error::InvalidInputLength);
        }

        let mut shared_secret = [0u8; SHARED_SECRET_SIZE];
        shared_secret.copy_from_slice(&bytes[..SHARED_SECRET_SIZE]);
        let mut offset = SHARED_SECRET_SIZE;

        let mut r_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
        vec_from_bytes(&bytes[offset..], &mut r_as_ntt);
        offset += vec_len_bytes::<K, Vector>();

        let error2 = PolynomialRingElement::<Vector>::from_bytes(&bytes[offset..]);
        offset += PolynomialRingElement::<Vector>::num_bytes();

        let mut randomness = [0u8; 32];
        randomness.copy_from_slice(&bytes[offset..offset + 32]);

        Ok(Self {
            shared_secret,
            r_as_ntt,
            error2,
            randomness,
        })
    }
}

/// Trait container for multiplexing over platform dependent [`EncapsState`].
pub trait State {
    fn as_any(&self) -> &dyn Any;

    /// Get the shared secret.
    fn shared_secret(&self) -> &[u8];
}
impl<const K: usize, Vector: Operations + 'static> State for EncapsState<K, Vector> {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn shared_secret(&self) -> &[u8] {
        &self.shared_secret
    }
}

// === Implementations

/// Convert [`MlKemPublicKeyUnpacked`] to a [`PublicKey1`]
impl<const K: usize, Vector: Operations> From<&MlKemPublicKeyUnpacked<K, Vector>> for PublicKey1 {
    fn from(pk: &MlKemPublicKeyUnpacked<K, Vector>) -> Self {
        Self {
            seed: pk.ind_cpa_public_key.seed_for_A,
            hash: pk.public_key_hash,
        }
    }
}

/// Convert [`MlKemPublicKeyUnpacked`] to a [`PublicKey2`].
impl<const K: usize, Vector: Operations> From<&MlKemPublicKeyUnpacked<K, Vector>>
    for PublicKey2<K, Vector>
{
    fn from(pk: &MlKemPublicKeyUnpacked<K, Vector>) -> Self {
        Self {
            t_as_ntt: pk.ind_cpa_public_key.t_as_ntt,
        }
    }
}

/// Convert a byte slice `&[u8]` to a [`PublicKey2`].
impl<const K: usize, Vector: Operations> TryFrom<&[u8]> for PublicKey2<K, Vector> {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        if value.len() < K * 15 * 32 {
            return Err(Error::InvalidInputLength);
        }

        let mut t_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
        vec_from_bytes(value, &mut t_as_ntt);

        Ok(Self { t_as_ntt })
    }
}

// The key pair struct that we (de)serialize.
pub struct KeyPair<const K: usize, Vector: Operations> {
    pk1: PublicKey1,
    pk2: PublicKey2<K, Vector>,
    sk: MlKemPrivateKeyUnpacked<K, Vector>,
    matrix: [[PolynomialRingElement<Vector>; K]; K],
}

impl<const K: usize, Vector: Operations> From<MlKemKeyPairUnpacked<K, Vector>>
    for KeyPair<K, Vector>
{
    fn from(kp: MlKemKeyPairUnpacked<K, Vector>) -> Self {
        KeyPair {
            pk1: PublicKey1::from(kp.public_key()),
            pk2: PublicKey2::from(kp.public_key()),
            sk: kp.private_key,
            matrix: kp.public_key.ind_cpa_public_key.A,
        }
    }
}

impl<const K: usize, Vector: Operations> From<KeyPair<K, Vector>>
    for MlKemKeyPairUnpacked<K, Vector>
{
    fn from(value: KeyPair<K, Vector>) -> Self {
        MlKemKeyPairUnpacked {
            private_key: value.sk,
            public_key: MlKemPublicKeyUnpacked {
                ind_cpa_public_key: IndCpaPublicKeyUnpacked {
                    t_as_ntt: value.pk2.t_as_ntt,
                    seed_for_A: value.pk1.seed,
                    A: value.matrix,
                },
                public_key_hash: value.pk1.hash,
            },
        }
    }
}

impl<const K: usize, Vector: Operations> KeyPair<K, Vector> {
    /// Get [`PublicKey1`] as bytes.
    pub fn pk1_bytes(&self, pk1: &mut [u8]) {
        pk1[0..32].copy_from_slice(&self.pk1.seed);
        pk1[32..64].copy_from_slice(&self.pk1.hash);
    }

    /// Get [`PublicKey2`] as bytes.
    pub fn pk2_bytes(&self, pk2: &mut [u8]) {
        vec_to_bytes(&self.pk2.t_as_ntt, pk2);
    }

    /// The byte size of this key pair.
    pub fn num_bytes() -> usize {
        PublicKey1::len() + PublicKey2::<K, Vector>::len()
        // sk length
        + vec_len_bytes::<K, Vector>() + 32
        // matrix length
        + K * vec_len_bytes::<K, Vector>()
    }

    /// Write this key pair into the `key` bytes.
    ///
    /// `key` must be at least of length `num_bytes()`
    pub fn to_bytes(self, key: &mut [u8]) {
        debug_assert!(key.len() >= Self::num_bytes());

        let mut offset = 0;

        #[inline(always)]
        fn write(out: &mut [u8], value: &[u8], offset: &mut usize) {
            let new_offset = *offset + value.len();
            out[*offset..new_offset].copy_from_slice(value);
            *offset = new_offset;
        }

        // PK1
        write(key, &self.pk1.seed, &mut offset);
        write(key, &self.pk1.hash, &mut offset);

        // PK2
        vec_to_bytes(&self.pk2.t_as_ntt, &mut key[offset..]);
        offset += vec_len_bytes::<K, Vector>();

        // SK
        vec_to_bytes(
            &self.sk.ind_cpa_private_key.secret_as_ntt,
            &mut key[offset..],
        );
        offset += vec_len_bytes::<K, Vector>();
        write(key, &self.sk.implicit_rejection_value, &mut offset);

        // Matrix
        for i in 0..self.matrix.len() {
            vec_to_bytes(&self.matrix[i], &mut key[offset..]);
            offset += vec_len_bytes::<K, Vector>();
        }
    }

    /// Read a key pair from the `key` bytes.
    ///
    /// `key` must be at least of length `num_bytes()`
    pub fn from_bytes(key: &[u8]) -> Result<Self, Error> {
        debug_assert!(key.len() >= Self::num_bytes());
        if key.len() < Self::num_bytes() {
            return Err(Error::InvalidInputLength);
        }

        // PK1
        let pk1 = PublicKey1::try_from(key).unwrap();
        let mut offset = PublicKey1::len();

        // PK2
        let pk2 = PublicKey2::try_from(&key[offset..]).unwrap();
        offset += PublicKey2::<K, Vector>::len();

        // SK
        let implicit_rejection_value = [0u8; 32];
        let mut sk: MlKemPrivateKeyUnpacked<K, Vector> = MlKemPrivateKeyUnpacked {
            ind_cpa_private_key: IndCpaPrivateKeyUnpacked::default(),
            implicit_rejection_value,
        };
        vec_from_bytes(&key[offset..], &mut sk.ind_cpa_private_key.secret_as_ntt);
        offset += vec_len_bytes::<K, Vector>();
        sk.implicit_rejection_value
            .copy_from_slice(&key[offset..offset + 32]);
        offset += sk.implicit_rejection_value.len();

        // Matrix
        let mut matrix = [[PolynomialRingElement::<Vector>::ZERO(); K]; K];
        for i in 0..matrix.len() {
            vec_from_bytes(&key[offset..], &mut matrix[i]);
            offset += vec_len_bytes::<K, Vector>();
        }

        Ok(Self {
            pk1,
            pk2,
            sk,
            matrix,
        })
    }
}
