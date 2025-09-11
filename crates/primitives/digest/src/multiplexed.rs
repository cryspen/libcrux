use libcrux_traits::digest::typed_refs::{DigestMut, Hash, HashError, MultiplexesHash};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum HashAlgorithm {
    // Sha2 variants
    #[cfg(feature = "sha2")]
    Sha2_224,
    #[cfg(feature = "sha2")]
    Sha2_256,
    #[cfg(feature = "sha2")]
    Sha2_384,
    #[cfg(feature = "sha2")]
    Sha2_512,

    // Sha3 variants
    #[cfg(feature = "sha3")]
    Sha3_224,
    #[cfg(feature = "sha3")]
    Sha3_256,
    #[cfg(feature = "sha3")]
    Sha3_384,
    #[cfg(feature = "sha3")]
    Sha3_512,

    // Blake2 variants
    #[cfg(feature = "blake2")]
    Blake2b,
    #[cfg(feature = "blake2")]
    Blake2s,
}

impl Hash for HashAlgorithm {
    fn digest_len_is_valid(&self, len: usize) -> bool {
        match *self {
            // Sha2 variants
            #[cfg(feature = "sha2")]
            HashAlgorithm::Sha2_224 => crate::sha2::Sha2_224.digest_len_is_valid(len),
            #[cfg(feature = "sha2")]
            HashAlgorithm::Sha2_256 => crate::sha2::Sha2_256.digest_len_is_valid(len),
            #[cfg(feature = "sha2")]
            HashAlgorithm::Sha2_384 => crate::sha2::Sha2_384.digest_len_is_valid(len),
            #[cfg(feature = "sha2")]
            HashAlgorithm::Sha2_512 => crate::sha2::Sha2_512.digest_len_is_valid(len),

            // Sha3 variants
            #[cfg(feature = "sha3")]
            HashAlgorithm::Sha3_224 => crate::sha3::Sha3_224.digest_len_is_valid(len),
            #[cfg(feature = "sha3")]
            HashAlgorithm::Sha3_256 => crate::sha3::Sha3_256.digest_len_is_valid(len),
            #[cfg(feature = "sha3")]
            HashAlgorithm::Sha3_384 => crate::sha3::Sha3_384.digest_len_is_valid(len),
            #[cfg(feature = "sha3")]
            HashAlgorithm::Sha3_512 => crate::sha3::Sha3_512.digest_len_is_valid(len),

            // Blake2 variants
            #[cfg(feature = "blake2")]
            HashAlgorithm::Blake2b => {
                crate::blake2::Blake2b::<crate::blake2::RuntimeDigestLen>::default()
                    .digest_len_is_valid(len)
            }
            #[cfg(feature = "blake2")]
            HashAlgorithm::Blake2s => {
                crate::blake2::Blake2s::<crate::blake2::RuntimeDigestLen>::default()
                    .digest_len_is_valid(len)
            }
        }
    }
    fn hash<'a>(&self, digest: DigestMut<'a, Self>, payload: &[u8]) -> Result<(), HashError> {
        match self {
            // Sha2 variants
            #[cfg(feature = "sha2")]
            HashAlgorithm::Sha2_224 => {
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;

                crate::sha2::Sha2_224.hash(digest, payload)
            }
            #[cfg(feature = "sha2")]
            HashAlgorithm::Sha2_256 => {
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;

                crate::sha2::Sha2_256.hash(digest, payload)
            }
            #[cfg(feature = "sha2")]
            HashAlgorithm::Sha2_384 => {
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;

                crate::sha2::Sha2_384.hash(digest, payload)
            }
            #[cfg(feature = "sha2")]
            HashAlgorithm::Sha2_512 => {
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;

                crate::sha2::Sha2_512.hash(digest, payload)
            }

            // Sha3 variants
            #[cfg(feature = "sha3")]
            HashAlgorithm::Sha3_224 => {
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;

                crate::sha3::Sha3_224.hash(digest, payload)
            }
            #[cfg(feature = "sha3")]
            HashAlgorithm::Sha3_256 => {
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;

                crate::sha3::Sha3_256.hash(digest, payload)
            }
            #[cfg(feature = "sha3")]
            HashAlgorithm::Sha3_384 => {
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;

                crate::sha3::Sha3_384.hash(digest, payload)
            }
            #[cfg(feature = "sha3")]
            HashAlgorithm::Sha3_512 => {
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;

                crate::sha3::Sha3_512.hash(digest, payload)
            }
            // Blake2 variants
            #[cfg(feature = "blake2")]
            HashAlgorithm::Blake2b => {
                use crate::blake2::*;
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;
                Blake2b::<RuntimeDigestLen>::default().hash(digest, payload)
            }
            #[cfg(feature = "blake2")]
            HashAlgorithm::Blake2s => {
                use crate::blake2::*;
                let digest = Self::mux_digest(digest).ok_or(HashError::WrongDigest)?;
                Blake2s::<RuntimeDigestLen>::default().hash(digest, payload)
            }
        }
    }
}
macro_rules! impl_mux {
    ($module:ident, $algo:ident) => {
        impl_mux!($module, $algo, $algo);
    };
    ($module:ident, $algo:ident, $type:ty) => {
        impl MultiplexesHash<$type> for HashAlgorithm {
            fn mux_algo(&self) -> Option<$type> {
                Some(<$type>::default())
            }

            fn wrap_algo(_algo: $type) -> Self {
                Self::$algo
            }
        }
    };
}

#[cfg(feature = "sha2")]
mod sha2_impl {
    use super::*;
    use crate::sha2::*;
    impl_mux!(sha2, Sha2_224);
    impl_mux!(sha2, Sha2_256);
    impl_mux!(sha2, Sha2_384);
    impl_mux!(sha2, Sha2_512);
}

#[cfg(feature = "blake2")]
mod blake2_impl {
    use super::*;
    use crate::blake2::*;
    impl_mux!(blake2, Blake2b, Blake2b<RuntimeDigestLen>);
    impl_mux!(blake2, Blake2s, Blake2s<RuntimeDigestLen>);
}

#[cfg(feature = "sha3")]
mod sha3_impl {
    use super::*;
    use crate::sha3::*;
    impl_mux!(sha3, Sha3_224);
    impl_mux!(sha3, Sha3_256);
    impl_mux!(sha3, Sha3_384);
    impl_mux!(sha3, Sha3_512);
}
