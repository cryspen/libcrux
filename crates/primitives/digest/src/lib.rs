#[cfg(any(feature = "sha2", feature = "sha3", feature = "blake2"))]
pub use libcrux_traits::digest::Hasher;

#[cfg(feature = "blake2")]
pub mod blake2 {
    pub use libcrux_blake2::{Blake2bHash, Blake2bHasher, Blake2sHash, Blake2sHasher};
}

#[cfg(feature = "sha2")]
pub mod sha2 {
    pub use libcrux_sha2::{
        Sha224Hash as Sha2_224Hash, Sha224Hasher as Sha2_224Hasher, Sha256Hash as Sha2_256Hash,
        Sha256Hasher as Sha2_256Hasher, Sha384Hash as Sha2_384Hash, Sha384Hasher as Sha2_384Hasher,
        Sha512Hash as Sha2_512Hash, Sha512Hasher as Sha2_512Hasher,
    };
}

#[cfg(feature = "sha3")]
pub mod sha3 {

    pub use libcrux_sha3::{
        Sha3_224, Sha3_224Hasher, Sha3_256, Sha3_256Hasher, Sha3_384, Sha3_384Hasher, Sha3_512,
        Sha3_512Hasher,
    };
}
