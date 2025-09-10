#[cfg(feature = "blake2")]
pub mod blake2 {

    pub use libcrux_blake2::{Blake2bHasher, Blake2sHasher};
}

#[cfg(feature = "sha2")]
pub mod sha2 {

    pub use libcrux_sha2::{
        Sha224Hasher as Sha2_224Hasher, Sha256Hasher as Sha2_256Hasher,
        Sha384Hasher as Sha2_384Hasher, Sha512Hasher as Sha2_512Hasher,
    };
}

#[cfg(feature = "sha3")]
pub mod sha3 {

    pub use libcrux_sha3::{Sha3_224Hasher, Sha3_256Hasher, Sha3_384Hasher, Sha3_512Hasher};
}
