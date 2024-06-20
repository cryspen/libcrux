//! # Key Encapsulation Mechanism
//!
//! A KEM interface.
//!
//! For ECDH structs, check the [`ecdh`] module.
//!
//! Available algorithms:
//! * [`Algorithm::X25519`]\: x25519 ECDH KEM. Also see [`ecdh#x25519`].
//! * [`Algorithm::Secp256r1`]\: NIST P256 ECDH KEM. Also see [`ecdh#P256`].
//! * [`Algorithm::MlKem512`]\: ML-KEM 512 from [FIPS 203].
//! * [`Algorithm::MlKem768`]\: ML-KEM 768 from [FIPS 203].
//! * [`Algorithm::MlKem1024`]\: ML-KEM 1024 from [FIPS 203].
//! * [`Algorithm::X25519MlKem768Draft00`]\: Hybrid x25519 - ML-KEM 768 [draft kem for hpke](https://www.ietf.org/archive/id/draft-westerbaan-cfrg-hpke-xyber768d00-00.html).
//! * [`Algorithm::XWingKemDraft02`]\: Hybrid x25519 - ML-KEM 768 [draft xwing kem for hpke](https://www.ietf.org/archive/id/draft-connolly-cfrg-xwing-kem-02.html).
//!
//! ```
//! use libcrux::{kem::*, drbg::Drbg, digest::Algorithm::Sha256};
//!
//! let mut rng = Drbg::new(Sha256).unwrap();
//! let (sk_a, pk_a) = key_gen(Algorithm::MlKem768, &mut rng).unwrap();
//! let received_pk = pk_a.encode();
//!
//! let pk = PublicKey::decode(Algorithm::MlKem768, &received_pk).unwrap();
//! let (ss_b, ct_b) = pk.encapsulate(&mut rng).unwrap();
//! let received_ct = ct_b.encode();
//!
//! let ct_a = Ct::decode(Algorithm::MlKem768, &received_ct).unwrap();
//! let ss_a = ct_a.decapsulate(&sk_a).unwrap();
//! assert_eq!(ss_b.encode(), ss_a.encode());
//! ```
//!
//! [FIPS 203]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.ipd.pdf

// hacspec code: don't let clippy touch it.
#[allow(clippy::all)]
pub mod kyber;

// TODO: These functions are currently exposed simply in order to make NIST KAT
// testing possible without an implementation of the NIST AES-CTR DRBG. Remove them
// (and change the visibility of the exported functions to pub(crate)) the
// moment we have an implementation of one. This is tracked by:
// https://github.com/cryspen/libcrux/issues/36
#[cfg(feature = "tests")]
pub mod deterministic {
    pub use super::kyber::kyber1024::decapsulate as kyber1024_decapsulate_derand;
    pub use super::kyber::kyber1024::encapsulate as kyber1024_encapsulate_derand;
    pub use super::kyber::kyber1024::generate_key_pair as kyber1024_generate_keypair_derand;
    pub use super::kyber::kyber512::decapsulate as kyber512_decapsulate_derand;
    pub use super::kyber::kyber512::encapsulate as kyber512_encapsulate_derand;
    pub use super::kyber::kyber512::generate_key_pair as kyber512_generate_keypair_derand;
    pub use super::kyber::kyber768::decapsulate as kyber768_decapsulate_derand;
    pub use super::kyber::kyber768::encapsulate as kyber768_encapsulate_derand;
    pub use super::kyber::kyber768::generate_key_pair as kyber768_generate_keypair_derand;
}

use self::kyber::MlKemSharedSecret;
use self::kyber::{kyber1024, kyber512, kyber768};
pub use kyber::{
    kyber1024::{MlKem1024Ciphertext, MlKem1024PrivateKey, MlKem1024PublicKey},
    kyber512::{MlKem512Ciphertext, MlKem512PrivateKey, MlKem512PublicKey},
    kyber768::{MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey},
    MlKemCiphertext, MlKemKeyPair,
};

#[cfg(feature = "tests")]
pub use kyber::{
    kyber1024::validate_public_key as ml_kem1024_validate_public_key,
    kyber512::validate_public_key as ml_kem512_validate_public_key,
    kyber768::validate_public_key as ml_kem768_validate_public_key,
};
