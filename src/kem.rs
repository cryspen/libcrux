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

pub use libcrux_ml_kem::{
    mlkem1024::{MlKem1024Ciphertext, MlKem1024PrivateKey, MlKem1024PublicKey},
    mlkem512::{MlKem512Ciphertext, MlKem512PrivateKey, MlKem512PublicKey},
    mlkem768::{MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey},
    MlKemCiphertext, MlKemKeyPair,
};

pub use libcrux_kem::Algorithm;
pub use libcrux_kem::Error;

pub use libcrux_kem::X25519MlKem768Draft00PrivateKey;

pub use libcrux_kem::XWingKemDraft02PrivateKey;

pub use libcrux_kem::PrivateKey;

pub use libcrux_kem::X25519MlKem768Draft00PublicKey;

pub use libcrux_kem::XWingKemDraft02PublicKey;

pub use libcrux_kem::PublicKey;

pub use libcrux_kem::Ct;

pub use libcrux_kem::Ss;

pub use libcrux_kem::secret_to_public;

pub use libcrux_kem::key_gen;
