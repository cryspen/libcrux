// hacspec code: don't let clippy touch it.
#[allow(clippy::all)]
pub mod kyber;

// // TODO: These functions are currently exposed simply in order to make NIST KAT
// // testing possible without an implementation of the NIST AES-CTR DRBG. Remove them
// // (and change the visibility of the exported functions to pub(crate)) the
// // moment we have an implementation of one. This is tracked by:
// // https://github.com/cryspen/libcrux/issues/36
// #[cfg(feature = "tests")]
// pub mod deterministic {
//     pub use super::kyber::kyber1024::decapsulate as kyber1024_decapsulate_derand;
//     pub use super::kyber::kyber1024::encapsulate as kyber1024_encapsulate_derand;
//     pub use super::kyber::kyber1024::generate_key_pair as kyber1024_generate_keypair_derand;
//     pub use super::kyber::kyber512::decapsulate as kyber512_decapsulate_derand;
//     pub use super::kyber::kyber512::encapsulate as kyber512_encapsulate_derand;
//     pub use super::kyber::kyber512::generate_key_pair as kyber512_generate_keypair_derand;
//     pub use super::kyber::kyber768::decapsulate as kyber768_decapsulate_derand;
//     pub use super::kyber::kyber768::encapsulate as kyber768_encapsulate_derand;
//     pub use super::kyber::kyber768::generate_key_pair as kyber768_generate_keypair_derand;
// }

// #[cfg(feature = "tests")]
// pub use kyber::{
//     kyber1024::validate_public_key as ml_kem1024_validate_public_key,
//     kyber512::validate_public_key as ml_kem512_validate_public_key,
//     kyber768::validate_public_key as ml_kem768_validate_public_key,
// };
