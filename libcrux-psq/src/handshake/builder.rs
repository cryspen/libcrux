// use rand::CryptoRng;

// use crate::ciphersuites::{
//     Ciphersuite, CiphersuiteTrait, X25519ChachaPolyHkdfSha256, X25519Mlkem768ChachaPolyHkdfSha256,
// };

// use super::{
//     dhkem::{DHKeyPair, DHPublicKey},
//     initiator::{query::QueryInitiator, registration::RegistrationInitiator},
//     pqkem::{PQKeyPair, PQPublicKey},
//     responder::Responder,
//     HandshakeError as Error,
// };

// pub struct Builder<'a, Rng: CryptoRng> {
//     rng: Rng,
//     context: &'a [u8],
//     inner_aad: &'a [u8],
//     outer_aad: &'a [u8],
//     longterm_ecdh_keys: Option<&'a DHKeyPair>,
//     longterm_pq_keys: Option<&'a Ciphersuite::PQKeypair>,
//     peer_longterm_ecdh_pk: Option<&'a DHPublicKey>,
//     peer_longterm_pq_pk: Option<&'a Ciphersuite::PQEncapsKey>,
//     recent_keys_upper_bound: Option<usize>,
//     ciphersuite: Box<dyn CiphersuiteTrait>,
// }

// // pub fn builder<'a, Rng: CryptoRng>(
// //     ciphersuite: Ciphersuite,
// //     rng: Rng,
// // ) -> Builder<'a, Rng, impl CiphersuiteTrait> {
// //     match ciphersuite {
// //         Ciphersuite::QueryCiphersuite(query_ciphersuite) => match query_ciphersuite {
// //             crate::ciphersuites::QueryCiphersuite::X25519ChachaPolyHkdfSha256(x25519_chacha_poly_hkdf_sha256) => Builder::<Rng, X25519ChachaPolyHkdfSha256>::new(rng),
// //             crate::ciphersuites::QueryCiphersuite::X25519ChachaPolyHkdfSha256Mldsa65 => todo!(),
// //         },
// //         Ciphersuite::RegistrationCiphersuite(registration_ciphersuite) => match registration_ciphersuite {
// //             crate::ciphersuites::RegistrationCiphersuite::X25519Mlkem768ChachaPolyHkdfSha256(x25519_mlkem768_chacha_poly_hkdf_sha256) => Builder::<Rng, X25519Mlkem768ChachaPolyHkdfSha256>::new(rng),
// //             crate::ciphersuites::RegistrationCiphersuite::X25519McElieceChachaPolyHkdfSha256(x25519_mc_eliece_chacha_poly_hkdf_sha256) => Builder::<Rng, X25519Mlkem768ChachaPolyHkdfSha256>::new(rng),
// //             crate::ciphersuites::RegistrationCiphersuite::X25519Mlkem768ChachaPolyHkdfSha256Mldsa65 => todo!(),
// //             crate::ciphersuites::RegistrationCiphersuite::X25519McElieceChachaPolyHkdfSha256Mldsa65 => todo!(),
// //         },
// //     }
// // }

// impl<'a, Rng: CryptoRng, Ciphersuite: CiphersuiteTrait> Builder<'a, Rng, Ciphersuite> {
//     /// Create a new builder.
//     pub fn new(rng: Rng) -> Self {
//         Self {
//             rng,
//             context: &[],
//             inner_aad: &[],
//             outer_aad: &[],
//             longterm_ecdh_keys: None,
//             longterm_pq_keys: None,
//             peer_longterm_ecdh_pk: None,
//             peer_longterm_pq_pk: None,
//             recent_keys_upper_bound: None,
//         }
//     }

//     // properties

//     /// Set the context.
//     pub fn context(mut self, context: &'a [u8]) -> Self {
//         self.context = context;
//         self
//     }

//     /// Set the inner AAD.
//     pub fn inner_aad(mut self, inner_aad: &'a [u8]) -> Self {
//         self.inner_aad = inner_aad;
//         self
//     }

//     /// Set the outer AAD.
//     pub fn outer_aad(mut self, outer_aad: &'a [u8]) -> Self {
//         self.outer_aad = outer_aad;
//         self
//     }

//     /// Set the long-term ECDH key pair.
//     pub fn longterm_ecdh_keys(mut self, longterm_ecdh_keys: &'a DHKeyPair) -> Self {
//         // XXX: We don't have anything in the key to check if it's correct for
//         //      this ciphersuite.
//         self.longterm_ecdh_keys = Some(longterm_ecdh_keys);
//         self
//     }

//     /// Set the long-term PQ key pair.
//     pub fn longterm_pq_keys(mut self, longterm_pq_keys: &'a Ciphersuite::PQKeypair) -> Self {
//         self.longterm_pq_keys = Some(longterm_pq_keys);
//         self
//     }

//     /// Set the peer's long-term ECDH public key.
//     pub fn peer_longterm_ecdh_pk(mut self, peer_longterm_ecdh_pk: &'a DHPublicKey) -> Self {
//         self.peer_longterm_ecdh_pk = Some(peer_longterm_ecdh_pk);
//         self
//     }

//     /// Set the peer's long-term PQ public key.
//     pub fn peer_longterm_pq_pk(
//         mut self,
//         peer_longterm_pq_pk: &'a Ciphersuite::PQEncapsKey,
//     ) -> Self {
//         self.peer_longterm_pq_pk = Some(peer_longterm_pq_pk);
//         self
//     }

//     /// Set the maximum number of recent keys stored for DoS protection.
//     pub fn recent_keys_upper_bound(mut self, recent_keys_upper_bound: usize) -> Self {
//         self.recent_keys_upper_bound = Some(recent_keys_upper_bound);
//         self
//     }

//     // builders

//     /// Build a new [`QueryInitiator`].
//     ///
//     /// This requires that a `responder_ecdh_pk` is set.
//     /// It also uses the `context` and `outer_aad`.
//     pub fn build_query_initiator(self) -> Result<QueryInitiator<'a>, Error> {
//         debug_assert!(Ciphersuite::query());
//         if !Ciphersuite::query() {
//             return Err(Error::BuilderState);
//         }

//         let Some(responder_ecdh_pk) = self.peer_longterm_ecdh_pk else {
//             return Err(Error::BuilderState);
//         };

//         QueryInitiator::new(responder_ecdh_pk, self.context, self.outer_aad, self.rng)
//     }

//     /// Build a new [`RegistrationInitiator`].
//     ///
//     /// This requires that a `longterm_ecdh_keys` and a `peer_longterm_ecdh_pk`
//     /// is set.
//     /// It also uses the `context`, `inner_aad`, `outer_aad`, and
//     /// `peer_longterm_pq_pk`.
//     pub fn build_registration_initiator(self) -> Result<RegistrationInitiator<'a, Rng>, Error> {
//         debug_assert!(Ciphersuite::registration());
//         if !Ciphersuite::registration() {
//             return Err(Error::BuilderState);
//         }

//         let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
//             return Err(Error::BuilderState);
//         };

//         let Some(peer_longterm_ecdh_pk) = self.peer_longterm_ecdh_pk else {
//             return Err(Error::BuilderState);
//         };

//         RegistrationInitiator::new(
//             longterm_ecdh_keys,
//             peer_longterm_ecdh_pk,
//             self.peer_longterm_pq_pk.map(Ciphersuite::pq_encaps_key),
//             self.context,
//             self.inner_aad,
//             self.outer_aad,
//             self.rng,
//         )
//     }

//     /// Build a new [`Responder`].
//     ///
//     /// This requires that a `longterm_ecdh_keys`, and `recent_keys_upper_bound` is set.
//     /// It also uses the `context`, `outer_aad`, and `longterm_pq_keys`.
//     pub fn build_responder(self) -> Result<Responder<'a, Rng>, Error> {
//         let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
//             return Err(Error::BuilderState);
//         };

//         let Some(recent_keys_upper_bound) = self.recent_keys_upper_bound else {
//             return Err(Error::BuilderState);
//         };

//         Ok(Responder::new(
//             longterm_ecdh_keys,
//             self.longterm_pq_keys.map(Ciphersuite::pq_keypair),
//             self.context,
//             self.outer_aad,
//             recent_keys_upper_bound,
//             self.rng,
//         ))
//     }
// }
