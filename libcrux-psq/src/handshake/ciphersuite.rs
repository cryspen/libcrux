pub mod builder;
pub mod initiator;
pub mod responder;
pub mod traits;
pub mod types;

#[derive(Clone, Copy, Debug)]
/// Available ciphersuites for use in the PSQ handshake.
pub enum CiphersuiteName {
    /// Use X25519 for the outer KEM, no inner KEM, Chacha20Poly1305 as payload AEAD and SHA-256 for HKDF.
    X25519ChachaPolyHkdfSha256,
    /// Use X25519 for the outer KEM, ML-KEM 768 for the inner KEM, Chacha20Poly1305 as payload AEAD and SHA-256 for HKDF.
    X25519Mlkem768ChachaPolyHkdfSha256,
    /// Use X25519 for the outer KEM, Classic McEliece for the inner KEM, Chacha20Poly1305 as payload AEAD and SHA-256 for HKDF. (requires feature `classic-mceliece`)
    X25519ClassicMcElieceChachaPolyHkdfSha256,
}
