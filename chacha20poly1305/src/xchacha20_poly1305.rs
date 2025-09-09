//! Non-standard XChacha implementation
//! https://datatracker.ietf.org/doc/html/draft-arciszewski-xchacha-03
//!
//! **NOTE:** This part of the code has not been formally verified yet.

use crate::{
    hacl::chacha20::{chacha20_constants, rounds},
    AeadError,
};
use libcrux_traits::aead::{typed_owned, typed_refs};

pub use crate::{KEY_LEN, TAG_LEN};

pub use crate::impl_aead_trait::XChaCha20Poly1305;

/// An owned XChaCha20Poly1305 key.
pub type Key = typed_owned::Key<XChaCha20Poly1305>;
/// An owned XChaCha20Poly1305 tag.
pub type Tag = typed_owned::Tag<XChaCha20Poly1305>;
/// An owned XChaCha20Poly1305 nonce.
pub type Nonce = typed_owned::Nonce<XChaCha20Poly1305>;

/// A reference to a XChaCha20Poly1305 key.
pub type KeyRef<'a> = typed_refs::KeyRef<'a, XChaCha20Poly1305>;
/// A reference to a XChaCha20Poly1305 tag.
pub type TagRef<'a> = typed_refs::TagRef<'a, XChaCha20Poly1305>;
/// A mutable reference to a XChaCha20Poly1305 tag.
pub type TagMut<'a> = typed_refs::TagMut<'a, XChaCha20Poly1305>;
/// A reference to a XChaCha20Poly1305 nonce.
pub type NonceRef<'a> = typed_refs::NonceRef<'a, XChaCha20Poly1305>;

/// Length of the XChaCha nonce.
pub const NONCE_LEN: usize = 24;

/// XChacha20Poly1305 encrypt: Writes the concatenation of the ciphertext
/// produced by ChaCha20 and the MAC tag into `ctxt` and returns the two pieces
/// separately.
pub fn encrypt<'a>(
    key: &[u8; KEY_LEN],
    ptxt: &[u8],
    ctxt: &'a mut [u8],
    aad: &[u8],
    nonce: &[u8; NONCE_LEN],
) -> Result<(&'a [u8], &'a [u8; TAG_LEN]), AeadError> {
    let mut subkey = [0u8; KEY_LEN];
    let mut new_nonce = [0u8; super::NONCE_LEN];

    derive(key, nonce, &mut subkey, &mut new_nonce);
    super::encrypt(&subkey, ptxt, ctxt, aad, &new_nonce)
}

/// XChacha20Poly1305 decrypt: Writes the result of the decryption to `ptxt`,
/// and returns the slice of appropriate length.
pub fn decrypt<'a>(
    key: &[u8; KEY_LEN],
    ptxt: &'a mut [u8],
    ctxt: &[u8],
    aad: &[u8],
    nonce: &[u8; NONCE_LEN],
) -> Result<&'a [u8], AeadError> {
    let mut subkey = [0u8; KEY_LEN];
    let mut new_nonce = [0u8; super::NONCE_LEN];

    derive(key, nonce, &mut subkey, &mut new_nonce);
    super::decrypt(&subkey, ptxt, ctxt, aad, &new_nonce)
}

/// Derive the nonce and subkey
#[inline(always)]
pub(crate) fn derive(
    key_in: &[u8; KEY_LEN],
    nonce_in: &[u8; NONCE_LEN],
    key_out: &mut [u8; KEY_LEN],
    nonce_out: &mut [u8; 12],
) {
    let (nonce_16, nonce_8) = nonce_in.split_at(16);
    let nonce_16: &[u8; 16] = nonce_16.try_into().unwrap();

    hchacha20(key_in, nonce_16, key_out);
    nonce_out[4..].copy_from_slice(nonce_8);
}

/// Convert the `key` and `nonce` into the subkey.
fn hchacha20(key: &[u8; 32], nonce: &[u8; 16], out: &mut [u8; 32]) {
    // Set up the state
    let mut state = [0u32; 16];
    state[..4].copy_from_slice(&chacha20_constants);

    for (i, k) in key.chunks_exact(4).enumerate() {
        state[4 + i] |=
            k[0] as u32 | (k[1] as u32) << 8 | (k[2] as u32) << 16 | (k[3] as u32) << 24;
    }
    for (i, k) in nonce.chunks_exact(4).enumerate() {
        state[12 + i] |=
            k[0] as u32 | (k[1] as u32) << 8 | (k[2] as u32) << 16 | (k[3] as u32) << 24;
    }

    rounds(&mut state);

    for (i, out_chunk) in out[..16].chunks_exact_mut(4).enumerate() {
        out_chunk.copy_from_slice(&state[i].to_le_bytes());
    }
    for (i, out_chunk) in out[16..].chunks_exact_mut(4).enumerate() {
        out_chunk.copy_from_slice(&state[12 + i].to_le_bytes());
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use crate::KEY_LEN;

    use super::hchacha20;

    #[test]
    fn state() {
        let mut k = [0u8; KEY_LEN];
        let expected_k =
            hex::decode("82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc")
                .unwrap();
        let key = hex::decode("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
            .unwrap()
            .try_into()
            .unwrap();
        let nonce = hex::decode("000000090000004a0000000031415927")
            .unwrap()
            .try_into()
            .unwrap();

        hchacha20(&key, &nonce, &mut k);
        assert_eq!(&k, expected_k.as_slice());
    }

    #[test]
    fn encrypt() {
        let ptxt = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        let aad = &[
            0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
        ];
        let key = &[
            0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d,
            0x8e, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
            0x9c, 0x9d, 0x9e, 0x9f,
        ];
        let nonce = &[
            0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d,
            0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
        ];

        let mut ctxt = std::vec![0u8; ptxt.len() + 16];
        let (_, tag) = super::encrypt(key, ptxt, &mut ctxt, aad, nonce).unwrap();

        let expected_ctxt = &[
            0xbd, 0x6d, 0x17, 0x9d, 0x3e, 0x83, 0xd4, 0x3b, 0x95, 0x76, 0x57, 0x94, 0x93, 0xc0,
            0xe9, 0x39, 0x57, 0x2a, 0x17, 0x00, 0x25, 0x2b, 0xfa, 0xcc, 0xbe, 0xd2, 0x90, 0x2c,
            0x21, 0x39, 0x6c, 0xbb, 0x73, 0x1c, 0x7f, 0x1b, 0x0b, 0x4a, 0xa6, 0x44, 0x0b, 0xf3,
            0xa8, 0x2f, 0x4e, 0xda, 0x7e, 0x39, 0xae, 0x64, 0xc6, 0x70, 0x8c, 0x54, 0xc2, 0x16,
            0xcb, 0x96, 0xb7, 0x2e, 0x12, 0x13, 0xb4, 0x52, 0x2f, 0x8c, 0x9b, 0xa4, 0x0d, 0xb5,
            0xd9, 0x45, 0xb1, 0x1b, 0x69, 0xb9, 0x82, 0xc1, 0xbb, 0x9e, 0x3f, 0x3f, 0xac, 0x2b,
            0xc3, 0x69, 0x48, 0x8f, 0x76, 0xb2, 0x38, 0x35, 0x65, 0xd3, 0xff, 0xf9, 0x21, 0xf9,
            0x66, 0x4c, 0x97, 0x63, 0x7d, 0xa9, 0x76, 0x88, 0x12, 0xf6, 0x15, 0xc6, 0x8b, 0x13,
            0xb5, 0x2e,
        ];
        let expected_tag = &[
            0xc0, 0x87, 0x59, 0x24, 0xc1, 0xc7, 0x98, 0x79, 0x47, 0xde, 0xaf, 0xd8, 0x78, 0x0a,
            0xcf, 0x49,
        ];

        assert_eq!(expected_tag, tag);
        assert_eq!(expected_ctxt, &ctxt[0..ptxt.len()]);
    }
}
