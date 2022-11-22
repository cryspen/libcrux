//! # hacspec chacha20 poly1305
//!
//! This module contains the hacspec implementation of Chacha20Poly1305
//! using the libjade primitives for Chacha20 and Poly1305.

// Import hacspec and all needed definitions.
use hacspec_lib::*;

// Import chacha20 and poly1305 from libjade
use libjade::*;

#[derive(Debug)]
pub enum Error {
    InvalidTag,
}

public_bytes!(Nonce, 12);
public_bytes!(Key, 32);
public_bytes!(Block, 64);
public_bytes!(Tag, 16);
type ByteSeqResult = Result<Seq<u8>, Error>;

fn poly1305_key(key: Key, iv: Nonce) -> Key {
    // let key_block0 = chacha20_key_block0(key, iv);
    let key_block0 = [0u8; 32];
    let r = unsafe {
        jade_stream_chacha_chacha20_ietf_amd64_ref(
            key_block0.as_ptr() as _,
            32,
            iv.0.as_ptr() as _,
            key.0.as_ptr() as _,
        )
    };
    assert!(r == 0); // TODO: handle error
    Key::from_native_slice(&key_block0)
}

/// pad16(x):
///     if (len(x) % 16)==0
///        then return NULL
///        else return copies(0, 16-(len(x)%16))
///     end
fn pad16(x: &PublicByteSeq) -> PublicByteSeq {
    if x.len() % 16 == 0 {
        PublicByteSeq::new(0)
    } else {
        PublicByteSeq::new(16 - (x.len() % 16))
    }
}

fn pad16_len(x: &PublicByteSeq) -> usize {
    if x.len() % 16 == 0 {
        0
    } else {
        16 - (x.len() % 16)
    }
}

/// Encrypt
///
/// XXX: not streaming
///
/// chacha20_aead_encrypt(aad, key, iv, constant, plaintext):
///     nonce = constant | iv
///     otk = poly1305_key_gen(key, nonce)
///     ciphertext = chacha20_encrypt(key, 1, nonce, plaintext)
///     mac_data = aad | pad16(aad)
///     mac_data |= ciphertext | pad16(ciphertext)
///     mac_data |= num_to_8_le_bytes(aad.length)
///     mac_data |= num_to_8_le_bytes(ciphertext.length)
///     tag = poly1305_mac(mac_data, otk)
///     return (ciphertext, tag)
fn chacha20_poly1305_encrypt_hacspec(
    key: Key,
    iv: Nonce,
    aad: &PublicByteSeq,
    msg: &PublicByteSeq,
) -> (PublicByteSeq, Tag) {
    let poly_key = poly1305_key(key, iv);
    let msg_len = msg.len();
    let mut ciphertext = vec![0u8; msg_len];
    let r = unsafe {
        // FIXME: The counter has to be set to 1.
        //        https://formosa-crypto.zulipchat.com/#narrow/stream/308382-Libjade.3Ageneral/topic/chacha-poly/near/311530838
        jade_stream_chacha_chacha20_ietf_amd64_ref(
            ciphertext.as_mut_ptr(),
            msg_len as u64,
            iv.0.as_ptr() as _,
            key.0.as_ptr() as _,
        )
    };
    assert!(r == 0); // TODO: error handling.
    let ciphertext = PublicByteSeq::from_native_slice(&ciphertext);

    // Concat aad and ciphertext
    let mut mac_data = PublicByteSeq::new(
        aad.len() + pad16_len(aad) + ciphertext.len() + pad16_len(&ciphertext) + 8 + 8,
    );
    mac_data = mac_data.concat(aad);
    mac_data = mac_data.concat_owned(pad16(aad));
    mac_data = mac_data.concat(&ciphertext);
    mac_data = mac_data.concat_owned(pad16(&ciphertext));
    mac_data = mac_data.concat(&u64_to_le_bytes(aad.len() as u64));
    mac_data = mac_data.concat(&u64_to_le_bytes(ciphertext.len() as u64));
    let mut tag = Tag::default();
    let r = unsafe {
        jade_onetimeauth_poly1305_amd64_ref(
            tag.0.as_mut_ptr(),
            aad.native_slice().as_ptr() as _,
            aad.len() as u64,
            poly_key.0.as_ptr() as _,
        )
    };
    assert!(r == 0); // TODO: error hanlding
    (ciphertext, tag)
}

pub fn chacha20_poly1305_encrypt(
    key: &[u8; 32],
    iv: &[u8; 12],
    aad: &[u8],
    msg: &[u8],
) -> (Vec<u8>, [u8; 16]) {
    let key = Key::from_native_slice(key);
    let iv = Nonce::from_native_slice(iv);
    let aad = PublicByteSeq::from_native_slice(aad);
    let msg = PublicByteSeq::from_native_slice(msg);
    let (ctxt, tag) = chacha20_poly1305_encrypt_hacspec(key, iv, &aad, &msg);
    (ctxt.native_slice().to_vec(), tag.0)
}

// pub fn chacha20_poly1305_decrypt(
//     key: Key,
//     iv: Nonce,
//     aad: &ByteSeq,
//     cipher_text: &ByteSeq,
//     tag: Poly1305Tag,
// ) -> ByteSeqResult {
//     let mut poly_st = init(key, iv);
//     poly_st = poly1305_update_padded(aad, poly_st);
//     poly_st = poly1305_update_padded(cipher_text, poly_st);
//     let my_tag = finish(aad.len(), cipher_text.len(), poly_st);
//     if my_tag.declassify_eq(&tag) {
//         ByteSeqResult::Ok(chacha20(key, iv, 1u32, cipher_text))
//     } else {
//         ByteSeqResult::Err(Error::InvalidTag)
//     }
// }
