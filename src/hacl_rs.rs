use hacl_rs::hacl::aead_chacha20poly1305;

use crate::aead::{DecryptError, Tag};

/// Encrypt Chacha20Poly1305 hacl rs.
pub(crate) fn hacl_rs_encrypt(key: &[u8], msg_ctxt: &mut [u8], iv: &[u8], aad: &[u8]) -> Tag {
    let mut tag = [0u8; 16];
    let mut output = vec![0u8; msg_ctxt.len()];
    let input = msg_ctxt;
    let data =
        unsafe { &mut *(core::ptr::slice_from_raw_parts_mut(aad.as_ptr() as *mut u8, aad.len())) };
    let nonce =
        unsafe { &mut *(core::ptr::slice_from_raw_parts_mut(iv.as_ptr() as *mut u8, iv.len())) };
    let key =
        unsafe { &mut *(core::ptr::slice_from_raw_parts_mut(key.as_ptr() as *mut u8, key.len())) };
    let input_len = input.len().try_into().unwrap();
    // XXX: handle
    let data_len = aad.len().try_into().unwrap();
    // XXX: handle
    aead_chacha20poly1305::encrypt(
        &mut output,
        &mut tag,
        input,
        input_len,
        data,
        data_len,
        key,
        nonce,
    );
    for (dst, src) in input.iter_mut().zip(output) {
        *dst = src;
    }
    tag.into()
}

/// Dencrypt Chacha20Poly1305 hacl rs.
pub(crate) fn hacl_rs_decrypt(
    key: &[u8],
    ctxt_msg: &mut [u8],
    iv: &[u8],
    aad: &[u8],
    tag: &[u8],
) -> Result<(), DecryptError> {
    let mut output = vec![0u8; ctxt_msg.len()];
    let input = ctxt_msg;
    let data =
        unsafe { &mut *(core::ptr::slice_from_raw_parts_mut(aad.as_ptr() as *mut u8, aad.len())) };
    let nonce =
        unsafe { &mut *(core::ptr::slice_from_raw_parts_mut(iv.as_ptr() as *mut u8, iv.len())) };
    let key =
        unsafe { &mut *(core::ptr::slice_from_raw_parts_mut(key.as_ptr() as *mut u8, key.len())) };
    let tag =
        unsafe { &mut *(core::ptr::slice_from_raw_parts_mut(tag.as_ptr() as *mut u8, tag.len())) };
    let input_len = input.len().try_into().unwrap();
    // XXX: handle
    let data_len = aad.len().try_into().unwrap();
    // XXX: handle
    let r = aead_chacha20poly1305::decrypt(
        &mut output,
        input,
        input_len,
        data,
        data_len,
        key,
        nonce,
        tag,
    );
    if r == 0 {
        for (dst, src) in input.iter_mut().zip(output) {
            *dst = src;
        }
        Ok(())
    } else {
        Err(DecryptError::DecryptionFailed)
    }
}

pub(crate) fn x25519(
    private_key: impl AsRef<[u8; 32]>,
    public_key: impl AsRef<[u8; 32]>,
) -> Result<[u8; 32], crate::ecdh::Error> {
    use hacl_rs::hacl::curve25519_51::*;

    let mut result = [0u8; 32];
    let private_key = private_key.as_ref();
    let private_key = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(
            private_key.as_ptr() as *mut u8,
            private_key.len(),
        ))
    };
    let public_key = public_key.as_ref();
    let public_key = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(
            public_key.as_ptr() as *mut u8,
            public_key.len(),
        ))
    };
    if ecdh(&mut result, private_key, public_key) {
        return Ok(result);
    } else {
        return Err(crate::ecdh::Error::InvalidPoint);
    }
}


pub(crate) fn x25519_secret_to_public(
    private_key: impl AsRef<[u8; 32]>,
) -> [u8; 32]{
    use hacl_rs::hacl::curve25519_51::*;

    let mut result = [0u8; 32];
    let private_key = private_key.as_ref();
    let private_key = unsafe {
        &mut *(core::ptr::slice_from_raw_parts_mut(
            private_key.as_ptr() as *mut u8,
            private_key.len(),
        ))
    };
    secret_to_public(&mut result, private_key);
    result
}
