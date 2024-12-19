use crate::{AeadError, KEY_LEN, NONCE_LEN, TAG_LEN};

/// The ChaCha20-Poly1305 AEAD encryption function. Writes the concatenation of the ciphertexoft
/// produced by ChaCha20 and the MAC tag into `ctxt` and returns the two pieces separately.
///
/// This implementation is backed by hacl-rs and can only handle inputs up to a length of `u32::MAX`.
/// When provided longer values, this function will return an error.
pub fn encrypt<'a>(
    key: &[u8; KEY_LEN],
    ptxt: &[u8],
    ctxt: &'a mut [u8],
    aad: &[u8],
    nonce: &[u8; NONCE_LEN],
) -> Result<(&'a [u8], &'a [u8; TAG_LEN]), AeadError> {
    let ptxt_len: u32 = ptxt
        .len()
        .try_into()
        .map_err(|_| AeadError::PlaintextTooLarge)?;

    let aad_len: u32 = aad.len().try_into().map_err(|_| AeadError::AadTooLarge)?;

    // we already knwo that ptxt.len() < u32::MAX, so we can safely add here.
    if ctxt.len() < ptxt.len() + TAG_LEN {
        return Err(AeadError::CiphertextTooShort);
    }

    // ensure destination slice has just the right length
    let (ctxt_cpa, tag) = ctxt.split_at_mut(ptxt.len());
    let tag: &mut [u8; TAG_LEN] = tag.try_into().unwrap();

    crate::hacl::aead_chacha20poly1305::encrypt(
        ctxt_cpa, tag, ptxt, ptxt_len, aad, aad_len, key, nonce,
    );

    Ok((ctxt_cpa, tag))
}

/// The ChaCha20-Poly1305 AEAD decryption function. Writes the result of the decryption to `ptxt`,
/// and returns the slice of appropriate length.
///
/// This implementation is backed by hacl-rs and can only handle inputs up to a length of `u32::MAX`.
/// When provided longer values, this function will return an error.
pub fn decrypt<'a>(
    key: &[u8; KEY_LEN],
    ptxt: &'a mut [u8],
    ctxt: &[u8],
    aad: &[u8],
    nonce: &[u8; NONCE_LEN],
) -> Result<&'a [u8], AeadError> {
    if ctxt.len() < TAG_LEN {
        return Err(AeadError::InvalidCiphertext);
    }

    // we know that ctxt.len() >= TAG_LEN, so we can subtract
    if ptxt.len() < ctxt.len() - TAG_LEN {
        return Err(AeadError::PlaintextTooShort);
    }

    let ctxt_len: u32 = ctxt
        .len()
        .try_into()
        .map_err(|_| AeadError::CiphertextTooLarge)?;

    let aad_len: u32 = aad.len().try_into().map_err(|_| AeadError::AadTooLarge)?;

    let (ctxt_cpa, tag) = ctxt.split_at(ctxt.len() - TAG_LEN);
    let ptxt = &mut ptxt[..ctxt_cpa.len()];

    // this call should only ever produce 0 or 1, where 0 is success and 1 is error
    match crate::hacl::aead_chacha20poly1305::decrypt(
        ptxt, ctxt_cpa, ctxt_len, aad, aad_len, key, nonce, tag,
    ) {
        0 => Ok(ptxt),
        _ => Err(AeadError::InvalidCiphertext),
    }
}

/// The ChaCha20-Poly1305 AEAD decryption function. Writes the result of the decryption to `ptxt`,
/// and returns the slice of appropriate length.
///
/// This implementation is backed by hacl-rs and can only handle inputs up to a length of `u32::MAX`.
/// When provided longer values, this function will return an error.
pub fn decrypt_detached<'a>(
    key: &[u8; KEY_LEN],
    ptxt: &'a mut [u8],
    ctxt: &[u8],
    tag: &[u8; TAG_LEN],
    aad: &[u8],
    nonce: &[u8; NONCE_LEN],
) -> Result<&'a [u8], AeadError> {
    if ptxt.len() < ctxt.len() {
        return Err(AeadError::PlaintextTooShort);
    }

    let ctxt_len: u32 = ctxt
        .len()
        .try_into()
        .map_err(|_| AeadError::CiphertextTooLarge)?;

    let aad_len: u32 = aad.len().try_into().map_err(|_| AeadError::AadTooLarge)?;

    let ptxt = &mut ptxt[..ctxt.len()];

    // this call should only ever produce 0 or 1, where 0 is success and 1 is error
    match crate::hacl::aead_chacha20poly1305::decrypt(
        ptxt, ctxt, ctxt_len, aad, aad_len, key, nonce, tag,
    ) {
        0 => Ok(ptxt),
        _ => Err(AeadError::InvalidCiphertext),
    }
}
