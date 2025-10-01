use super::arrayref::*;

/// A simple test function that exercises basic AEAD encrypt/decrypt functionality.
///
/// This function performs a round-trip encryption and decryption operation using
/// the provided AEAD implementation and verifies that the original plaintext is recovered.
pub fn simple<
    const KEY_LEN: usize,
    const TAG_LEN: usize,
    const NONCE_LEN: usize,
    T: Aead<KEY_LEN, TAG_LEN, NONCE_LEN>,
>() {
    let key = [1; KEY_LEN];
    let nonce = [2; NONCE_LEN];
    let plaintext = b"abcdefgh";
    let aad = b"ijklmnop";

    let mut ciphertext = [0; 8];
    let mut tag = [0; TAG_LEN];
    T::encrypt(&mut ciphertext, &mut tag, &key, &nonce, aad, plaintext)
        .expect("Aead::encrypt failed");

    let mut decrypted_plaintext = [0; 8];
    T::decrypt(
        &mut decrypted_plaintext,
        &key,
        &nonce,
        aad,
        &ciphertext,
        &tag,
    )
    .expect("Aead::decrypt failed");

    assert_eq!(*plaintext, decrypted_plaintext);
}
