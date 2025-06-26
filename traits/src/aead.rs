//! AEAD Interface

pub enum AEADError {
    EncryptError,
    DecryptError,
}

pub trait AEADInternal<const TAG_LEN: usize, const KEY_LEN: usize, const IV_LEN: usize> {
    fn encrypt_detached(
        ciphertext: &mut [u8],
        tag: &mut [u8; TAG_LEN],
        key: &[u8; KEY_LEN],
        iv: &[u8; IV_LEN],
        plaintext: &[u8],
        aad: &[u8],
    ) -> Result<(), AEADError>;

    // Document: Tag appended
    fn encrypt(
        ciphertext_tag: &mut [u8],
        key: &[u8; KEY_LEN],
        iv: &[u8; IV_LEN],
        plaintext: &[u8],
        aad: &[u8],
    ) -> Result<(), AEADError>;

    fn decrypt_detached(
        plaintext: &mut [u8],
        key: &[u8; KEY_LEN],
        iv: &[u8; IV_LEN],
        ciphertext: &[u8],
        tag: &[u8; TAG_LEN],
        aad: &[u8],
    ) -> Result<(), AEADError>;

    // Document: Tag appended
    fn decrypt(
        plaintext: &mut [u8],
        key: &[u8; KEY_LEN],
        iv: &[u8; IV_LEN],
        ciphertext_tag: &[u8],
        aad: &[u8],
    ) -> Result<(), AEADError>;

    // Document: Tag appended
    fn encrypt_inplace(
        ptxt_ctxt: &mut [u8],
        key: &[u8; KEY_LEN],
        iv: &[u8; IV_LEN],
        aad: &[u8],
    ) -> Result<(), AEADError>;

    fn encrypt_inplace_detached(
        ptxt_ctxt: &mut [u8],
        tag: &mut [u8; TAG_LEN],
        key: &[u8; KEY_LEN],
        iv: &[u8; IV_LEN],
        aad: &[u8],
    ) -> Result<(), AEADError>;

    // Document: Tag appended
    fn decrypt_inplace(
        ctxt_ptxt: &mut [u8],
        key: &[u8; KEY_LEN],
        iv: &[u8; IV_LEN],
        aad: &[u8],
    ) -> Result<(), AEADError>;

    fn decrypt_inplace_detached(
        ctxt_ptxt: &mut [u8],
        tag: &[u8; TAG_LEN],
        key: &[u8; KEY_LEN],
        iv: &[u8; IV_LEN],
        aad: &[u8],
    ) -> Result<(), AEADError>;
}

// Randomized for keygen / iv gen
// Ref version
// Typed version
// Struct based dynamic version
