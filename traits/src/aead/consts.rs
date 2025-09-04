pub trait AeadConsts {
    const KEY_LEN: usize;
    const TAG_LEN: usize;
    const NONCE_LEN: usize;
}
