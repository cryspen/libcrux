//! The AES block cipher function.

use crate::platform::*;

pub(crate) type ExtendedKey<T, const NUM_KEYS: usize> = [T; NUM_KEYS];

// This is inlined into the key expansion below.
// const RCON: [u8; 11] = [
//     0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36,
// ];

/// AES block size
pub(crate) const AES_BLOCK_LEN: usize = 16;

/// The AES block cipher function.
#[inline]
pub(crate) fn block_cipher<T: AESState, const NUM_KEYS: usize>(
    st: &mut T,
    keyex: &ExtendedKey<T, NUM_KEYS>,
) {
    st.xor_key(&keyex[0]);
    for i in 1..NUM_KEYS - 1 {
        st.aes_enc(&keyex[i]);
    }
    st.aes_enc_last(&keyex[NUM_KEYS - 1]);
}
