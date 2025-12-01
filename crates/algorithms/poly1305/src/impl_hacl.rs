use crate::{Error, KEY_LEN, TAG_LEN};

/// Computes the Poly1305 MAC tag for the provided `key` and `msg` and writes it into `tag`.
///
/// Returns an error if `msg` is longer than u32::MAX.
pub fn mac(key: &[u8; KEY_LEN], msg: &[u8], tag: &mut [u8; TAG_LEN]) -> Result<(), Error> {
    let msg_len: u32 = msg.len().try_into().map_err(|_| Error::MessageTooLarge)?;

    crate::hacl::mac_poly1305::mac(tag, msg, msg_len, key);

    Ok(())
}
