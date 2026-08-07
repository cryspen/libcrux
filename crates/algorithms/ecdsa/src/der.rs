//! Minimal DER (ASN.1) codec for the ECDSA-Sig-Value structure.
//!
//! ```asn1
//! ECDSA-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }
//! ```
//!
//! while `libcrux-ecdsa` works with the raw `(r, s)` scalars. These helpers
//! convert between the two representations. Only the small encodings produced
//! by P-256 (each integer is at most 33 content bytes, the sequence at most ~70
//! bytes) are relevant, so short-form and single-byte long-form lengths are all
//! that is supported. This module deals purely with encoding, on stack
//! buffers only, since this crate is `no_std` without `alloc`.

const INTEGER_TAG: u8 = 0x02;
const SEQUENCE_TAG: u8 = 0x30;

const HIGH_BIT: u8 = 0x80;

/// Maximum encoded size of a P-256 `ECDSA-Sig-Value`: 2-byte SEQUENCE header
/// plus two INTEGERs of at most 2 (tag + length) + 1 (sign byte) + 32
/// (content) bytes each.
pub(crate) const MAX_DER_LEN: usize = 2 + 2 * (2 + 1 + 32);

/// A fixed-capacity buffer holding a DER-encoded value, together with the
/// number of bytes actually used.
pub(crate) struct DerBuffer {
    buf: [u8; MAX_DER_LEN],
    len: usize,
}

impl DerBuffer {
    /// The encoded bytes.
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.buf[..self.len]
    }
}

/// Append `data` to `buf` at `*pos`, advancing `*pos`.
fn push(buf: &mut [u8; MAX_DER_LEN], pos: &mut usize, data: &[u8]) {
    buf[*pos..*pos + data.len()].copy_from_slice(data);
    *pos += data.len();
}

/// DER-encode a big-endian unsigned integer as an ASN.1 `INTEGER` into `buf`
/// at `*pos`, advancing `*pos` past the written bytes.
fn encode_integer(buf: &mut [u8; MAX_DER_LEN], pos: &mut usize, value: &[u8; 32]) {
    // Strip leading zero bytes, but keep at least one byte.
    let mut start = 0;
    while start + 1 < value.len() && value[start] == 0 {
        start += 1;
    }
    let content = &value[start..];

    // ASN.1 integers are signed. If the high bit is set, prepend a zero byte
    // so the value is interpreted as positive.
    let needs_sign_byte = content.first().is_some_and(|b| b & HIGH_BIT != 0);
    let content_len = content.len() + if needs_sign_byte { 1 } else { 0 };

    push(buf, pos, &[INTEGER_TAG, content_len as u8]); // content length always < 128 for P-256
    if needs_sign_byte {
        push(buf, pos, &[0x00]);
    }
    push(buf, pos, content);
}

/// Encode a raw `(r, s)` P-256 signature (each 32 bytes) as a DER
/// `ECDSA-Sig-Value`.
pub(crate) fn raw_to_der(r: &[u8; 32], s: &[u8; 32]) -> DerBuffer {
    let mut buf = [0u8; MAX_DER_LEN];
    // Encode the integers into a scratch area first so we know the body
    // length before writing the SEQUENCE header.
    let mut body = [0u8; MAX_DER_LEN];
    let mut body_len = 0;
    encode_integer(&mut body, &mut body_len, r);
    encode_integer(&mut body, &mut body_len, s);

    let mut pos = 0;
    push(&mut buf, &mut pos, &[SEQUENCE_TAG, body_len as u8]); // body length always < 128 for P-256
    push(&mut buf, &mut pos, &body[..body_len]);

    DerBuffer { buf, len: pos }
}

/// Read a DER length (short form or single-byte long form) starting at `*pos`,
/// advancing `*pos` past the length octets.
fn read_len(bytes: &[u8], pos: &mut usize) -> Option<usize> {
    let first = *bytes.get(*pos)?;
    *pos += 1;
    if first < 0x80 {
        Some(first as usize)
    } else if first == 0x81 {
        let len = *bytes.get(*pos)? as usize;
        *pos += 1;
        Some(len)
    } else {
        // Larger lengths cannot occur for P-256 signatures.
        None
    }
}

/// Read a DER `INTEGER` starting at `*pos` and return it left-padded to 32
/// bytes, advancing `*pos` past the integer.
fn read_integer_32(bytes: &[u8], pos: &mut usize) -> Option<[u8; 32]> {
    if *bytes.get(*pos)? != INTEGER_TAG {
        return None;
    }
    *pos += 1;
    let len = read_len(bytes, pos)?;
    let content = bytes.get(*pos..*pos + len)?;
    *pos += len;

    // Strip leading zero bytes (sign byte / minimal-encoding padding).
    let trimmed = {
        let mut start = 0;
        while start < content.len() && content[start] == 0 {
            start += 1;
        }
        &content[start..]
    };
    if trimmed.len() > 32 {
        return None;
    }

    let mut out = [0u8; 32];
    out[32 - trimmed.len()..].copy_from_slice(trimmed);
    Some(out)
}

/// Decode a DER `ECDSA-Sig-Value` into raw `(r, s)` scalars, each 32 bytes.
///
/// Returns `None` if the input is not a well-formed P-256 signature.
pub(crate) fn der_to_raw(der: &[u8]) -> Option<([u8; 32], [u8; 32])> {
    let mut pos = 0;
    if *der.get(pos)? != SEQUENCE_TAG {
        return None;
    }
    pos += 1;
    let seq_len = read_len(der, &mut pos)?;
    if pos + seq_len != der.len() {
        return None;
    }
    let r = read_integer_32(der, &mut pos)?;
    let s = read_integer_32(der, &mut pos)?;
    if pos != der.len() {
        return None;
    }
    Some((r, s))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_high_bit() {
        let r = [0x80u8; 32]; // high bit set → needs sign padding
        let s = [0x01u8; 32];
        let der = raw_to_der(&r, &s);
        let (r2, s2) = der_to_raw(der.as_bytes()).unwrap();
        assert_eq!(r, r2);
        assert_eq!(s, s2);
    }

    #[test]
    fn roundtrip_leading_zeros() {
        let mut r = [0u8; 32];
        r[31] = 0x2a; // small value with many leading zeros
        let s = [0xffu8; 32];
        let der = raw_to_der(&r, &s);
        let (r2, s2) = der_to_raw(der.as_bytes()).unwrap();
        assert_eq!(r, r2);
        assert_eq!(s, s2);
    }

    #[test]
    fn rejects_garbage() {
        assert!(der_to_raw(&[0x00, 0x01, 0x02]).is_none());
        assert!(der_to_raw(&[]).is_none());
    }
}
