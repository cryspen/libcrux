pub(crate) mod field;
pub(crate) mod ring;

pub(crate) fn bytes_to_bit_vector(bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len() * 8);

    for byte in bytes {
        for j in 0..u8::BITS {
            out.push((byte >> j) & 1);
        }
    }
    out
}
