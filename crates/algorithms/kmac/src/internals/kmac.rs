use libcrux_sha3::portable::incremental::{CShake128It, CShake256It};

const KMAC_LABEL: &[u8; 4] = b"KMAC";
const LABEL_LEN: usize = KMAC_LABEL.len() << 3;

// From https://github.com/hoxxep/MACs/blob/kmac-submission/kmac/src/encoding.rs
pub(crate) fn num_encoding_size(num: usize) -> u8 {
    let zero_bits = (num | 1).leading_zeros() as u8;
    debug_assert!(zero_bits < 64);
    let bits = 64u8 - zero_bits;
    bits.div_ceil(8)
}

#[inline(always)]
pub(crate) fn left_encode_byte(num: u8) -> [u8; 2] {
    [1u8, num]
}

#[inline(always)]
pub(crate) fn left_encode(num: usize, buffer: &mut [u8; 9]) -> &[u8] {
    let encoding_size = num_encoding_size(num);
    debug_assert!(encoding_size < 9);
    let encoding_length = encoding_size as usize;
    buffer[0] = encoding_size;
    buffer[1..=encoding_length].copy_from_slice(&num.to_be_bytes()[8 - encoding_length..]);
    &buffer[..=encoding_length]
}

#[inline(always)]
pub(crate) fn right_encode(num: usize, buffer: &mut [u8; 9]) -> &[u8] {
    let encoding_size = num_encoding_size(num);
    debug_assert!(encoding_size < 9);
    let encoding_length = encoding_size as usize;
    buffer[0..encoding_length].copy_from_slice(&num.to_be_bytes()[8 - encoding_length..]);
    buffer[encoding_length] = encoding_size;
    &buffer[..=encoding_length]
}

pub fn compute_kmac_128<'a>(
    tag: &'a mut [u8],
    tag_length: usize,
    key: &[u8],
    key_length: usize,
    data: &[u8],
    customization: &[u8],
    customization_length: usize,
) -> &'a [u8] {
    const RATE: usize = 168;

    let mut state = CShake128It::new();
    let zeros = [0u8; RATE];
    let mut b = [0u8; 9];
    let customization_length = customization_length << 3;
    let key_length = key_length << 3;
    let tag_length = tag_length << 3;

    // Assert RATE can be casted to u8
    // XXX: Unfortunately const blocks are not supported by hax.
    // const { assert!(RATE < 256) };

    // Left bytepad
    state.absorb(&left_encode_byte(RATE as u8));

    // Encode string KMAC
    state.absorb(left_encode(LABEL_LEN, &mut b));
    state.absorb(KMAC_LABEL);

    // Encode string customization label
    let custom_enc = left_encode(customization_length, &mut b);
    state.absorb(custom_enc);
    state.absorb(customization);

    // Pad zeros
    let buffer_len = 2 + 6 + custom_enc.len() + customization.len();
    let n_zeros = buffer_len.next_multiple_of(RATE) - buffer_len;
    debug_assert!(n_zeros < RATE);
    state.absorb(&zeros[..n_zeros]);

    // Compute new_X
    // Left bytepad
    state.absorb(&left_encode_byte(RATE as u8));

    // encode_string K
    let key_enc = left_encode(key_length, &mut b);
    state.absorb(key_enc);
    state.absorb(key);

    // Pad zeros
    let buffer_len = 2 + key_enc.len() + key.len();
    let n_zeros = buffer_len.next_multiple_of(RATE) - buffer_len;
    debug_assert!(n_zeros < RATE);
    state.absorb(&zeros[..n_zeros]);

    // Append data
    state.absorb(data);

    // Right encode output length
    state.absorb_finalize(right_encode(tag_length, &mut b), tag);

    tag
}

pub fn compute_kmac_256<'a>(
    tag: &'a mut [u8],
    tag_length: usize,
    key: &[u8],
    key_length: usize,
    data: &[u8],
    customization: &[u8],
    customization_length: usize,
) -> &'a [u8] {
    const RATE: usize = 136;

    let mut state = CShake256It::new();
    let zeros = [0u8; RATE];
    let customization_length = customization_length << 3;
    let key_length = key_length << 3;
    let tag_length = tag_length << 3;
    let mut b = [0u8; 9];

    // Assert RATE can be casted to u8
    // XXX: Unfortunately const blocks are not supported by hax.
    // const { assert!(RATE < 256) };

    // Left bytepad
    state.absorb(&left_encode_byte(RATE as u8));
    // Encode string KMAC
    state.absorb(left_encode(LABEL_LEN, &mut b));
    state.absorb(KMAC_LABEL);

    // Encode string customization label
    let custom_enc = left_encode(customization_length, &mut b);
    state.absorb(custom_enc);
    state.absorb(customization);

    // Pad zeros
    let buffer_len = 2 + 6 + custom_enc.len() + customization.len();
    let n_zeros = buffer_len.next_multiple_of(RATE) - buffer_len;
    debug_assert!(n_zeros < RATE);
    state.absorb(&zeros[..n_zeros]);

    // Compute new_X
    // Left bytepad
    state.absorb(&left_encode_byte(RATE as u8));

    // encode_string K
    let key_enc = left_encode(key_length, &mut b);
    state.absorb(key_enc);
    state.absorb(key);

    // Pad zeros
    let buffer_len = 2 + key_enc.len() + key.len();
    let n_zeros = buffer_len.next_multiple_of(RATE) - buffer_len;
    debug_assert!(n_zeros < RATE);
    state.absorb(&zeros[..n_zeros]);

    // Append data
    state.absorb(data);

    // Right encode output length
    state.absorb_finalize(right_encode(tag_length, &mut b), tag);

    tag
}
