use libcrux_sha3::portable::incremental::Xof;

const KMAC_LABEL: &[u8; 4] = b"KMAC";
const LABEL_LEN: usize = KMAC_LABEL.len() << 3;

// From https://github.com/hoxxep/MACs/blob/kmac-submission/kmac/src/encoding.rs
pub(crate) fn zero_bytes(num: usize) -> u8 {
    let zero_bits = (num | 1usize).leading_zeros();
    let zero_bits = (zero_bits % 64) as u8;
    zero_bits / 8
}

#[inline(always)]
pub(crate) fn left_encode_byte(num: u8) -> [u8; 2] {
    [1u8, num]
}

#[inline(always)]
pub(crate) fn encode(num: usize, buffer: &mut [u8; 9], left_encode: bool) -> &[u8] {
    let zero_size = zero_bytes(num);
    let zero_length = zero_size as usize;
    let be_bytes = num.to_be_bytes();
    let encoding_length = be_bytes.len() - zero_length;
    let encoding_size = encoding_length as u8;
    debug_assert!(0 < encoding_length);
    debug_assert!(encoding_length <= 8);
    let output_length = encoding_length + 1;
    if left_encode {
        buffer[0] = encoding_size;
        buffer[1..output_length].copy_from_slice(&be_bytes[zero_length..]);
    } else {
        buffer[0..encoding_length].copy_from_slice(&be_bytes[zero_length..]);
        buffer[encoding_length] = encoding_size;
    }

    &buffer[..output_length]
}

#[inline(always)]
pub(crate) fn left_encode(num: usize, buffer: &mut [u8; 9]) -> &[u8] {
    encode(num, buffer, true)
}

#[inline(always)]
pub(crate) fn right_encode(num: usize, buffer: &mut [u8; 9]) -> &[u8] {
    encode(num, buffer, false)
}

pub fn compute_kmac<'a, const RATE: usize, CShake: Xof<RATE>>(
    tag: &'a mut [u8],
    tag_length: usize,
    key: &[u8],
    key_length: usize,
    data: &[u8],
    customization: &[u8],
    customization_length: usize,
) -> &'a [u8] {
    let mut state = CShake::new();
    // let mut state = CShake256It::new();
    let zeros = [0u8; RATE];
    let customization_bits = customization_length << 3;
    let key_bits = key_length << 3;
    let tag_bits = tag_length << 3;
    let mut b = [0u8; 9];

    // Left bytepad
    state.absorb(&left_encode_byte(RATE as u8));
    // Encode string KMAC
    state.absorb(left_encode(LABEL_LEN, &mut b));
    state.absorb(KMAC_LABEL);

    // Encode string customization label
    let custom_enc = left_encode(customization_bits, &mut b);
    state.absorb(custom_enc);
    state.absorb(customization);

    // Pad zeros
    let buffer_len = 2 + 6 + custom_enc.len() + (customization_length % RATE);
    let n_zeros = (RATE - (buffer_len % RATE)) % RATE;
    debug_assert!(n_zeros < RATE);
    state.absorb(&zeros[..n_zeros]);

    // Compute new_X
    // Left bytepad
    state.absorb(&left_encode_byte(RATE as u8));

    // encode_string K
    let key_enc = left_encode(key_bits, &mut b);
    state.absorb(key_enc);
    state.absorb(key);

    // Pad zeros
    let buffer_len = 2 + key_enc.len() + (key_length % RATE);
    let n_zeros = (RATE - (buffer_len % RATE)) % RATE;
    debug_assert!(n_zeros < RATE);
    state.absorb(&zeros[..n_zeros]);

    // Append data
    state.absorb(data);

    // Right encode output length
    state.absorb_final(right_encode(tag_bits, &mut b));
    state.squeeze(tag);
    // state.absorb_finalize(right_encode(tag_bits, &mut b), tag);

    tag
}
