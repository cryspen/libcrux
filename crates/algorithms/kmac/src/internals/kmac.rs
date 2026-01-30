use libcrux_sha3::portable::incremental::{left_encode, left_encode_byte, right_encode, CShake};

const KMAC_LABEL: &[u8; 4] = b"KMAC";

#[hax_lib::requires(RATE == 136 || RATE == 168)]
pub fn compute_kmac<'a, const RATE: usize, CShakeState: CShake<RATE>>(
    tag: &'a mut [u8],
    tag_length: usize,
    key: &[u8],
    key_length: usize,
    data: &[u8],
    customization: &[u8],
) -> &'a [u8] {
    let mut state = CShakeState::new(KMAC_LABEL, customization);

    let zeros = [0u8; RATE];
    // let customization_bits = customization_length << 3;
    let key_bits = key_length << 3;
    let tag_bits = tag_length << 3;
    let mut b = [0u8; 9];

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

    tag
}
