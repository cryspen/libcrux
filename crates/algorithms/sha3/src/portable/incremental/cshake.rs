use crate::{
    generic_keccak::xof::KeccakXofState,
    portable::incremental::{private::Sealed, CShake},
};

pub struct CShakeIncremental<const RATE: usize> {
    state: KeccakXofState<1, RATE, u64>,
}

/// A portable, incremental implementation of CSHAKE-128.
pub type CShake128 = CShakeIncremental<168>;
/// A portable, incremental implementation of CSHAKE-256.
pub type CShake256 = CShakeIncremental<136>;

// From https://github.com/hoxxep/MACs/blob/kmac-submission/kmac/src/encoding.rs
fn zero_bytes(num: usize) -> u8 {
    let zero_bits = (num | 1usize).leading_zeros();
    let zero_bits = (zero_bits % 64) as u8;
    zero_bits / 8
}

#[inline(always)]
/// Left-encode a single byte.
pub fn left_encode_byte(num: u8) -> [u8; 2] {
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
/// Left-encode any `num < u64::MAX`.
pub fn left_encode(num: usize, buffer: &mut [u8; 9]) -> &[u8] {
    encode(num, buffer, true)
}

#[inline(always)]
/// Right-encode any `num < u64::MAX`.
pub fn right_encode(num: usize, buffer: &mut [u8; 9]) -> &[u8] {
    encode(num, buffer, false)
}

#[hax_lib::attributes]
impl<const RATE: usize> CShake<RATE> for CShakeIncremental<RATE>
where
    CShakeIncremental<RATE>: Sealed,
{
    #[requires(RATE == 136 || RATE == 168)]
    fn new(name: &[u8], customization: &[u8]) -> Self {
        let mut state = KeccakXofState::<1, RATE, u64>::new();

        let zeros = [0u8; RATE];
        let name_bits = name.len() << 3;
        let customization_bits = customization.len() << 3;
        let mut b = [0u8; 9];

        // Left bytepad
        state.absorb(&[&left_encode_byte(RATE as u8)]);
        // Encode name string
        let name_bits_encoding = left_encode(name_bits, &mut b);
        let name_bits_encoding_len = name_bits_encoding.len();
        state.absorb(&[name_bits_encoding]);
        state.absorb(&[name]);

        // Encode customization string
        let customization_encoding = left_encode(customization_bits, &mut b);
        let customization_encoding_len = customization_encoding.len();
        state.absorb(&[customization_encoding]);
        state.absorb(&[customization]);

        // Pad zeros
        let buffer_len = 2
            + name.len()
            + name_bits_encoding_len
            + customization_encoding_len
            + (customization.len() % RATE);
        let n_zeros = (RATE - (buffer_len % RATE)) % RATE;
        debug_assert!(n_zeros < RATE);
        state.absorb(&[&zeros[..n_zeros]]);

        Self { state }
    }

    fn absorb(&mut self, input: &[u8]) {
        self.state.absorb(&[input]);
    }

    fn absorb_final(&mut self, input: &[u8]) {
        self.state.absorb_final::<0x4u8>(&[input]);
    }

    fn squeeze(&mut self, out: &mut [u8]) {
        self.state.squeeze(out);
    }
}
