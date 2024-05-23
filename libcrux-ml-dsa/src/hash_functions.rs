#![allow(non_snake_case)]
pub(crate) fn H<const OUTPUT_LENGTH: usize>(input: &[u8]) -> [u8; OUTPUT_LENGTH] {
    let mut out = [0u8; OUTPUT_LENGTH];
    libcrux_sha3::portable::shake256(&mut out, input);

    out
}

pub(crate) mod XOF {
    use libcrux_sha3::portable::{incremental, KeccakState1};

    const BLOCK_SIZE: usize = 168;
    const FIVE_BLOCKS_SIZE: usize = BLOCK_SIZE * 5;

    #[inline(always)]
    pub(crate) fn new(seed: [u8; 34]) -> KeccakState1 {
        let mut state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, &seed);

        state
    }

    pub(crate) fn squeeze_first_five_blocks(state: &mut KeccakState1) -> [u8; FIVE_BLOCKS_SIZE] {
        let mut out = [0u8; FIVE_BLOCKS_SIZE];
        incremental::shake128_squeeze_first_five_blocks(state, &mut out);

        out
    }

    pub(crate) fn squeeze_next_block(state: &mut KeccakState1) -> [u8; BLOCK_SIZE] {
        let mut out = [0u8; BLOCK_SIZE];
        incremental::shake128_squeeze_next_block(state, &mut out);

        out
    }
}
