#![allow(non_snake_case)]

pub(crate) mod H {
    use libcrux_sha3::portable::{incremental, shake256, KeccakState1};

    const BLOCK_SIZE: usize = 136;

    pub(crate) fn one_shot<const OUTPUT_LENGTH: usize>(input: &[u8]) -> [u8; OUTPUT_LENGTH] {
        let mut out = [0u8; OUTPUT_LENGTH];
        shake256(&mut out, input);

        out
    }

    #[inline(always)]
    pub(crate) fn new(seed: &[u8]) -> KeccakState1 {
        let mut state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, &seed);

        state
    }

    #[inline(always)]
    pub(crate) fn squeeze_first_block(state: &mut KeccakState1) -> [u8; BLOCK_SIZE] {
        let mut out = [0u8; BLOCK_SIZE];
        incremental::shake256_squeeze_first_block(state, &mut out);

        out
    }

    #[inline(always)]
    pub(crate) fn squeeze_next_block(state: &mut KeccakState1) -> [u8; BLOCK_SIZE] {
        let mut out = [0u8; BLOCK_SIZE];
        incremental::shake256_squeeze_next_block(state, &mut out);

        out
    }
}

pub(crate) mod H_128 {
    use libcrux_sha3::portable::{incremental, KeccakState1};

    const BLOCK_SIZE: usize = 168;
    const FIVE_BLOCKS_SIZE: usize = BLOCK_SIZE * 5;

    #[inline(always)]
    pub(crate) fn new(seed: [u8; 34]) -> KeccakState1 {
        let mut state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, &seed);

        state
    }

    #[inline(always)]
    pub(crate) fn squeeze_first_five_blocks(state: &mut KeccakState1) -> [u8; FIVE_BLOCKS_SIZE] {
        let mut out = [0u8; FIVE_BLOCKS_SIZE];
        incremental::shake128_squeeze_first_five_blocks(state, &mut out);

        out
    }

    #[inline(always)]
    pub(crate) fn squeeze_next_block(state: &mut KeccakState1) -> [u8; BLOCK_SIZE] {
        let mut out = [0u8; BLOCK_SIZE];
        incremental::shake128_squeeze_next_block(state, &mut out);

        out
    }
}
