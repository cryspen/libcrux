#![cfg(feature = "simd128")]

mod test_vectors;

use crate::test_vectors::{DIGEST_LEN_SHAKE256, STRING_LEN_SHAKE256};

use libcrux_sha3::neon::x2::incremental::{
    init, shake256_absorb_final, shake256_squeeze_first_block,
};

const DIGEST_LEN_SHAKE256: usize = 136;
const STRING_LEN_SHAKE256: usize = DIGEST_LEN_SHAKE256 * 2;

#[test]
fn sha3_shake256_incremental() {
    // Test squeezing 1 block (136 bytes for SHAKE256, not 168)
    let mut state = init();
    shake256_absorb_final(&mut state, test_vectors::HELLO, test_vectors::HELLO);

    let mut digest0 = [0u8; DIGEST_LEN_SHAKE256];
    let mut digest1 = [0u8; DIGEST_LEN_SHAKE256];
    shake256_squeeze_first_block(&mut state, &mut digest0, &mut digest1);

    assert_eq!(hex::encode(digest0), hex::encode(digest1),);
    assert_eq!(
        hex::encode(digest0),
        &test_vectors::shake256::HELLO_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
    );
}
