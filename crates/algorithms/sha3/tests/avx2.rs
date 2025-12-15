#![cfg(feature = "simd256")]

mod test_vectors;

use crate::test_vectors::{
    DIGEST_LEN_SHAKE128, DIGEST_LEN_SHAKE256, STRING_LEN_SHAKE128, STRING_LEN_SHAKE256,
};
use libcrux_sha3::avx2::x4::incremental;

#[test]
fn sha3_shake128_squeeze_first_three_next_block() {
    let mut state = incremental::init();

    incremental::shake128_absorb_final(
        &mut state,
        test_vectors::STAR0,
        test_vectors::STAR1,
        test_vectors::STAR2,
        test_vectors::STAR3,
    );

    let mut out0 = [0u8; DIGEST_LEN_SHAKE128 * 3];
    let mut out1 = [0u8; DIGEST_LEN_SHAKE128 * 3];
    let mut out2 = [0u8; DIGEST_LEN_SHAKE128 * 3];
    let mut out3 = [0u8; DIGEST_LEN_SHAKE128 * 3];

    incremental::shake128_squeeze_first_three_blocks(
        &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
    );

    assert_eq!(
        hex::encode(&out0),
        test_vectors::shake128::STAR0_FIVE_BLOCKS[..STRING_LEN_SHAKE128 * 3]
    );
    assert_eq!(
        hex::encode(&out1),
        test_vectors::shake128::STAR1_FIVE_BLOCKS[..STRING_LEN_SHAKE128 * 3]
    );
    assert_eq!(
        hex::encode(&out2),
        test_vectors::shake128::STAR2_FIVE_BLOCKS[..STRING_LEN_SHAKE128 * 3]
    );
    assert_eq!(
        hex::encode(&out3),
        test_vectors::shake128::STAR3_FIVE_BLOCKS[..STRING_LEN_SHAKE128 * 3]
    );

    let mut out0 = [0u8; DIGEST_LEN_SHAKE128];
    let mut out1 = [0u8; DIGEST_LEN_SHAKE128];
    let mut out2 = [0u8; DIGEST_LEN_SHAKE128];
    let mut out3 = [0u8; DIGEST_LEN_SHAKE128];

    incremental::shake128_squeeze_next_block(
        &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
    );

    assert_eq!(
        hex::encode(&out0),
        test_vectors::shake128::STAR0_FIVE_BLOCKS[STRING_LEN_SHAKE128 * 3..STRING_LEN_SHAKE128 * 4]
    );
    assert_eq!(
        hex::encode(&out1),
        test_vectors::shake128::STAR1_FIVE_BLOCKS[STRING_LEN_SHAKE128 * 3..STRING_LEN_SHAKE128 * 4]
    );
    assert_eq!(
        hex::encode(&out2),
        test_vectors::shake128::STAR2_FIVE_BLOCKS[STRING_LEN_SHAKE128 * 3..STRING_LEN_SHAKE128 * 4]
    );
    assert_eq!(
        hex::encode(&out3),
        test_vectors::shake128::STAR3_FIVE_BLOCKS[STRING_LEN_SHAKE128 * 3..STRING_LEN_SHAKE128 * 4]
    );
}

#[test]
fn sha3_shake128_squeeze_first_five() {
    let mut state = incremental::init();

    incremental::shake128_absorb_final(
        &mut state,
        test_vectors::STAR0,
        test_vectors::STAR1,
        test_vectors::STAR2,
        test_vectors::STAR3,
    );

    let mut out0 = [0u8; DIGEST_LEN_SHAKE128 * 5];
    let mut out1 = [0u8; DIGEST_LEN_SHAKE128 * 5];
    let mut out2 = [0u8; DIGEST_LEN_SHAKE128 * 5];
    let mut out3 = [0u8; DIGEST_LEN_SHAKE128 * 5];

    incremental::shake128_squeeze_first_five_blocks(
        &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
    );

    assert_eq!(
        hex::encode(&out0),
        test_vectors::shake128::STAR0_FIVE_BLOCKS
    );
    assert_eq!(
        hex::encode(&out1),
        test_vectors::shake128::STAR1_FIVE_BLOCKS
    );
    assert_eq!(
        hex::encode(&out2),
        test_vectors::shake128::STAR2_FIVE_BLOCKS
    );
    assert_eq!(
        hex::encode(&out3),
        test_vectors::shake128::STAR3_FIVE_BLOCKS
    );
}

#[test]
fn sha3_shake256_squeeze_first_next() {
    let mut state = incremental::init();

    incremental::shake256_absorb_final(
        &mut state,
        test_vectors::STAR0,
        test_vectors::STAR1,
        test_vectors::STAR2,
        test_vectors::STAR3,
    );

    let mut out0 = [0u8; DIGEST_LEN_SHAKE256];
    let mut out1 = [0u8; DIGEST_LEN_SHAKE256];
    let mut out2 = [0u8; DIGEST_LEN_SHAKE256];
    let mut out3 = [0u8; DIGEST_LEN_SHAKE256];

    incremental::shake256_squeeze_first_block(
        &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
    );

    assert_eq!(
        hex::encode(&out0),
        test_vectors::shake256::STAR0_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
    );
    assert_eq!(
        hex::encode(&out1),
        test_vectors::shake256::STAR1_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
    );
    assert_eq!(
        hex::encode(&out2),
        test_vectors::shake256::STAR2_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
    );
    assert_eq!(
        hex::encode(&out3),
        test_vectors::shake256::STAR3_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
    );

    incremental::shake256_squeeze_next_block(
        &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
    );

    assert_eq!(
        hex::encode(&out0),
        test_vectors::shake256::STAR0_FIVE_BLOCKS[STRING_LEN_SHAKE256..STRING_LEN_SHAKE256 * 2]
    );
    assert_eq!(
        hex::encode(&out1),
        test_vectors::shake256::STAR1_FIVE_BLOCKS[STRING_LEN_SHAKE256..STRING_LEN_SHAKE256 * 2]
    );
    assert_eq!(
        hex::encode(&out2),
        test_vectors::shake256::STAR2_FIVE_BLOCKS[STRING_LEN_SHAKE256..STRING_LEN_SHAKE256 * 2]
    );
    assert_eq!(
        hex::encode(&out3),
        test_vectors::shake256::STAR3_FIVE_BLOCKS[STRING_LEN_SHAKE256..STRING_LEN_SHAKE256 * 2]
    );

    incremental::shake256_squeeze_next_block(
        &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
    );

    assert_eq!(
        hex::encode(&out0),
        test_vectors::shake256::STAR0_FIVE_BLOCKS[STRING_LEN_SHAKE256 * 2..STRING_LEN_SHAKE256 * 3]
    );
    assert_eq!(
        hex::encode(&out1),
        test_vectors::shake256::STAR1_FIVE_BLOCKS[STRING_LEN_SHAKE256 * 2..STRING_LEN_SHAKE256 * 3]
    );
    assert_eq!(
        hex::encode(&out2),
        test_vectors::shake256::STAR2_FIVE_BLOCKS[STRING_LEN_SHAKE256 * 2..STRING_LEN_SHAKE256 * 3]
    );
    assert_eq!(
        hex::encode(&out3),
        test_vectors::shake256::STAR3_FIVE_BLOCKS[STRING_LEN_SHAKE256 * 2..STRING_LEN_SHAKE256 * 3]
    );
}
