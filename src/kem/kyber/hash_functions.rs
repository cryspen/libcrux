#![allow(non_snake_case)]

use crate::digest::{self, digest_size, Algorithm};

use super::constants::H_DIGEST_SIZE;

pub(crate) fn G(input: &[u8]) -> [u8; digest_size(Algorithm::Sha3_512)] {
    digest::sha3_512(input)
}

pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    digest::sha3_256(input)
}

pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake256::<LEN>(input)
}

// The following API uses the repeated squeeze API
// The first version uses Scalar SHAKE 128
pub(crate) enum XofState {
    X2(digest::Shake128StateX2),
    X3(digest::Shake128StateX3),
    X4(digest::Shake128StateX4),
}

#[inline(always)]
pub(crate) fn XOF_absorb<const K: usize>(input: [[u8; 34]; K]) -> XofState {
    match K as u8 {
        2 => {
            let mut state = digest::shake128_init_x2();
            digest::shake128_absorb_final_x2(&mut state, &input[0], &input[1]);
            XofState::X2(state)
        }
        3 => {
            let mut state = digest::shake128_init_x3();
            digest::shake128_absorb_final_x3(&mut state, &input[0], &input[1], &input[2]);
            XofState::X3(state)
        }
        4 => {
            let mut state = digest::shake128_init_x4();
            digest::shake128_absorb_final_x4(
                &mut state, &input[0], &input[1], &input[2], &input[3],
            );
            XofState::X4(state)
        }
        _ => unreachable!(),
    }
}

#[inline(always)]
pub(crate) fn XOF_squeeze_three_blocks<const K: usize>(
    xof_state: XofState,
) -> ([[u8; 168 * 3]; K], XofState) {
    let mut output = [[0; 168 * 3]; K];
    match K as u8 {
        2 => {
            if let XofState::X2(mut st) = xof_state {
                let tmp = digest::shake128_squeeze_nblocks_x2::<504>(&mut st);
                output[0] = tmp[0];
                output[1] = tmp[1];
                (output, XofState::X2(st))
            } else {
                unreachable!()
            }
        }
        3 => {
            if let XofState::X3(mut st) = xof_state {
                let tmp = digest::shake128_squeeze_nblocks_x3::<504>(&mut st);
                output[0] = tmp[0];
                output[1] = tmp[1];
                output[2] = tmp[2];
                (output, XofState::X3(st))
            } else {
                unreachable!()
            }
        }
        4 => {
            if let XofState::X4(mut st) = xof_state {
                let tmp = digest::shake128_squeeze_nblocks_x4::<504>(&mut st);
                output[0] = tmp[0];
                output[1] = tmp[1];
                output[2] = tmp[2];
                output[3] = tmp[3];
                (output, XofState::X4(st))
            } else {
                unreachable!()
            }
        }
        _ => unreachable!(),
    }
}

#[inline(always)]
pub(crate) fn XOF_squeeze_block<const K: usize>(xof_state: XofState) -> ([[u8; 168]; K], XofState) {
    let mut output = [[0; 168]; K];
    match K as u8 {
        2 => {
            if let XofState::X2(mut st) = xof_state {
                let tmp = digest::shake128_squeeze_nblocks_x2::<168>(&mut st);
                output[0] = tmp[0];
                output[1] = tmp[1];
                (output, XofState::X2(st))
            } else {
                unreachable!()
            }
        }
        3 => {
            if let XofState::X3(mut st) = xof_state {
                let tmp = digest::shake128_squeeze_nblocks_x3::<168>(&mut st);
                output[0] = tmp[0];
                output[1] = tmp[1];
                output[2] = tmp[2];
                (output, XofState::X3(st))
            } else {
                unreachable!()
            }
        }
        4 => {
            if let XofState::X4(mut st) = xof_state {
                let tmp = digest::shake128_squeeze_nblocks_x4::<168>(&mut st);
                output[0] = tmp[0];
                output[1] = tmp[1];
                output[2] = tmp[2];
                output[3] = tmp[3];
                (output, XofState::X4(st))
            } else {
                unreachable!()
            }
        }
        _ => unreachable!(),
    }
}
