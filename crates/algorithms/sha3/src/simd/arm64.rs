#[cfg(hax)]
use hax_lib::int::ToInt;

#[cfg(hax)]
use hax_lib::prop::*;

#[cfg(hax)]
use crate::proof_utils::valid_rate;

use libcrux_intrinsics::arm64::*;

use crate::{generic_keccak::KeccakState, traits::*};

#[allow(non_camel_case_types)]
pub type uint64x2_t = _uint64x2_t;

#[inline(always)]
fn _veor5q_u64(
    a: uint64x2_t,
    b: uint64x2_t,
    c: uint64x2_t,
    d: uint64x2_t,
    e: uint64x2_t,
) -> uint64x2_t {
    _veor3q_u64(_veor3q_u64(a, b, c), d, e)
}

#[inline(always)]
fn _vrax1q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    libcrux_intrinsics::arm64::_vrax1q_u64(a, b)
}

#[inline(always)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    libcrux_intrinsics::arm64::_vxarq_u64::<LEFT, RIGHT>(a, b)
}

#[inline(always)]
fn _vbcaxq_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    libcrux_intrinsics::arm64::_vbcaxq_u64(a, b, c)
}

#[inline(always)]
fn _veorq_n_u64(a: uint64x2_t, c: u64) -> uint64x2_t {
    let c = _vdupq_n_u64(c);
    _veorq_u64(a, c)
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 1000 --split_queries no")]
#[hax_lib::requires(valid_rate(RATE)
            && blocks[0].len() == blocks[1].len()
            && offset.to_int() + RATE.to_int() <= blocks[0].len().to_int()
)]
#[hax_lib::ensures(|_| hax_lib::forall(|i: usize|
    if i < 25 {
        if i < RATE / 8 {
            get_lane_u64(future(state)[i], 0)
                == get_lane_u64(state[i], 0)
                   ^ u64::from_le_bytes(blocks[0][offset + 8 * i..offset + 8 * i + 8].try_into().unwrap())
            && get_lane_u64(future(state)[i], 1)
                == get_lane_u64(state[i], 1)
                   ^ u64::from_le_bytes(blocks[1][offset + 8 * i..offset + 8 * i + 8].try_into().unwrap())
        } else {
            get_lane_u64(future(state)[i], 0) == get_lane_u64(state[i], 0)
            && get_lane_u64(future(state)[i], 1) == get_lane_u64(state[i], 1)
        }
    } else { true }
))]
pub(crate) fn load_block<const RATE: usize>(
    state: &mut [uint64x2_t; 25],
    blocks: &[&[u8]; 2],
    offset: usize,
) {
    #[cfg(hax)]
    let old_state = *state; // ghost variable

    for i in 0..RATE / 16 {
        hax_lib::loop_invariant!(|i: usize| hax_lib::forall(|j: usize| if j < RATE / 16 {
            if j < 2 * i {
                get_lane_u64(state[j], 0)
                    == get_lane_u64(old_state[j], 0)
                        ^ u64::from_le_bytes(
                            blocks[0][offset + 8 * j..offset + 8 * j + 8]
                                .try_into()
                                .unwrap(),
                        )
                    && get_lane_u64(state[j], 1)
                        == get_lane_u64(old_state[j], 1)
                            ^ u64::from_le_bytes(
                                blocks[1][offset + 8 * j..offset + 8 * j + 8]
                                    .try_into()
                                    .unwrap(),
                            )
            } else {
                get_lane_u64(state[j], 0) == get_lane_u64(old_state[j], 0)
                    && get_lane_u64(state[j], 1) == get_lane_u64(old_state[j], 1)
            }
        } else {
            true
        }));
        hax_lib::assert!(RATE <= 200 && i < RATE / 16);
        let start = offset + 16 * i;
        let v0 = _vld1q_bytes_u64(&blocks[0][start..start + 16]);
        let v1 = _vld1q_bytes_u64(&blocks[1][start..start + 16]);
        let i0 = (2 * i) / 5;
        let j0 = (2 * i) % 5;
        let i1 = (2 * i + 1) / 5;
        let j1 = (2 * i + 1) % 5;
        set_ij(
            state,
            i0,
            j0,
            _veorq_u64(*get_ij(state, i0, j0), _vtrn1q_u64(v0, v1)),
        );
        set_ij(
            state,
            i1,
            j1,
            _veorq_u64(*get_ij(state, i1, j1), _vtrn2q_u64(v0, v1)),
        );
    }
    hax_lib::fstar!("admit()");
    let remaining = RATE % 16;
    if remaining > 0 {
        let i = RATE / 8 - 1;
        let mut u = [0u64; 2];
        let start = offset + RATE - 8;
        u[0] = u64::from_le_bytes(blocks[0][start..start + 8].try_into().unwrap());
        u[1] = u64::from_le_bytes(blocks[1][start..start + 8].try_into().unwrap());
        let uvec = _vld1q_u64(&u);
        set_ij(
            state,
            i / 5,
            i % 5,
            _veorq_u64(*get_ij(state, i / 5, i % 5), uvec),
        );
    }
}

#[inline(always)]
#[hax_lib::requires(valid_rate(RATE) && len < RATE && offset.to_int() + len.to_int() <= blocks[0].len().to_int() && blocks[0].len() == blocks[1].len())]
pub(crate) fn load_last<const RATE: usize, const DELIMITER: u8>(
    state: &mut [uint64x2_t; 25],
    blocks: &[&[u8]; 2],
    offset: usize,
    len: usize,
) {
    #[cfg(not(eurydice))]
    debug_assert!(offset + len <= blocks[0].len() && blocks[0].len() == blocks[1].len());

    let mut buffer0 = [0u8; RATE];
    buffer0[0..len].copy_from_slice(&blocks[0][offset..offset + len]);
    buffer0[len] = DELIMITER;
    buffer0[RATE - 1] |= 0x80;

    let mut buffer1 = [0u8; RATE];
    buffer1[0..len].copy_from_slice(&blocks[1][offset..offset + len]);
    buffer1[len] = DELIMITER;
    buffer1[RATE - 1] |= 0x80;

    load_block::<RATE>(state, &[&buffer0, &buffer1], 0);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(valid_rate(RATE) && len <= RATE && start.to_int() + len.to_int() <= out0.len().to_int() && out0.len() == out1.len())]
#[hax_lib::ensures(|_| (future(out0).len() == out0.len()).to_prop()
    & (future(out1).len() == out1.len()).to_prop()
    & hax_lib::forall(|i: usize| if i < out0.len() {
        if i < start {
            out0[i] == future(out0)[i]
        } else if i < start + len {
            future(out0)[i] == get_lane_u64(s[(i - start) / 8], 0).to_le_bytes()[(i - start) % 8]
        } else {
            out0[i] == future(out0)[i]
        }
    } else {
        true
    })
    & hax_lib::forall(|i: usize| if i < out1.len() {
        if i < start {
            out1[i] == future(out1)[i]
        } else if i < start + len {
            future(out1)[i] == get_lane_u64(s[(i - start) / 8], 1).to_le_bytes()[(i - start) % 8]
        } else {
            out1[i] == future(out1)[i]
        }
    } else {
        true
    })
)]
pub(crate) fn store_block<const RATE: usize>(
    s: &[uint64x2_t; 25],
    out0: &mut [u8],
    out1: &mut [u8],
    start: usize,
    len: usize,
) {
    #[cfg(not(eurydice))]
    debug_assert!(len <= RATE && start + len <= out0.len() && out0.len() == out1.len());

    #[cfg(hax)]
    let old_out0 = out0.to_vec().as_slice(); // ghost variable
    #[cfg(hax)]
    let old_out1 = out1.to_vec().as_slice(); // ghost variable
    hax_lib::fstar!("admit()");

    for i in 0..len / 16 {
        hax_lib::loop_invariant!(|i: usize| (out0.len() == old_out0.len()).to_prop()
            & (out1.len() == old_out1.len()).to_prop()
            & hax_lib::forall(|j: usize| if j < out0.len() {
                if j < start {
                    out0[j] == old_out0[j]
                } else if j < start + i * 16 {
                    out0[j] == get_lane_u64(s[(j - start) / 8], 0).to_le_bytes()[(j - start) % 8]
                } else {
                    out0[j] == old_out0[j]
                }
            } else {
                true
            })
            & hax_lib::forall(|j: usize| if j < out1.len() {
                if j < start {
                    out1[j] == old_out1[j]
                } else if j < start + i * 16 {
                    out1[j] == get_lane_u64(s[(j - start) / 8], 1).to_le_bytes()[(j - start) % 8]
                } else {
                    out1[j] == old_out1[j]
                }
            } else {
                true
            }));
        let i0 = (2 * i) / 5;
        let j0 = (2 * i) % 5;
        let i1 = (2 * i + 1) / 5;
        let j1 = (2 * i + 1) % 5;
        let v0 = _vtrn1q_u64(*get_ij(s, i0, j0), *get_ij(s, i1, j1));
        let v1 = _vtrn2q_u64(*get_ij(s, i0, j0), *get_ij(s, i1, j1));
        _vst1q_bytes_u64(&mut out0[start + 16 * i..start + 16 * (i + 1)], v0);
        _vst1q_bytes_u64(&mut out1[start + 16 * i..start + 16 * (i + 1)], v1);
    }
    let remaining = len % 16;
    if remaining > 8 {
        let mut out0_tmp = [0u8; 16];
        let mut out1_tmp = [0u8; 16];
        let i = 2 * (len / 16);
        let i0 = i / 5;
        let j0 = i % 5;
        let i1 = (i + 1) / 5;
        let j1 = (i + 1) % 5;
        let v0 = _vtrn1q_u64(*get_ij(s, i0, j0), *get_ij(s, i1, j1));
        let v1 = _vtrn2q_u64(*get_ij(s, i0, j0), *get_ij(s, i1, j1));
        _vst1q_bytes_u64(&mut out0_tmp, v0);
        _vst1q_bytes_u64(&mut out1_tmp, v1);
        out0[start + len - remaining..start + len].copy_from_slice(&out0_tmp[0..remaining]);
        out1[start + len - remaining..start + len].copy_from_slice(&out1_tmp[0..remaining]);
    } else if remaining > 0 {
        let mut out01 = [0u8; 16];
        let i = 2 * (len / 16);
        _vst1q_bytes_u64(&mut out01, *get_ij(s, i / 5, i % 5));
        out0[start + len - remaining..start + len].copy_from_slice(&out01[0..remaining]);
        out1[start + len - remaining..start + len].copy_from_slice(&out01[8..8 + remaining]);
    }
}

impl KeccakItem<2> for uint64x2_t {
    #[inline(always)]
    fn zero() -> Self {
        _vdupq_n_u64(0)
    }
    #[inline(always)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
        _veor5q_u64(a, b, c, d, e)
    }
    #[inline(always)]
    fn rotate_left1_and_xor(a: Self, b: Self) -> Self {
        _vrax1q_u64(a, b)
    }
    #[inline(always)]
    fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self {
        _vxarq_u64::<LEFT, RIGHT>(a, b)
    }
    #[inline(always)]
    fn and_not_xor(a: Self, b: Self, c: Self) -> Self {
        _vbcaxq_u64(a, b, c)
    }
    #[inline(always)]
    fn xor_constant(a: Self, c: u64) -> Self {
        _veorq_n_u64(a, c)
    }
    #[inline(always)]
    fn xor(a: Self, b: Self) -> Self {
        _veorq_u64(a, b)
    }
}

#[hax_lib::attributes]
impl Absorb<2> for KeccakState<2, uint64x2_t> {
    #[hax_lib::requires(
        valid_rate(RATE) &&
        start.to_int() + RATE.to_int() <= input[0].len().to_int() &&
        input[0].len() == input[1].len()
    )]
    fn load_block<const RATE: usize>(&mut self, input: &[&[u8]; 2], start: usize) {
        load_block::<RATE>(&mut self.st, input, start);
    }

    #[hax_lib::requires(
        valid_rate(RATE) &&
        len < RATE &&
        start.to_int() + len.to_int() <= input[0].len().to_int() &&
        input[0].len() == input[1].len()
    )]
    fn load_last<const RATE: usize, const DELIMITER: u8>(
        &mut self,
        input: &[&[u8]; 2],
        start: usize,
        len: usize,
    ) {
        load_last::<RATE, DELIMITER>(&mut self.st, input, start, len);
    }
}

#[hax_lib::attributes]
impl Squeeze2<uint64x2_t> for KeccakState<2, uint64x2_t> {
    #[hax_lib::requires(
        valid_rate(RATE) &&
        len <= RATE &&
        start.to_int() + len.to_int() <= out0.len().to_int() &&
        out0.len() == out1.len()
    )]
    #[hax_lib::ensures(|_| future(out0).len() == out0.len() && future(out1).len() == out1.len())]
    fn squeeze2<const RATE: usize>(
        &self,
        out0: &mut [u8],
        out1: &mut [u8],
        start: usize,
        len: usize,
    ) {
        store_block::<RATE>(&self.st, out0, out1, start, len);
    }
}
