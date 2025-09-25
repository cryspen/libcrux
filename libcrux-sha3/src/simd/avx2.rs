use crate::{generic_keccak::KeccakState, traits::*};
use libcrux_intrinsics::avx2::*;

#[cfg(hax)]
use hax_lib::int::*;

#[inline(always)]
#[hax_lib::requires(
    LEFT.to_int() + RIGHT.to_int() == 64.to_int() &&
    RIGHT > 0 &&
    RIGHT < 64
)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: Vec256) -> Vec256 {
    debug_assert!(LEFT + RIGHT == 64);
    debug_assert!(RIGHT > 0);
    debug_assert!(RIGHT < 64);
    // This could be done more efficiently, if the shift values are multiples of 8.
    // However, in SHA-3 this function is only called twice with such inputs (8/56).
    mm256_xor_si256(mm256_slli_epi64::<LEFT>(x), mm256_srli_epi64::<RIGHT>(x))
}

#[inline(always)]
fn _veor5q_u64(a: Vec256, b: Vec256, c: Vec256, d: Vec256, e: Vec256) -> Vec256 {
    let ab = mm256_xor_si256(a, b);
    let cd = mm256_xor_si256(c, d);
    let abcd = mm256_xor_si256(ab, cd);
    mm256_xor_si256(abcd, e)
}

#[inline(always)]
fn _vrax1q_u64(a: Vec256, b: Vec256) -> Vec256 {
    mm256_xor_si256(a, rotate_left::<1, 63>(b))
}

#[inline(always)]
#[hax_lib::requires(
    LEFT.to_int() + RIGHT.to_int() == 64.to_int() &&
    RIGHT > 0 &&
    RIGHT < 64
)]
fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: Vec256, b: Vec256) -> Vec256 {
    let ab = mm256_xor_si256(a, b);
    rotate_left::<LEFT, RIGHT>(ab)
}

#[inline(always)]
fn _vbcaxq_u64(a: Vec256, b: Vec256, c: Vec256) -> Vec256 {
    mm256_xor_si256(a, mm256_andnot_si256(c, b))
}

#[inline(always)]
fn _veorq_n_u64(a: Vec256, c: u64) -> Vec256 {
    // Casting here is required, doesn't change the value.
    let c = mm256_set1_epi64x(c as i64);
    mm256_xor_si256(a, c)
}

#[inline(always)]
#[hax_lib::requires(
    RATE <= 200 &&
    RATE % 8 == 0 &&
    (RATE % 32 == 8 || RATE % 32 == 16) &&
    offset.to_int() + RATE.to_int() <= blocks[0].len().to_int() &&
    blocks[0].len() == blocks[1].len() &&
    blocks[0].len() == blocks[2].len() &&
    blocks[0].len() == blocks[3].len()
)]
pub(crate) fn load_block<const RATE: usize>(
    state: &mut [Vec256; 25],
    blocks: &[&[u8]; 4],
    offset: usize,
) {
    debug_assert!(offset + RATE <= blocks[0].len());
    debug_assert!(RATE % 8 == 0);
    debug_assert!(RATE % 32 == 8 || RATE % 32 == 16);

    for i in 0..RATE / 32 {
        let start = offset + 32 * i;
        let v0 = mm256_loadu_si256_u8(&blocks[0][start..start + 32]);
        let v1 = mm256_loadu_si256_u8(&blocks[1][start..start + 32]);
        let v2 = mm256_loadu_si256_u8(&blocks[2][start..start + 32]);
        let v3 = mm256_loadu_si256_u8(&blocks[3][start..start + 32]);

        let v0l = mm256_unpacklo_epi64(v0, v1); // 0 0 2 2
        let v1h = mm256_unpackhi_epi64(v0, v1); // 1 1 3 3
        let v2l = mm256_unpacklo_epi64(v2, v3); // 0 0 2 2
        let v3h = mm256_unpackhi_epi64(v2, v3); // 1 1 3 3

        let v0 = mm256_permute2x128_si256::<0x20>(v0l, v2l); // 0 0 0 0
        let v1 = mm256_permute2x128_si256::<0x20>(v1h, v3h); // 1 1 1 1
        let v2 = mm256_permute2x128_si256::<0x31>(v0l, v2l); // 2 2 2 2
        let v3 = mm256_permute2x128_si256::<0x31>(v1h, v3h); // 3 3 3 3

        let i0 = (4 * i) / 5;
        let j0 = (4 * i) % 5;
        let i1 = (4 * i + 1) / 5;
        let j1 = (4 * i + 1) % 5;
        let i2 = (4 * i + 2) / 5;
        let j2 = (4 * i + 2) % 5;
        let i3 = (4 * i + 3) / 5;
        let j3 = (4 * i + 3) % 5;

        set_ij(state, i0, j0, mm256_xor_si256(*get_ij(state, i0, j0), v0));
        set_ij(state, i1, j1, mm256_xor_si256(*get_ij(state, i1, j1), v1));
        set_ij(state, i2, j2, mm256_xor_si256(*get_ij(state, i2, j2), v2));
        set_ij(state, i3, j3, mm256_xor_si256(*get_ij(state, i3, j3), v3));
    }

    let rem = RATE % 32; // has to be 8 or 16
    let start = offset + 32 * (RATE / 32);
    let mut u8s = [0u8; 32];
    u8s[0..8].copy_from_slice(&blocks[0][start..start + 8]);
    u8s[8..16].copy_from_slice(&blocks[1][start..start + 8]);
    u8s[16..24].copy_from_slice(&blocks[2][start..start + 8]);
    u8s[24..32].copy_from_slice(&blocks[3][start..start + 8]);
    let u = mm256_loadu_si256_u8(u8s.as_slice());
    let i = (4 * (RATE / 32)) / 5;
    let j = (4 * (RATE / 32)) % 5;
    set_ij(state, i, j, mm256_xor_si256(*get_ij(state, i, j), u));
    if rem == 16 {
        let mut u8s = [0u8; 32];
        u8s[0..8].copy_from_slice(&blocks[0][start + 8..start + 16]);
        u8s[8..16].copy_from_slice(&blocks[1][start + 8..start + 16]);
        u8s[16..24].copy_from_slice(&blocks[2][start + 8..start + 16]);
        u8s[24..32].copy_from_slice(&blocks[3][start + 8..start + 16]);
        let u = mm256_loadu_si256_u8(u8s.as_slice());
        let i = (4 * (RATE / 32) + 1) / 5;
        let j = (4 * (RATE / 32) + 1) % 5;
        set_ij(state, i, j, mm256_xor_si256(*get_ij(state, i, j), u));
    }
}

#[inline(always)]
#[hax_lib::requires(
    RATE <= 200 &&
    RATE % 8 == 0 &&
    (RATE % 32 == 8 || RATE % 32 == 16) &&
    len < RATE &&
    start.to_int() + len.to_int() <= blocks[0].len().to_int() &&
    blocks[0].len() == blocks[1].len() &&
    blocks[0].len() == blocks[2].len() &&
    blocks[0].len() == blocks[3].len()
)]
pub(crate) fn load_last<const RATE: usize, const DELIMITER: u8>(
    state: &mut [Vec256; 25],
    blocks: &[&[u8]; 4],
    start: usize,
    len: usize,
) {
    let mut buffers = [[0u8; RATE]; 4];
    for i in 0..4 {
        buffers[i][0..len].copy_from_slice(&blocks[i][start..start + len]);
        buffers[i][len] = DELIMITER;
        buffers[i][RATE - 1] |= 0x80;
    }

    load_block::<RATE>(
        state,
        &[
            &buffers[0] as &[u8],
            &buffers[1] as &[u8],
            &buffers[2] as &[u8],
            &buffers[3] as &[u8],
        ],
        0,
    );
}

#[inline(always)]
#[hax_lib::requires(
    len <= 200 &&
    start.to_int() + len.to_int() <= out0.len().to_int() &&
    out0.len() == out1.len() &&
    out0.len() == out2.len() &&
    out0.len() == out3.len()
)]
#[hax_lib::ensures(|_|
    future(out0).len() == out0.len() &&
    future(out1).len() == out1.len() &&
    future(out2).len() == out2.len() &&
    future(out3).len() == out3.len()
)]
pub(crate) fn store_block<const RATE: usize>(
    s: &[Vec256; 25],
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
    start: usize,
    len: usize,
) {
    let chunks = len / 32;

    #[cfg(hax)]
    let (out0_len, out1_len, out2_len, out3_len) = (out0.len(), out1.len(), out2.len(), out3.len());

    for i in 0..chunks {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|_: usize| out0.len() == out0_len
            && out1.len() == out1_len
            && out2.len() == out2_len
            && out3.len() == out3_len);

        let i0 = (4 * i) / 5;
        let j0 = (4 * i) % 5;
        let i1 = (4 * i + 1) / 5;
        let j1 = (4 * i + 1) % 5;
        let i2 = (4 * i + 2) / 5;
        let j2 = (4 * i + 2) % 5;
        let i3 = (4 * i + 3) / 5;
        let j3 = (4 * i + 3) % 5;

        let v0l = mm256_permute2x128_si256::<0x20>(*get_ij(s, i0, j0), *get_ij(s, i2, j2)); // 0 0 2 2
        let v1h = mm256_permute2x128_si256::<0x20>(*get_ij(s, i1, j1), *get_ij(s, i3, j3)); // 1 1 3 3
        let v2l = mm256_permute2x128_si256::<0x31>(*get_ij(s, i0, j0), *get_ij(s, i2, j2)); // 0 0 2 2
        let v3h = mm256_permute2x128_si256::<0x31>(*get_ij(s, i1, j1), *get_ij(s, i3, j3)); // 1 1 3 3

        let v0 = mm256_unpacklo_epi64(v0l, v1h); // 0 1 2 3
        let v1 = mm256_unpackhi_epi64(v0l, v1h); // 0 1 2 3
        let v2 = mm256_unpacklo_epi64(v2l, v3h); // 0 1 2 3
        let v3 = mm256_unpackhi_epi64(v2l, v3h); // 0 1 2 3

        let base = start + 32 * i;
        let limit = base + 32;

        mm256_storeu_si256_u8(&mut out0[base..limit], v0);
        mm256_storeu_si256_u8(&mut out1[base..limit], v1);
        mm256_storeu_si256_u8(&mut out2[base..limit], v2);
        mm256_storeu_si256_u8(&mut out3[base..limit], v3);
    }

    let rem = len % 32;
    if rem > 0 {
        let mut tmp = [0u8; 32];
        let chunks8 = rem / 8;

        for k in 0..chunks8 {
            hax_lib::loop_invariant!(|_: usize| out0.len() == out0_len
                && out1.len() == out1_len
                && out2.len() == out2_len
                && out3.len() == out3_len);

            let idx = 4 * chunks + k;
            let i = idx / 5;
            let j = idx % 5;

            mm256_storeu_si256_u8(&mut tmp, *get_ij(s, i, j));

            let base = start + 32 * chunks + 8 * k;
            let limit = base + 8;

            out0[base..limit].copy_from_slice(&tmp[0..8]);
            out1[base..limit].copy_from_slice(&tmp[8..16]);
            out2[base..limit].copy_from_slice(&tmp[16..24]);
            out3[base..limit].copy_from_slice(&tmp[24..32]);
        }

        let rem8 = rem % 8;
        if rem8 > 0 {
            let idx = 4 * chunks + chunks8;
            let i = idx / 5;
            let j = idx % 5;

            mm256_storeu_si256_u8(&mut tmp, *get_ij(s, i, j));

            let limit = start + len;
            let base = limit - rem8;

            out0[base..limit].copy_from_slice(&tmp[0..rem8]);
            out1[base..limit].copy_from_slice(&tmp[8..8 + rem8]);
            out2[base..limit].copy_from_slice(&tmp[16..16 + rem8]);
            out3[base..limit].copy_from_slice(&tmp[24..24 + rem8]);
        }
    }
}

#[hax_lib::attributes]
impl KeccakItem<4> for Vec256 {
    #[inline(always)]
    fn zero() -> Self {
        mm256_set1_epi64x(0)
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
    #[hax_lib::requires(
        LEFT.to_int() + RIGHT.to_int() == 64.to_int() &&
        RIGHT > 0 &&
        RIGHT < 64
    )]
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
        mm256_xor_si256(a, b)
    }
}

#[hax_lib::attributes]
impl Absorb<4> for KeccakState<4, Vec256> {
    #[hax_lib::requires(
        RATE <= 200 &&
        RATE % 8 == 0 &&
        (RATE % 32 == 8 || RATE % 32 == 16) &&
        start.to_int() + RATE.to_int() <= input[0].len().to_int() &&
        input[0].len() == input[1].len() &&
        input[0].len() == input[2].len() &&
        input[0].len() == input[3].len()
    )]
    fn load_block<const RATE: usize>(&mut self, input: &[&[u8]; 4], start: usize) {
        load_block::<RATE>(&mut self.st, input, start);
    }

    #[hax_lib::requires(
        RATE <= 200 &&
        RATE % 8 == 0 &&
        (RATE % 32 == 8 || RATE % 32 == 16) &&
        len < RATE &&
        start.to_int() + len.to_int() <= input[0].len().to_int() &&
        input[0].len() == input[1].len() &&
        input[0].len() == input[2].len() &&
        input[0].len() == input[3].len()
    )]
    fn load_last<const RATE: usize, const DELIMITER: u8>(
        &mut self,
        input: &[&[u8]; 4],
        start: usize,
        len: usize,
    ) {
        load_last::<RATE, DELIMITER>(&mut self.st, input, start, len)
    }
}

#[hax_lib::attributes]
impl Squeeze4<Vec256> for KeccakState<4, Vec256> {
    #[hax_lib::requires(
        len <= 200 &&
        start.to_int() + len.to_int() <= out0.len().to_int() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    fn squeeze4<const RATE: usize>(
        &self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
        start: usize,
        len: usize,
    ) {
        store_block::<RATE>(&self.st, out0, out1, out2, out3, start, len)
    }
}
