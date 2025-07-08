use crate::{generic_keccak::KeccakState, traits::*};
use libcrux_intrinsics::avx2::*;
use libcrux_secrets::{
    Classify, ClassifyRef, Declassify as _, DeclassifyRef, DeclassifyRefMut, Secret,
};

#[inline(always)]
fn rotate_left<const LEFT: i32, const RIGHT: i32>(x: Vec256) -> Vec256 {
    debug_assert!(LEFT + RIGHT == 64);
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
pub(crate) fn load_block<const RATE: usize>(
    state: &mut [Secret<Vec256>; 25],
    blocks: &[&[Secret<u8>]; 4],
    offset: usize,
) {
    debug_assert!(RATE <= blocks[0].len() && RATE % 8 == 0 && (RATE % 32 == 8 || RATE % 32 == 16));
    for i in 0..RATE / 32 {
        let start = offset + 32 * i;
        let v0 = mm256_loadu_si256_u8(blocks[0][start..start + 32].declassify_ref());
        let v1 = mm256_loadu_si256_u8(blocks[1][start..start + 32].declassify_ref());
        let v2 = mm256_loadu_si256_u8(blocks[2][start..start + 32].declassify_ref());
        let v3 = mm256_loadu_si256_u8(blocks[3][start..start + 32].declassify_ref());

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

        set_ij(
            state,
            i0,
            j0,
            mm256_xor_si256(get_ij(state, i0, j0).declassify(), v0).classify(),
        );
        set_ij(
            state,
            i1,
            j1,
            mm256_xor_si256(get_ij(state, i1, j1).declassify(), v1).classify(),
        );
        set_ij(
            state,
            i2,
            j2,
            mm256_xor_si256(get_ij(state, i2, j2).declassify(), v2).classify(),
        );
        set_ij(
            state,
            i3,
            j3,
            mm256_xor_si256(get_ij(state, i3, j3).declassify(), v3).classify(),
        );
    }

    let rem = RATE % 32; // has to be 8 or 16
    let start = offset + 32 * (RATE / 32);
    let mut u8s = [0u8; 32];
    u8s[0..8].copy_from_slice(blocks[0][start..start + 8].declassify_ref());
    u8s[8..16].copy_from_slice(blocks[1][start..start + 8].declassify_ref());
    u8s[16..24].copy_from_slice(blocks[2][start..start + 8].declassify_ref());
    u8s[24..32].copy_from_slice(blocks[3][start..start + 8].declassify_ref());
    let u = mm256_loadu_si256_u8(u8s.as_slice());
    let i = (4 * (RATE / 32)) / 5;
    let j = (4 * (RATE / 32)) % 5;
    set_ij(
        state,
        i,
        j,
        mm256_xor_si256(get_ij(state, i, j).declassify(), u).classify(),
    );
    if rem == 16 {
        let mut u8s = [0u8; 32];
        u8s[0..8].copy_from_slice(blocks[0][start + 8..start + 16].declassify_ref());
        u8s[8..16].copy_from_slice(blocks[1][start + 8..start + 16].declassify_ref());
        u8s[16..24].copy_from_slice(blocks[2][start + 8..start + 16].declassify_ref());
        u8s[24..32].copy_from_slice(blocks[3][start + 8..start + 16].declassify_ref());
        let u = mm256_loadu_si256_u8(u8s.as_slice());
        let i = (4 * (RATE / 32) + 1) / 5;
        let j = (4 * (RATE / 32) + 1) % 5;
        set_ij(
            state,
            i,
            j,
            mm256_xor_si256(get_ij(state, i, j).declassify(), u).classify(),
        );
    }
}

#[inline(always)]
pub(crate) fn load_last<const RATE: usize, const DELIMITER: u8>(
    state: &mut [Secret<Vec256>; 25],
    blocks: &[&[Secret<u8>]; 4],
    start: usize,
    len: usize,
) {
    let mut buffers = [[0u8; RATE]; 4];
    for i in 0..4 {
        buffers[i][0..len].copy_from_slice(&blocks[i][start..start + len].declassify_ref());
        buffers[i][len] = DELIMITER;
        buffers[i][RATE - 1] |= 0x80;
    }

    load_block::<RATE>(
        state,
        &[
            (&buffers[0] as &[u8]).classify_ref(),
            (&buffers[1] as &[u8]).classify_ref(),
            (&buffers[2] as &[u8]).classify_ref(),
            (&buffers[3] as &[u8]).classify_ref(),
        ],
        0,
    );
}

#[inline(always)]
pub(crate) fn store_block<const RATE: usize>(
    s: &[Secret<Vec256>; 25],
    out0: &mut [Secret<u8>],
    out1: &mut [Secret<u8>],
    out2: &mut [Secret<u8>],
    out3: &mut [Secret<u8>],
    start: usize,
    len: usize,
) {
    let chunks = len / 32;
    for i in 0..chunks {
        let i0 = (4 * i) / 5;
        let j0 = (4 * i) % 5;
        let i1 = (4 * i + 1) / 5;
        let j1 = (4 * i + 1) % 5;
        let i2 = (4 * i + 2) / 5;
        let j2 = (4 * i + 2) % 5;
        let i3 = (4 * i + 3) / 5;
        let j3 = (4 * i + 3) % 5;

        let v0l = mm256_permute2x128_si256::<0x20>(
            get_ij(s, i0, j0).declassify(),
            get_ij(s, i2, j2).declassify(),
        );
        // 0 0 2 2
        let v1h = mm256_permute2x128_si256::<0x20>(
            get_ij(s, i1, j1).declassify(),
            get_ij(s, i3, j3).declassify(),
        ); // 1 1 3 3
        let v2l = mm256_permute2x128_si256::<0x31>(
            get_ij(s, i0, j0).declassify(),
            get_ij(s, i2, j2).declassify(),
        ); // 0 0 2 2
        let v3h = mm256_permute2x128_si256::<0x31>(
            get_ij(s, i1, j1).declassify(),
            get_ij(s, i3, j3).declassify(),
        ); // 1 1 3 3

        let v0 = mm256_unpacklo_epi64(v0l, v1h); // 0 1 2 3
        let v1 = mm256_unpackhi_epi64(v0l, v1h); // 0 1 2 3
        let v2 = mm256_unpacklo_epi64(v2l, v3h); // 0 1 2 3
        let v3 = mm256_unpackhi_epi64(v2l, v3h); // 0 1 2 3

        mm256_storeu_si256_u8(
            out0[start + 32 * i..start + 32 * (i + 1)].declassify_ref_mut(),
            v0,
        );
        mm256_storeu_si256_u8(
            out1[start + 32 * i..start + 32 * (i + 1)].declassify_ref_mut(),
            v1,
        );
        mm256_storeu_si256_u8(
            out2[start + 32 * i..start + 32 * (i + 1)].declassify_ref_mut(),
            v2,
        );
        mm256_storeu_si256_u8(
            out3[start + 32 * i..start + 32 * (i + 1)].declassify_ref_mut(),
            v3,
        );
    }

    let rem = len % 32;
    if rem > 0 {
        let start = start + 32 * chunks;
        let mut u8s = [0u8; 32].classify();
        let chunks8 = rem / 8;
        for k in 0..chunks8 {
            let i = (4 * chunks + k) / 5;
            let j = (4 * chunks + k) % 5;
            mm256_storeu_si256_u8(u8s.declassify_ref_mut(), get_ij(s, i, j).declassify());
            out0[start + 8 * k..start + 8 * (k + 1)].copy_from_slice(&u8s[0..8]);
            out1[start + 8 * k..start + 8 * (k + 1)].copy_from_slice(&u8s[8..16]);
            out2[start + 8 * k..start + 8 * (k + 1)].copy_from_slice(&u8s[16..24]);
            out3[start + 8 * k..start + 8 * (k + 1)].copy_from_slice(&u8s[24..32]);
        }
        let rem8 = rem % 8;
        if rem8 > 0 {
            let i = (4 * chunks + chunks8) / 5;
            let j = (4 * chunks + chunks8) % 5;
            mm256_storeu_si256_u8(u8s.declassify_ref_mut(), get_ij(s, i, j).declassify());
            out0[start + len - rem8..start + len].copy_from_slice(&u8s[0..rem]);
            out1[start + len - rem8..start + len].copy_from_slice(&u8s[8..8 + rem]);
            out2[start + len - rem8..start + len].copy_from_slice(&u8s[16..16 + rem]);
            out3[start + len - rem8..start + len].copy_from_slice(&u8s[24..24 + rem]);
        }
    }
}

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

impl Absorb<4> for KeccakState<4, Vec256> {
    fn load_block<const RATE: usize>(&mut self, input: &[&[Secret<u8>]; 4], start: usize) {
        load_block::<RATE>(&mut self.st, input, start);
    }

    fn load_last<const RATE: usize, const DELIMITER: u8>(
        &mut self,
        input: &[&[Secret<u8>]; 4],
        start: usize,
        len: usize,
    ) {
        load_last::<RATE, DELIMITER>(&mut self.st, input, start, len)
    }
}

impl Squeeze4<Vec256> for KeccakState<4, Vec256> {
    fn squeeze<const RATE: usize>(
        &self,
        out0: &mut [Secret<u8>],
        out1: &mut [Secret<u8>],
        out2: &mut [Secret<u8>],
        out3: &mut [Secret<u8>],
        start: usize,
        len: usize,
    ) {
        store_block::<RATE>(&self.st, out0, out1, out2, out3, start, len)
    }
}
