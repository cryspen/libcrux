#![allow(clippy::needless_range_loop)]

use crate::aes_generic::AES_BLOCK_LEN;

pub(crate) type State = [u16; 8];

fn new_state() -> State {
    [0u16; 8]
}

#[inline]
fn interleave_u8_1(i0: u8, i1: u8) -> u16 {
    let mut x = i0 as u16;

    x = (x | (x << 4)) & 0x0F0F;
    x = (x | (x << 2)) & 0x3333;
    x = (x | (x << 1)) & 0x5555;

    let mut y = i1 as u16;

    y = (y | (y << 4)) & 0x0F0F;
    y = (y | (y << 2)) & 0x3333;
    y = (y | (y << 1)) & 0x5555;

    x | (y << 1)
}

#[inline]
fn deinterleave_u8_1(i0: u16) -> (u8, u8) {
    let mut x = i0 & 0x5555;

    x = (x | (x >> 1)) & 0x3333;
    x = (x | (x >> 2)) & 0x0F0F;
    x = (x | (x >> 4)) & 0x00FF;

    let mut y = (i0 >> 1) & 0x5555;

    y = (y | (y >> 1)) & 0x3333;
    y = (y | (y >> 2)) & 0x0F0F;
    y = (y | (y >> 4)) & 0x00FF;

    (x as u8, y as u8)
}

#[inline]
fn interleave_u16_2(i0: u16, i1: u16) -> (u16, u16) {
    let x = ((i1 & 0x3333) << 2) | (i0 & 0x3333);
    let y = ((i0 & 0xcccc) >> 2) | (i1 & 0xcccc);
    (x, y)
}

#[inline]
fn interleave_u16_4(i0: u16, i1: u16) -> (u16, u16) {
    let x = ((i1 & 0x0F0F) << 4) | (i0 & 0x0F0F);
    let y = ((i0 & 0xF0F0) >> 4) | (i1 & 0xF0F0);
    (x, y)
}

#[inline]
fn interleave_u16_8(i0: u16, i1: u16) -> (u16, u16) {
    let x = ((i1 & 0x00FF) << 8) | (i0 & 0x00FF);
    let y = ((i0 & 0xFF00) >> 8) | (i1 & 0xFF00);
    (x, y)
}

#[inline]
fn transpose_u8x16(input: &[u8; 16], output: &mut [u16; 8]) {
    let o0 = interleave_u8_1(input[0], input[1]);
    let o1 = interleave_u8_1(input[2], input[3]);
    let o2 = interleave_u8_1(input[4], input[5]);
    let o3 = interleave_u8_1(input[6], input[7]);
    let o4 = interleave_u8_1(input[8], input[9]);
    let o5 = interleave_u8_1(input[10], input[11]);
    let o6 = interleave_u8_1(input[12], input[13]);
    let o7 = interleave_u8_1(input[14], input[15]);

    let (o0, o1) = interleave_u16_2(o0, o1);
    let (o2, o3) = interleave_u16_2(o2, o3);
    let (o4, o5) = interleave_u16_2(o4, o5);
    let (o6, o7) = interleave_u16_2(o6, o7);

    let (o0, o2) = interleave_u16_4(o0, o2);
    let (o1, o3) = interleave_u16_4(o1, o3);
    let (o4, o6) = interleave_u16_4(o4, o6);
    let (o5, o7) = interleave_u16_4(o5, o7);

    let (o0, o4) = interleave_u16_8(o0, o4);
    let (o1, o5) = interleave_u16_8(o1, o5);
    let (o2, o6) = interleave_u16_8(o2, o6);
    let (o3, o7) = interleave_u16_8(o3, o7);

    output[0] = o0;
    output[1] = o1;
    output[2] = o2;
    output[3] = o3;
    output[4] = o4;
    output[5] = o5;
    output[6] = o6;
    output[7] = o7;
}

#[inline]
fn transpose_u16x8(input: &[u16; 8], output: &mut [u8]) {
    let (i0, i4) = interleave_u16_8(input[0], input[4]);
    let (i1, i5) = interleave_u16_8(input[1], input[5]);
    let (i2, i6) = interleave_u16_8(input[2], input[6]);
    let (i3, i7) = interleave_u16_8(input[3], input[7]);

    let (i0, i2) = interleave_u16_4(i0, i2);
    let (i1, i3) = interleave_u16_4(i1, i3);
    let (i4, i6) = interleave_u16_4(i4, i6);
    let (i5, i7) = interleave_u16_4(i5, i7);

    let (i0, i1) = interleave_u16_2(i0, i1);
    let (i2, i3) = interleave_u16_2(i2, i3);
    let (i4, i5) = interleave_u16_2(i4, i5);
    let (i6, i7) = interleave_u16_2(i6, i7);

    let (o0, o1) = deinterleave_u8_1(i0);
    let (o2, o3) = deinterleave_u8_1(i1);
    let (o4, o5) = deinterleave_u8_1(i2);
    let (o6, o7) = deinterleave_u8_1(i3);
    let (o8, o9) = deinterleave_u8_1(i4);

    let (o10, o11) = deinterleave_u8_1(i5);
    let (o12, o13) = deinterleave_u8_1(i6);
    let (o14, o15) = deinterleave_u8_1(i7);

    output[0] = o0;
    output[1] = o1;
    output[2] = o2;
    output[3] = o3;
    output[4] = o4;
    output[5] = o5;
    output[6] = o6;
    output[7] = o7;
    output[8] = o8;
    output[9] = o9;
    output[10] = o10;
    output[11] = o11;
    output[12] = o12;
    output[13] = o13;
    output[14] = o14;
    output[15] = o15;
}

#[inline]
fn xnor(a: u16, b: u16) -> u16 {
    !(a ^ b)
}

fn sub_bytes_state(st: &mut State) {
    let u0 = st[7];
    let u1 = st[6];
    let u2 = st[5];
    let u3 = st[4];
    let u4 = st[3];
    let u5 = st[2];
    let u6 = st[1];
    let u7 = st[0];

    let t1 = u6 ^ u4;
    let t2 = u3 ^ u0;
    let t3 = u1 ^ u2;
    let t4 = u7 ^ t3;
    let t5 = t1 ^ t2;
    let t6 = u1 ^ u5;
    let t7 = u0 ^ u6;
    let t8 = t1 ^ t6;
    let t9 = u6 ^ t4;
    let t10 = u3 ^ t4;
    let t11 = u7 ^ t5;
    let t12 = t5 ^ t6;
    let t13 = u2 ^ u5;
    let t14 = t3 ^ t5;
    let t15 = u5 ^ t7;
    let t16 = u0 ^ u5;
    let t17 = u7 ^ t8;
    let t18 = u6 ^ u5;
    let t19 = t2 ^ t18;
    let t20 = t4 ^ t15;
    let t21 = t1 ^ t13;
    let t22 = u0 ^ t4;
    let t39 = t21 ^ t5;
    let t40 = t21 ^ t7;
    let t41 = t7 ^ t19;
    let t42 = t16 ^ t14;
    let t43 = t22 ^ t17;
    let t44 = t19 & t5;
    let t45 = t20 & t11;
    let t46 = t12 ^ t44;
    let t47 = t10 & u7;
    let t48 = t47 ^ t44;
    let t49 = t7 & t21;
    let t50 = t9 & t4;
    let t51 = t40 ^ t49;
    let t52 = t22 & t17;
    let t53 = t52 ^ t49;
    let t54 = t2 & t8;
    let t55 = t41 & t39;
    let t56 = t55 ^ t54;
    let t57 = t16 & t14;
    let t58 = t57 ^ t54;
    let t59 = t46 ^ t45;
    let t60 = t48 ^ t42;
    let t61 = t51 ^ t50;
    let t62 = t53 ^ t58;
    let t63 = t59 ^ t56;
    let t64 = t60 ^ t58;
    let t65 = t61 ^ t56;
    let t66 = t62 ^ t43;
    let t67 = t65 ^ t66;
    let t68 = t65 & t63;
    let t69 = t64 ^ t68;
    let t70 = t63 ^ t64;
    let t71 = t66 ^ t68;
    let t72 = t71 & t70;
    let t73 = t69 & t67;
    let t74 = t63 & t66;
    let t75 = t70 & t74;
    let t76 = t70 ^ t68;
    let t77 = t64 & t65;
    let t78 = t67 & t77;
    let t79 = t67 ^ t68;
    let t80 = t64 ^ t72;
    let t81 = t75 ^ t76;
    let t82 = t66 ^ t73;
    let t83 = t78 ^ t79;
    let t84 = t81 ^ t83;
    let t85 = t80 ^ t82;
    let t86 = t80 ^ t81;
    let t87 = t82 ^ t83;
    let t88 = t85 ^ t84;
    let t89 = t87 & t5;
    let t90 = t83 & t11;
    let t91 = t82 & u7;
    let t92 = t86 & t21;
    let t93 = t81 & t4;
    let t94 = t80 & t17;
    let t95 = t85 & t8;
    let t96 = t88 & t39;
    let t97 = t84 & t14;
    let t98 = t87 & t19;
    let t99 = t83 & t20;
    let t100 = t82 & t10;
    let t101 = t86 & t7;
    let t102 = t81 & t9;
    let t103 = t80 & t22;
    let t104 = t85 & t2;
    let t105 = t88 & t41;
    let t106 = t84 & t16;
    let t107 = t104 ^ t105;
    let t108 = t93 ^ t99;
    let t109 = t96 ^ t107;
    let t110 = t98 ^ t108;
    let t111 = t91 ^ t101;
    let t112 = t89 ^ t92;
    let t113 = t107 ^ t112;
    let t114 = t90 ^ t110;
    let t115 = t89 ^ t95;
    let t116 = t94 ^ t102;
    let t117 = t97 ^ t103;
    let t118 = t91 ^ t114;
    let t119 = t111 ^ t117;
    let t120 = t100 ^ t108;
    let t121 = t92 ^ t95;
    let t122 = t110 ^ t121;
    let t123 = t106 ^ t119;
    let t124 = t104 ^ t115;
    let t125 = t111 ^ t116;

    let t128 = t94 ^ t107;

    let t131 = t93 ^ t101;
    let t132 = t112 ^ t120;

    let t134 = t97 ^ t116;
    let t135 = t131 ^ t134;
    let t136 = t93 ^ t115;

    let t138 = t119 ^ t132;
    let t140 = t114 ^ t136;

    let s0 = t109 ^ t122;
    let s2 = xnor(t123, t124);
    let s3 = t113 ^ t114;
    let s4 = t118 ^ t128;
    let s7 = xnor(t113, t125);
    let s6 = xnor(t109, t135);
    let s5 = t109 ^ t138;
    let s1 = xnor(t109, t140);

    st[0] = s7;
    st[1] = s6;
    st[2] = s5;
    st[3] = s4;
    st[4] = s3;
    st[5] = s2;
    st[6] = s1;
    st[7] = s0;
}

#[inline]
fn shift_row_u16(input: u16) -> u16 {
    (input & 0x1111)
        | ((input & 0x2220) >> 4)
        | ((input & 0x0002) << 12)
        | ((input & 0x4400) >> 8)
        | ((input & 0x0044) << 8)
        | ((input & 0x8000) >> 12)
        | ((input & 0x0888) << 4)
}

fn shift_rows_state(st: &mut State) {
    st[0] = shift_row_u16(st[0]);
    st[1] = shift_row_u16(st[1]);
    st[2] = shift_row_u16(st[2]);
    st[3] = shift_row_u16(st[3]);
    st[4] = shift_row_u16(st[4]);
    st[5] = shift_row_u16(st[5]);
    st[6] = shift_row_u16(st[6]);
    st[7] = shift_row_u16(st[7]);
}

#[inline]
fn mix_columns_state(st: &mut State) {
    let mut last_col: u16 = 0;

    for i in 0..8 {
        let col = st[i] ^ (((st[i] & 0xeeee) >> 1) | ((st[i] & 0x1111) << 3));
        st[i] = st[i] ^ last_col ^ col ^ (((col & 0xcccc) >> 2) | ((col & 0x3333) << 2));
        last_col = col;
    }

    st[0] ^= last_col;
    st[1] ^= last_col;
    st[3] ^= last_col;
    st[4] ^= last_col;
}

#[inline]
fn xor_key1_state(st: &mut State, k: &State) {
    st[0] ^= k[0];
    st[1] ^= k[1];
    st[2] ^= k[2];
    st[3] ^= k[3];
    st[4] ^= k[4];
    st[5] ^= k[5];
    st[6] ^= k[6];
    st[7] ^= k[7];
}

fn aes_enc(st: &mut State, key: &State) {
    sub_bytes_state(st);
    shift_rows_state(st);
    mix_columns_state(st);
    xor_key1_state(st, key)
}

fn aes_enc_last(st: &mut State, key: &State) {
    sub_bytes_state(st);
    shift_rows_state(st);
    xor_key1_state(st, key)
}

#[inline]
fn aes_keygen_assisti(rcon: u8, i: usize, u: u16) -> u16 {
    let u3 = u & 0xf000;
    let n = u3 >> 12;
    let n = ((n >> 1) | (n << 3)) & 0x000f;
    let ri = ((rcon >> i) & 1) as u16;
    let n = n ^ ri;
    let n = n << 12;
    n ^ (u3 >> 4)
}

fn aes_keygen_assist(next: &mut State, prev: &State, rcon: u8) {
    next.copy_from_slice(prev);
    sub_bytes_state(next);

    next[0] = aes_keygen_assisti(rcon, 0, next[0]);
    next[1] = aes_keygen_assisti(rcon, 1, next[1]);
    next[2] = aes_keygen_assisti(rcon, 2, next[2]);
    next[3] = aes_keygen_assisti(rcon, 3, next[3]);
    next[4] = aes_keygen_assisti(rcon, 4, next[4]);
    next[5] = aes_keygen_assisti(rcon, 5, next[5]);
    next[6] = aes_keygen_assisti(rcon, 6, next[6]);
    next[7] = aes_keygen_assisti(rcon, 7, next[7]);
}

fn aes_keygen_assist0(next: &mut State, prev: &State, rcon: u8) {
    aes_keygen_assist(next, prev, rcon);

    #[inline]
    fn aux(mut n: u16) -> u16 {
        n &= 0xf000;
        n ^= n >> 4;
        n ^= n >> 8;
        n
    }

    next[0] = aux(next[0]);
    next[1] = aux(next[1]);
    next[2] = aux(next[2]);
    next[3] = aux(next[3]);
    next[4] = aux(next[4]);
    next[5] = aux(next[5]);
    next[6] = aux(next[6]);
    next[7] = aux(next[7]);
}

fn aes_keygen_assist1(next: &mut State, prev: &State) {
    aes_keygen_assist(next, prev, 0);

    #[inline]
    fn aux(mut n: u16) -> u16 {
        n &= 0x0f00;
        n ^= n << 4;
        n ^= n >> 8;
        n
    }

    next[0] = aux(next[0]);
    next[1] = aux(next[1]);
    next[2] = aux(next[2]);
    next[3] = aux(next[3]);
    next[4] = aux(next[4]);
    next[5] = aux(next[5]);
    next[6] = aux(next[6]);
    next[7] = aux(next[7]);
}

#[inline]
fn key_expand1(p: u16, n: u16) -> u16 {
    let p = p ^ ((p & 0x0fff) << 4) ^ ((p & 0x00ff) << 8) ^ ((p & 0x000f) << 12);
    n ^ p
}

fn key_expansion_step(next: &mut State, prev: &State) {
    next[0] = key_expand1(prev[0], next[0]);
    next[1] = key_expand1(prev[1], next[1]);
    next[2] = key_expand1(prev[2], next[2]);
    next[3] = key_expand1(prev[3], next[3]);
    next[4] = key_expand1(prev[4], next[4]);
    next[5] = key_expand1(prev[5], next[5]);
    next[6] = key_expand1(prev[6], next[6]);
    next[7] = key_expand1(prev[7], next[7]);
}

impl crate::platform::AESState for State {
    fn new() -> Self {
        new_state()
    }

    fn load_block(&mut self, b: &[u8]) {
        debug_assert!(b.len() == 16);

        transpose_u8x16(b.try_into().unwrap(), self);
    }

    fn store_block(&self, out: &mut [u8]) {
        debug_assert!(out.len() == AES_BLOCK_LEN, "out.len() = {}", out.len());

        transpose_u16x8(self, out);
    }

    #[inline]
    fn xor_block(&self, input: &[u8], out: &mut [u8]) {
        debug_assert!(input.len() == out.len() && input.len() <= AES_BLOCK_LEN);

        let mut block = [0u8; AES_BLOCK_LEN];
        self.store_block(&mut block);

        for i in 0..input.len() {
            out[i] = input[i] ^ block[i];
        }
    }

    fn xor_key(&mut self, key: &Self) {
        xor_key1_state(self, key);
    }

    fn aes_enc(&mut self, key: &Self) {
        aes_enc(self, key);
    }

    fn aes_enc_last(&mut self, key: &Self) {
        aes_enc_last(self, key);
    }

    fn aes_keygen_assist0<const RCON: i32>(&mut self, prev: &Self) {
        aes_keygen_assist0(self, prev, RCON as u8);
    }

    fn aes_keygen_assist1(&mut self, prev: &Self) {
        aes_keygen_assist1(self, prev);
    }

    fn key_expansion_step(&mut self, prev: &Self) {
        key_expansion_step(self, prev)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[allow(non_snake_case)]
    fn sub_bytes_inv_state(st: &mut State) {
        let U0 = st[7];
        let U1 = st[6];
        let U2 = st[5];
        let U3 = st[4];
        let U4 = st[3];
        let U5 = st[2];
        let U6 = st[1];
        let U7 = st[0];

        let T23 = U0 ^ U3;
        let T22 = xnor(U1, U3);
        let T2 = xnor(U0, U1);
        let T1 = U3 ^ U4;
        let T24 = xnor(U4, U7);
        let R5 = U6 ^ U7;
        let T8 = xnor(U1, T23);
        let T19 = T22 ^ R5;
        let T9 = xnor(U7, T1);
        let T10 = T2 ^ T24;
        let T13 = T2 ^ R5;
        let T3 = T1 ^ R5;
        let T25 = xnor(U2, T1);
        let R13 = U1 ^ U6;
        let T17 = xnor(U2, T19);
        let T20 = T24 ^ R13;
        let T4 = U4 ^ T8;
        let R17 = xnor(U2, U5);
        let R18 = xnor(U5, U6);
        let R19 = xnor(U2, U4);
        let Y5 = U0 ^ R17;
        let T6 = T22 ^ R17;
        let T16 = R13 ^ R19;
        let T27 = T1 ^ R18;
        let T15 = T10 ^ T27;
        let T14 = T10 ^ R18;
        let T26 = T3 ^ T16;
        let M1 = T13 & T6;
        let M2 = T23 & T8;
        let M3 = T14 ^ M1;
        let M4 = T19 & Y5;
        let M5 = M4 ^ M1;
        let M6 = T3 & T16;
        let M7 = T22 & T9;
        let M8 = T26 ^ M6;
        let M9 = T20 & T17;
        let M10 = M9 ^ M6;
        let M11 = T1 & T15;
        let M12 = T4 & T27;
        let M13 = M12 ^ M11;
        let M14 = T2 & T10;
        let M15 = M14 ^ M11;
        let M16 = M3 ^ M2;
        let M17 = M5 ^ T24;
        let M18 = M8 ^ M7;
        let M19 = M10 ^ M15;
        let M20 = M16 ^ M13;
        let M21 = M17 ^ M15;
        let M22 = M18 ^ M13;
        let M23 = M19 ^ T25;
        let M24 = M22 ^ M23;
        let M25 = M22 & M20;
        let M26 = M21 ^ M25;
        let M27 = M20 ^ M21;
        let M28 = M23 ^ M25;
        let M29 = M28 & M27;
        let M30 = M26 & M24;
        let M31 = M20 & M23;
        let M32 = M27 & M31;
        let M33 = M27 ^ M25;
        let M34 = M21 & M22;
        let M35 = M24 & M34;
        let M36 = M24 ^ M25;
        let M37 = M21 ^ M29;
        let M38 = M32 ^ M33;
        let M39 = M23 ^ M30;
        let M40 = M35 ^ M36;
        let M41 = M38 ^ M40;
        let M42 = M37 ^ M39;
        let M43 = M37 ^ M38;
        let M44 = M39 ^ M40;
        let M45 = M42 ^ M41;
        let M46 = M44 & T6;
        let M47 = M40 & T8;
        let M48 = M39 & Y5;
        let M49 = M43 & T16;
        let M50 = M38 & T9;
        let M51 = M37 & T17;
        let M52 = M42 & T15;
        let M53 = M45 & T27;
        let M54 = M41 & T10;
        let M55 = M44 & T13;
        let M56 = M40 & T23;
        let M57 = M39 & T19;
        let M58 = M43 & T3;
        let M59 = M38 & T22;
        let M60 = M37 & T20;
        let M61 = M42 & T1;
        let M62 = M45 & T4;
        let M63 = M41 & T2;
        let P0 = M52 ^ M61;
        let P1 = M58 ^ M59;
        let P2 = M54 ^ M62;
        let P3 = M47 ^ M50;
        let P4 = M48 ^ M56;
        let P5 = M46 ^ M51;
        let P6 = M49 ^ M60;
        let P7 = P0 ^ P1;
        let P8 = M50 ^ M53;
        let P9 = M55 ^ M63;
        let P10 = M57 ^ P4;
        let P11 = P0 ^ P3;
        let P12 = M46 ^ M48;
        let P13 = M49 ^ M51;
        let P14 = M49 ^ M62;
        let P15 = M54 ^ M59;
        let P16 = M57 ^ M61;
        let P17 = M58 ^ P2;
        let P18 = M63 ^ P5;
        let P19 = P2 ^ P3;
        let P20 = P4 ^ P6;
        let P22 = P2 ^ P7;
        let P23 = P7 ^ P8;
        let P24 = P5 ^ P7;
        let P25 = P6 ^ P10;
        let P26 = P9 ^ P11;
        let P27 = P10 ^ P18;
        let P28 = P11 ^ P25;
        let P29 = P15 ^ P20;
        let W0 = P13 ^ P22;
        let W1 = P26 ^ P29;
        let W2 = P17 ^ P28;
        let W3 = P12 ^ P22;
        let W4 = P23 ^ P27;
        let W5 = P19 ^ P24;
        let W6 = P14 ^ P23;
        let W7 = P9 ^ P16;

        st[0] = W7;
        st[1] = W6;
        st[2] = W5;
        st[3] = W4;
        st[4] = W3;
        st[5] = W2;
        st[6] = W1;
        st[7] = W0;
    }

    fn sbox_fwd(s: u8) -> u8 {
        match s {
            0 => 0x63,
            1 => 0x7c,
            2 => 0x77,
            3 => 0x7b,
            4 => 0xf2,
            5 => 0x6b,
            6 => 0x6f,
            7 => 0xc5,
            8 => 0x30,
            9 => 0x01,
            10 => 0x67,
            11 => 0x2b,
            12 => 0xfe,
            13 => 0xd7,
            14 => 0xab,
            15 => 0x76,
            16 => 0xca,
            17 => 0x82,
            18 => 0xc9,
            19 => 0x7d,
            20 => 0xfa,
            21 => 0x59,
            22 => 0x47,
            23 => 0xf0,
            24 => 0xad,
            25 => 0xd4,
            26 => 0xa2,
            27 => 0xaf,
            28 => 0x9c,
            29 => 0xa4,
            30 => 0x72,
            31 => 0xc0,
            32 => 0xb7,
            33 => 0xfd,
            34 => 0x93,
            35 => 0x26,
            36 => 0x36,
            37 => 0x3f,
            38 => 0xf7,
            39 => 0xcc,
            40 => 0x34,
            41 => 0xa5,
            42 => 0xe5,
            43 => 0xf1,
            44 => 0x71,
            45 => 0xd8,
            46 => 0x31,
            47 => 0x15,
            48 => 0x04,
            49 => 0xc7,
            50 => 0x23,
            51 => 0xc3,
            52 => 0x18,
            53 => 0x96,
            54 => 0x05,
            55 => 0x9a,
            56 => 0x07,
            57 => 0x12,
            58 => 0x80,
            59 => 0xe2,
            60 => 0xeb,
            61 => 0x27,
            62 => 0xb2,
            63 => 0x75,
            64 => 0x09,
            65 => 0x83,
            66 => 0x2c,
            67 => 0x1a,
            68 => 0x1b,
            69 => 0x6e,
            70 => 0x5a,
            71 => 0xa0,
            72 => 0x52,
            73 => 0x3b,
            74 => 0xd6,
            75 => 0xb3,
            76 => 0x29,
            77 => 0xe3,
            78 => 0x2f,
            79 => 0x84,
            80 => 0x53,
            81 => 0xd1,
            82 => 0x00,
            83 => 0xed,
            84 => 0x20,
            85 => 0xfc,
            86 => 0xb1,
            87 => 0x5b,
            88 => 0x6a,
            89 => 0xcb,
            90 => 0xbe,
            91 => 0x39,
            92 => 0x4a,
            93 => 0x4c,
            94 => 0x58,
            95 => 0xcf,
            96 => 0xd0,
            97 => 0xef,
            98 => 0xaa,
            99 => 0xfb,
            100 => 0x43,
            101 => 0x4d,
            102 => 0x33,
            103 => 0x85,
            104 => 0x45,
            105 => 0xf9,
            106 => 0x02,
            107 => 0x7f,
            108 => 0x50,
            109 => 0x3c,
            110 => 0x9f,
            111 => 0xa8,
            112 => 0x51,
            113 => 0xa3,
            114 => 0x40,
            115 => 0x8f,
            116 => 0x92,
            117 => 0x9d,
            118 => 0x38,
            119 => 0xf5,
            120 => 0xbc,
            121 => 0xb6,
            122 => 0xda,
            123 => 0x21,
            124 => 0x10,
            125 => 0xff,
            126 => 0xf3,
            127 => 0xd2,
            128 => 0xcd,
            129 => 0x0c,
            130 => 0x13,
            131 => 0xec,
            132 => 0x5f,
            133 => 0x97,
            134 => 0x44,
            135 => 0x17,
            136 => 0xc4,
            137 => 0xa7,
            138 => 0x7e,
            139 => 0x3d,
            140 => 0x64,
            141 => 0x5d,
            142 => 0x19,
            143 => 0x73,
            144 => 0x60,
            145 => 0x81,
            146 => 0x4f,
            147 => 0xdc,
            148 => 0x22,
            149 => 0x2a,
            150 => 0x90,
            151 => 0x88,
            152 => 0x46,
            153 => 0xee,
            154 => 0xb8,
            155 => 0x14,
            156 => 0xde,
            157 => 0x5e,
            158 => 0x0b,
            159 => 0xdb,
            160 => 0xe0,
            161 => 0x32,
            162 => 0x3a,
            163 => 0x0a,
            164 => 0x49,
            165 => 0x06,
            166 => 0x24,
            167 => 0x5c,
            168 => 0xc2,
            169 => 0xd3,
            170 => 0xac,
            171 => 0x62,
            172 => 0x91,
            173 => 0x95,
            174 => 0xe4,
            175 => 0x79,
            176 => 0xe7,
            177 => 0xc8,
            178 => 0x37,
            179 => 0x6d,
            180 => 0x8d,
            181 => 0xd5,
            182 => 0x4e,
            183 => 0xa9,
            184 => 0x6c,
            185 => 0x56,
            186 => 0xf4,
            187 => 0xea,
            188 => 0x65,
            189 => 0x7a,
            190 => 0xae,
            191 => 0x08,
            192 => 0xba,
            193 => 0x78,
            194 => 0x25,
            195 => 0x2e,
            196 => 0x1c,
            197 => 0xa6,
            198 => 0xb4,
            199 => 0xc6,
            200 => 0xe8,
            201 => 0xdd,
            202 => 0x74,
            203 => 0x1f,
            204 => 0x4b,
            205 => 0xbd,
            206 => 0x8b,
            207 => 0x8a,
            208 => 0x70,
            209 => 0x3e,
            210 => 0xb5,
            211 => 0x66,
            212 => 0x48,
            213 => 0x03,
            214 => 0xf6,
            215 => 0x0e,
            216 => 0x61,
            217 => 0x35,
            218 => 0x57,
            219 => 0xb9,
            220 => 0x86,
            221 => 0xc1,
            222 => 0x1d,
            223 => 0x9e,
            224 => 0xe1,
            225 => 0xf8,
            226 => 0x98,
            227 => 0x11,
            228 => 0x69,
            229 => 0xd9,
            230 => 0x8e,
            231 => 0x94,
            232 => 0x9b,
            233 => 0x1e,
            234 => 0x87,
            235 => 0xe9,
            236 => 0xce,
            237 => 0x55,
            238 => 0x28,
            239 => 0xdf,
            240 => 0x8c,
            241 => 0xa1,
            242 => 0x89,
            243 => 0x0d,
            244 => 0xbf,
            245 => 0xe6,
            246 => 0x42,
            247 => 0x68,
            248 => 0x41,
            249 => 0x99,
            250 => 0x2d,
            251 => 0x0f,
            252 => 0xb0,
            253 => 0x54,
            254 => 0xbb,
            255 => 0x16,
        }
    }

    fn sbox_inv(s: u8) -> u8 {
        match s {
            0 => 0x52,
            1 => 0x09,
            2 => 0x6a,
            3 => 0xd5,
            4 => 0x30,
            5 => 0x36,
            6 => 0xa5,
            7 => 0x38,
            8 => 0xbf,
            9 => 0x40,
            10 => 0xa3,
            11 => 0x9e,
            12 => 0x81,
            13 => 0xf3,
            14 => 0xd7,
            15 => 0xfb,
            16 => 0x7c,
            17 => 0xe3,
            18 => 0x39,
            19 => 0x82,
            20 => 0x9b,
            21 => 0x2f,
            22 => 0xff,
            23 => 0x87,
            24 => 0x34,
            25 => 0x8e,
            26 => 0x43,
            27 => 0x44,
            28 => 0xc4,
            29 => 0xde,
            30 => 0xe9,
            31 => 0xcb,
            32 => 0x54,
            33 => 0x7b,
            34 => 0x94,
            35 => 0x32,
            36 => 0xa6,
            37 => 0xc2,
            38 => 0x23,
            39 => 0x3d,
            40 => 0xee,
            41 => 0x4c,
            42 => 0x95,
            43 => 0x0b,
            44 => 0x42,
            45 => 0xfa,
            46 => 0xc3,
            47 => 0x4e,
            48 => 0x08,
            49 => 0x2e,
            50 => 0xa1,
            51 => 0x66,
            52 => 0x28,
            53 => 0xd9,
            54 => 0x24,
            55 => 0xb2,
            56 => 0x76,
            57 => 0x5b,
            58 => 0xa2,
            59 => 0x49,
            60 => 0x6d,
            61 => 0x8b,
            62 => 0xd1,
            63 => 0x25,
            64 => 0x72,
            65 => 0xf8,
            66 => 0xf6,
            67 => 0x64,
            68 => 0x86,
            69 => 0x68,
            70 => 0x98,
            71 => 0x16,
            72 => 0xd4,
            73 => 0xa4,
            74 => 0x5c,
            75 => 0xcc,
            76 => 0x5d,
            77 => 0x65,
            78 => 0xb6,
            79 => 0x92,
            80 => 0x6c,
            81 => 0x70,
            82 => 0x48,
            83 => 0x50,
            84 => 0xfd,
            85 => 0xed,
            86 => 0xb9,
            87 => 0xda,
            88 => 0x5e,
            89 => 0x15,
            90 => 0x46,
            91 => 0x57,
            92 => 0xa7,
            93 => 0x8d,
            94 => 0x9d,
            95 => 0x84,
            96 => 0x90,
            97 => 0xd8,
            98 => 0xab,
            99 => 0x00,
            100 => 0x8c,
            101 => 0xbc,
            102 => 0xd3,
            103 => 0x0a,
            104 => 0xf7,
            105 => 0xe4,
            106 => 0x58,
            107 => 0x05,
            108 => 0xb8,
            109 => 0xb3,
            110 => 0x45,
            111 => 0x06,
            112 => 0xd0,
            113 => 0x2c,
            114 => 0x1e,
            115 => 0x8f,
            116 => 0xca,
            117 => 0x3f,
            118 => 0x0f,
            119 => 0x02,
            120 => 0xc1,
            121 => 0xaf,
            122 => 0xbd,
            123 => 0x03,
            124 => 0x01,
            125 => 0x13,
            126 => 0x8a,
            127 => 0x6b,
            128 => 0x3a,
            129 => 0x91,
            130 => 0x11,
            131 => 0x41,
            132 => 0x4f,
            133 => 0x67,
            134 => 0xdc,
            135 => 0xea,
            136 => 0x97,
            137 => 0xf2,
            138 => 0xcf,
            139 => 0xce,
            140 => 0xf0,
            141 => 0xb4,
            142 => 0xe6,
            143 => 0x73,
            144 => 0x96,
            145 => 0xac,
            146 => 0x74,
            147 => 0x22,
            148 => 0xe7,
            149 => 0xad,
            150 => 0x35,
            151 => 0x85,
            152 => 0xe2,
            153 => 0xf9,
            154 => 0x37,
            155 => 0xe8,
            156 => 0x1c,
            157 => 0x75,
            158 => 0xdf,
            159 => 0x6e,
            160 => 0x47,
            161 => 0xf1,
            162 => 0x1a,
            163 => 0x71,
            164 => 0x1d,
            165 => 0x29,
            166 => 0xc5,
            167 => 0x89,
            168 => 0x6f,
            169 => 0xb7,
            170 => 0x62,
            171 => 0x0e,
            172 => 0xaa,
            173 => 0x18,
            174 => 0xbe,
            175 => 0x1b,
            176 => 0xfc,
            177 => 0x56,
            178 => 0x3e,
            179 => 0x4b,
            180 => 0xc6,
            181 => 0xd2,
            182 => 0x79,
            183 => 0x20,
            184 => 0x9a,
            185 => 0xdb,
            186 => 0xc0,
            187 => 0xfe,
            188 => 0x78,
            189 => 0xcd,
            190 => 0x5a,
            191 => 0xf4,
            192 => 0x1f,
            193 => 0xdd,
            194 => 0xa8,
            195 => 0x33,
            196 => 0x88,
            197 => 0x07,
            198 => 0xc7,
            199 => 0x31,
            200 => 0xb1,
            201 => 0x12,
            202 => 0x10,
            203 => 0x59,
            204 => 0x27,
            205 => 0x80,
            206 => 0xec,
            207 => 0x5f,
            208 => 0x60,
            209 => 0x51,
            210 => 0x7f,
            211 => 0xa9,
            212 => 0x19,
            213 => 0xb5,
            214 => 0x4a,
            215 => 0x0d,
            216 => 0x2d,
            217 => 0xe5,
            218 => 0x7a,
            219 => 0x9f,
            220 => 0x93,
            221 => 0xc9,
            222 => 0x9c,
            223 => 0xef,
            224 => 0xa0,
            225 => 0xe0,
            226 => 0x3b,
            227 => 0x4d,
            228 => 0xae,
            229 => 0x2a,
            230 => 0xf5,
            231 => 0xb0,
            232 => 0xc8,
            233 => 0xeb,
            234 => 0xbb,
            235 => 0x3c,
            236 => 0x83,
            237 => 0x53,
            238 => 0x99,
            239 => 0x61,
            240 => 0x17,
            241 => 0x2b,
            242 => 0x04,
            243 => 0x7e,
            244 => 0xba,
            245 => 0x77,
            246 => 0xd6,
            247 => 0x26,
            248 => 0xe1,
            249 => 0x69,
            250 => 0x14,
            251 => 0x63,
            252 => 0x55,
            253 => 0x21,
            254 => 0x0c,
            255 => 0x7d,
        }
    }

    use rand_core::{OsRng, RngCore};

    use crate::platform::portable::aes_core::transpose_u8x16;

    fn get_bit_u8(x: &[u8], i: usize, j: usize) -> u8 {
        (x[i] >> j) & 0x1
    }

    fn get_bit_u16(x: &[u16], i: usize, j: usize) -> u8 {
        ((x[j] >> i) & 0x1) as u8
    }

    #[test]
    fn test_transpose() {
        let mut x = [0u8; 16];
        OsRng.fill_bytes(&mut x);
        let mut y = [0u16; 8];
        transpose_u8x16(&x, &mut y);
        for i in 0..16 {
            for j in 0..8 {
                if get_bit_u8(&x, i, j) != get_bit_u16(&y, i, j) {
                    println!("x[{},{}] = {}", i, j, get_bit_u8(&x, i, j));
                    println!("y[{},{}] = {}", i, j, get_bit_u16(&y, i, j));
                    assert!(false);
                } else {
                    println!("transpose ok: {},{}", i, j);
                }
            }
        }
        let mut z = [0u8; 16];
        transpose_u16x8(&y, &mut z);
        for i in 0..16 {
            for j in 0..8 {
                if get_bit_u8(&x, i, j) != get_bit_u8(&z, i, j) {
                    println!("x[{},{}] = {}", i, j, get_bit_u8(&x, i, j));
                    println!("z[{},{}] = {}", i, j, get_bit_u8(&z, i, j));
                    assert!(false);
                } else {
                    println!("inv-transpose ok: {},{}", i, j);
                }
            }
        }
    }

    #[test]
    fn test_sbox() {
        let mut x = [0u8; 16];
        let mut y = [0u16; 8];
        let mut w = [0u8; 16];
        for i in 0..=255 {
            x[0] = i;
            x[9] = i;
            transpose_u8x16(&x, &mut y);
            sub_bytes_state(&mut y);
            transpose_u16x8(&y, &mut w);
            if w[0] != sbox_fwd(i as u8) {
                println!("sbox[{}] = {}, should be {}", i, w[0], sbox_fwd(i as u8));
                assert!(false);
            } else {
                println!("sbox ok {}", i)
            }
        }
    }

    #[test]
    fn test_sbox_inv() {
        let mut x = [0u8; 16];
        let mut y = [0u16; 8];
        let mut w = [0u8; 16];
        for i in 0..=255 {
            x[0] = i;
            x[9] = i;
            transpose_u8x16(&x, &mut y);
            sub_bytes_inv_state(&mut y);
            transpose_u16x8(&y, &mut w);
            if w[0] != sbox_inv(i as u8) {
                println!(
                    "sbox_inv[{}] = {}, should be {}",
                    i,
                    w[0],
                    sbox_inv(i as u8)
                );
                assert!(false);
            } else {
                println!("sbox inv ok {}", i)
            }
        }
    }
}
