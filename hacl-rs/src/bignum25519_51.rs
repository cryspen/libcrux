#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

use libcrux_macros as krml;

use crate::fstar::{self, uint128::uint128_to_uint64};

#[inline(always)]
pub fn fadd(out: &mut [u64], f1: &[u64], f2: &[u64]) {
    let f10 = f1[0usize];
    let f20 = f2[0usize];
    let f11 = f1[1usize];
    let f21 = f2[1usize];
    let f12 = f1[2usize];
    let f22 = f2[2usize];
    let f13 = f1[3usize];
    let f23 = f2[3usize];
    let f14 = f1[4usize];
    let f24 = f2[4usize];
    out[0usize] = f10.wrapping_add(f20);
    out[1usize] = f11.wrapping_add(f21);
    out[2usize] = f12.wrapping_add(f22);
    out[3usize] = f13.wrapping_add(f23);
    out[4usize] = f14.wrapping_add(f24)
}

#[inline(always)]
pub fn fsub(out: &mut [u64], f1: &[u64], f2: &[u64]) {
    let f10 = f1[0usize];
    let f20 = f2[0usize];
    let f11 = f1[1usize];
    let f21 = f2[1usize];
    let f12 = f1[2usize];
    let f22 = f2[2usize];
    let f13 = f1[3usize];
    let f23 = f2[3usize];
    let f14 = f1[4usize];
    let f24 = f2[4usize];
    out[0usize] = f10.wrapping_add(0x3fffffffffff68u64).wrapping_sub(f20);
    out[1usize] = f11.wrapping_add(0x3ffffffffffff8u64).wrapping_sub(f21);
    out[2usize] = f12.wrapping_add(0x3ffffffffffff8u64).wrapping_sub(f22);
    out[3usize] = f13.wrapping_add(0x3ffffffffffff8u64).wrapping_sub(f23);
    out[4usize] = f14.wrapping_add(0x3ffffffffffff8u64).wrapping_sub(f24)
}

#[inline(always)]
pub fn fmul(out: &mut [u64], f1: &[u64], f2: &[u64]) {
    let f10 = f1[0usize];
    let f11 = f1[1usize];
    let f12 = f1[2usize];
    let f13 = f1[3usize];
    let f14 = f1[4usize];
    let f20 = f2[0usize];
    let f21 = f2[1usize];
    let f22 = f2[2usize];
    let f23 = f2[3usize];
    let f24 = f2[4usize];
    let tmp1 = f21.wrapping_mul(19u64);
    let tmp2 = f22.wrapping_mul(19u64);
    let tmp3 = f23.wrapping_mul(19u64);
    let tmp4 = f24.wrapping_mul(19u64);
    let o0 = fstar::uint128::mul_wide(f10, f20);
    let o1 = fstar::uint128::mul_wide(f10, f21);
    let o2 = fstar::uint128::mul_wide(f10, f22);
    let o3 = fstar::uint128::mul_wide(f10, f23);
    let o4 = fstar::uint128::mul_wide(f10, f24);
    let o01 = fstar::uint128::add(o0, fstar::uint128::mul_wide(f11, tmp4));
    let o11 = fstar::uint128::add(o1, fstar::uint128::mul_wide(f11, f20));
    let o21 = fstar::uint128::add(o2, fstar::uint128::mul_wide(f11, f21));
    let o31 = fstar::uint128::add(o3, fstar::uint128::mul_wide(f11, f22));
    let o41 = fstar::uint128::add(o4, fstar::uint128::mul_wide(f11, f23));
    let o02 = fstar::uint128::add(o01, fstar::uint128::mul_wide(f12, tmp3));
    let o12 = fstar::uint128::add(o11, fstar::uint128::mul_wide(f12, tmp4));
    let o22 = fstar::uint128::add(o21, fstar::uint128::mul_wide(f12, f20));
    let o32 = fstar::uint128::add(o31, fstar::uint128::mul_wide(f12, f21));
    let o42 = fstar::uint128::add(o41, fstar::uint128::mul_wide(f12, f22));
    let o03 = fstar::uint128::add(o02, fstar::uint128::mul_wide(f13, tmp2));
    let o13 = fstar::uint128::add(o12, fstar::uint128::mul_wide(f13, tmp3));
    let o23 = fstar::uint128::add(o22, fstar::uint128::mul_wide(f13, tmp4));
    let o33 = fstar::uint128::add(o32, fstar::uint128::mul_wide(f13, f20));
    let o43 = fstar::uint128::add(o42, fstar::uint128::mul_wide(f13, f21));
    let o04 = fstar::uint128::add(o03, fstar::uint128::mul_wide(f14, tmp1));
    let o14 = fstar::uint128::add(o13, fstar::uint128::mul_wide(f14, tmp2));
    let o24 = fstar::uint128::add(o23, fstar::uint128::mul_wide(f14, tmp3));
    let o34 = fstar::uint128::add(o33, fstar::uint128::mul_wide(f14, tmp4));
    let o44 = fstar::uint128::add(o43, fstar::uint128::mul_wide(f14, f20));
    let tmp_w0 = o04;
    let tmp_w1 = o14;
    let tmp_w2 = o24;
    let tmp_w3 = o34;
    let tmp_w4 = o44;
    let l· = fstar::uint128::add(tmp_w0, fstar::uint128::uint64_to_uint128(0u64));
    let tmp01 = uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0 = uint128_to_uint64(fstar::uint128::shift_right(l·, 51u32));
    let l·0 = fstar::uint128::add(tmp_w1, fstar::uint128::uint64_to_uint128(c0));
    let tmp11 = uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1 = uint128_to_uint64(fstar::uint128::shift_right(l·0, 51u32));
    let l·1 = fstar::uint128::add(tmp_w2, fstar::uint128::uint64_to_uint128(c1));
    let tmp21 = uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2 = uint128_to_uint64(fstar::uint128::shift_right(l·1, 51u32));
    let l·2 = fstar::uint128::add(tmp_w3, fstar::uint128::uint64_to_uint128(c2));
    let tmp31 = uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3 = uint128_to_uint64(fstar::uint128::shift_right(l·2, 51u32));
    let l·3 = fstar::uint128::add(tmp_w4, fstar::uint128::uint64_to_uint128(c3));
    let tmp41 = uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4 = uint128_to_uint64(fstar::uint128::shift_right(l·3, 51u32));
    let l·4 = tmp01.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0· = l·4 & 0x7ffffffffffffu64;
    let c5 = l·4.wrapping_shr(51u32);
    let o00 = tmp0·;
    let o10 = tmp11.wrapping_add(c5);
    let o20 = tmp21;
    let o30 = tmp31;
    let o40 = tmp41;
    out[0usize] = o00;
    out[1usize] = o10;
    out[2usize] = o20;
    out[3usize] = o30;
    out[4usize] = o40
}

#[inline(always)]
pub fn fmul2(out: &mut [u64], f1: &[u64], f2: &[u64]) {
    let f10 = f1[0usize];
    let f11 = f1[1usize];
    let f12 = f1[2usize];
    let f13 = f1[3usize];
    let f14 = f1[4usize];
    let f20 = f2[0usize];
    let f21 = f2[1usize];
    let f22 = f2[2usize];
    let f23 = f2[3usize];
    let f24 = f2[4usize];
    let f30 = f1[5usize];
    let f31 = f1[6usize];
    let f32 = f1[7usize];
    let f33 = f1[8usize];
    let f34 = f1[9usize];
    let f40 = f2[5usize];
    let f41 = f2[6usize];
    let f42 = f2[7usize];
    let f43 = f2[8usize];
    let f44 = f2[9usize];
    let tmp11 = f21.wrapping_mul(19u64);
    let tmp12 = f22.wrapping_mul(19u64);
    let tmp13 = f23.wrapping_mul(19u64);
    let tmp14 = f24.wrapping_mul(19u64);
    let tmp21 = f41.wrapping_mul(19u64);
    let tmp22 = f42.wrapping_mul(19u64);
    let tmp23 = f43.wrapping_mul(19u64);
    let tmp24 = f44.wrapping_mul(19u64);
    let o0 = fstar::uint128::mul_wide(f10, f20);
    let o1 = fstar::uint128::mul_wide(f10, f21);
    let o2 = fstar::uint128::mul_wide(f10, f22);
    let o3 = fstar::uint128::mul_wide(f10, f23);
    let o4 = fstar::uint128::mul_wide(f10, f24);
    let o01 = fstar::uint128::add(o0, fstar::uint128::mul_wide(f11, tmp14));
    let o11 = fstar::uint128::add(o1, fstar::uint128::mul_wide(f11, f20));
    let o21 = fstar::uint128::add(o2, fstar::uint128::mul_wide(f11, f21));
    let o31 = fstar::uint128::add(o3, fstar::uint128::mul_wide(f11, f22));
    let o41 = fstar::uint128::add(o4, fstar::uint128::mul_wide(f11, f23));
    let o02 = fstar::uint128::add(o01, fstar::uint128::mul_wide(f12, tmp13));
    let o12 = fstar::uint128::add(o11, fstar::uint128::mul_wide(f12, tmp14));
    let o22 = fstar::uint128::add(o21, fstar::uint128::mul_wide(f12, f20));
    let o32 = fstar::uint128::add(o31, fstar::uint128::mul_wide(f12, f21));
    let o42 = fstar::uint128::add(o41, fstar::uint128::mul_wide(f12, f22));
    let o03 = fstar::uint128::add(o02, fstar::uint128::mul_wide(f13, tmp12));
    let o13 = fstar::uint128::add(o12, fstar::uint128::mul_wide(f13, tmp13));
    let o23 = fstar::uint128::add(o22, fstar::uint128::mul_wide(f13, tmp14));
    let o33 = fstar::uint128::add(o32, fstar::uint128::mul_wide(f13, f20));
    let o43 = fstar::uint128::add(o42, fstar::uint128::mul_wide(f13, f21));
    let o04 = fstar::uint128::add(o03, fstar::uint128::mul_wide(f14, tmp11));
    let o14 = fstar::uint128::add(o13, fstar::uint128::mul_wide(f14, tmp12));
    let o24 = fstar::uint128::add(o23, fstar::uint128::mul_wide(f14, tmp13));
    let o34 = fstar::uint128::add(o33, fstar::uint128::mul_wide(f14, tmp14));
    let o44 = fstar::uint128::add(o43, fstar::uint128::mul_wide(f14, f20));
    let tmp_w10 = o04;
    let tmp_w11 = o14;
    let tmp_w12 = o24;
    let tmp_w13 = o34;
    let tmp_w14 = o44;
    let o00 = fstar::uint128::mul_wide(f30, f40);
    let o10 = fstar::uint128::mul_wide(f30, f41);
    let o20 = fstar::uint128::mul_wide(f30, f42);
    let o30 = fstar::uint128::mul_wide(f30, f43);
    let o40 = fstar::uint128::mul_wide(f30, f44);
    let o010 = fstar::uint128::add(o00, fstar::uint128::mul_wide(f31, tmp24));
    let o110 = fstar::uint128::add(o10, fstar::uint128::mul_wide(f31, f40));
    let o210 = fstar::uint128::add(o20, fstar::uint128::mul_wide(f31, f41));
    let o310 = fstar::uint128::add(o30, fstar::uint128::mul_wide(f31, f42));
    let o410 = fstar::uint128::add(o40, fstar::uint128::mul_wide(f31, f43));
    let o020 = fstar::uint128::add(o010, fstar::uint128::mul_wide(f32, tmp23));
    let o120 = fstar::uint128::add(o110, fstar::uint128::mul_wide(f32, tmp24));
    let o220 = fstar::uint128::add(o210, fstar::uint128::mul_wide(f32, f40));
    let o320 = fstar::uint128::add(o310, fstar::uint128::mul_wide(f32, f41));
    let o420 = fstar::uint128::add(o410, fstar::uint128::mul_wide(f32, f42));
    let o030 = fstar::uint128::add(o020, fstar::uint128::mul_wide(f33, tmp22));
    let o130 = fstar::uint128::add(o120, fstar::uint128::mul_wide(f33, tmp23));
    let o230 = fstar::uint128::add(o220, fstar::uint128::mul_wide(f33, tmp24));
    let o330 = fstar::uint128::add(o320, fstar::uint128::mul_wide(f33, f40));
    let o430 = fstar::uint128::add(o420, fstar::uint128::mul_wide(f33, f41));
    let o040 = fstar::uint128::add(o030, fstar::uint128::mul_wide(f34, tmp21));
    let o140 = fstar::uint128::add(o130, fstar::uint128::mul_wide(f34, tmp22));
    let o240 = fstar::uint128::add(o230, fstar::uint128::mul_wide(f34, tmp23));
    let o340 = fstar::uint128::add(o330, fstar::uint128::mul_wide(f34, tmp24));
    let o440 = fstar::uint128::add(o430, fstar::uint128::mul_wide(f34, f40));
    let tmp_w20 = o040;
    let tmp_w21 = o140;
    let tmp_w22 = o240;
    let tmp_w23 = o340;
    let tmp_w24 = o440;
    let l· = fstar::uint128::add(tmp_w10, fstar::uint128::uint64_to_uint128(0u64));
    let tmp0 = uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0 = uint128_to_uint64(fstar::uint128::shift_right(l·, 51u32));
    let l·0 = fstar::uint128::add(tmp_w11, fstar::uint128::uint64_to_uint128(c0));
    let tmp1 = uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1 = uint128_to_uint64(fstar::uint128::shift_right(l·0, 51u32));
    let l·1 = fstar::uint128::add(tmp_w12, fstar::uint128::uint64_to_uint128(c1));
    let tmp2 = uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2 = uint128_to_uint64(fstar::uint128::shift_right(l·1, 51u32));
    let l·2 = fstar::uint128::add(tmp_w13, fstar::uint128::uint64_to_uint128(c2));
    let tmp3 = uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3 = uint128_to_uint64(fstar::uint128::shift_right(l·2, 51u32));
    let l·3 = fstar::uint128::add(tmp_w14, fstar::uint128::uint64_to_uint128(c3));
    let tmp4 = uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4 = uint128_to_uint64(fstar::uint128::shift_right(l·3, 51u32));
    let l·4 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0· = l·4 & 0x7ffffffffffffu64;
    let c5 = l·4.wrapping_shr(51u32);
    let o100 = tmp0·;
    let o111 = tmp1.wrapping_add(c5);
    let o121 = tmp2;
    let o131 = tmp3;
    let o141 = tmp4;
    let l·5 = fstar::uint128::add(tmp_w20, fstar::uint128::uint64_to_uint128(0u64));
    let tmp00 = uint128_to_uint64(l·5) & 0x7ffffffffffffu64;
    let c00 = uint128_to_uint64(fstar::uint128::shift_right(l·5, 51u32));
    let l·6 = fstar::uint128::add(tmp_w21, fstar::uint128::uint64_to_uint128(c00));
    let tmp10 = uint128_to_uint64(l·6) & 0x7ffffffffffffu64;
    let c10 = uint128_to_uint64(fstar::uint128::shift_right(l·6, 51u32));
    let l·7 = fstar::uint128::add(tmp_w22, fstar::uint128::uint64_to_uint128(c10));
    let tmp20 = uint128_to_uint64(l·7) & 0x7ffffffffffffu64;
    let c20 = uint128_to_uint64(fstar::uint128::shift_right(l·7, 51u32));
    let l·8 = fstar::uint128::add(tmp_w23, fstar::uint128::uint64_to_uint128(c20));
    let tmp30 = uint128_to_uint64(l·8) & 0x7ffffffffffffu64;
    let c30 = uint128_to_uint64(fstar::uint128::shift_right(l·8, 51u32));
    let l·9 = fstar::uint128::add(tmp_w24, fstar::uint128::uint64_to_uint128(c30));
    let tmp40 = uint128_to_uint64(l·9) & 0x7ffffffffffffu64;
    let c40 = uint128_to_uint64(fstar::uint128::shift_right(l·9, 51u32));
    let l·10 = tmp00.wrapping_add(c40.wrapping_mul(19u64));
    let tmp0·0 = l·10 & 0x7ffffffffffffu64;
    let c50 = l·10.wrapping_shr(51u32);
    let o200 = tmp0·0;
    let o211 = tmp10.wrapping_add(c50);
    let o221 = tmp20;
    let o231 = tmp30;
    let o241 = tmp40;
    let o101 = o100;
    let o112 = o111;
    let o122 = o121;
    let o132 = o131;
    let o142 = o141;
    let o201 = o200;
    let o212 = o211;
    let o222 = o221;
    let o232 = o231;
    let o242 = o241;
    out[0usize] = o101;
    out[1usize] = o112;
    out[2usize] = o122;
    out[3usize] = o132;
    out[4usize] = o142;
    out[5usize] = o201;
    out[6usize] = o212;
    out[7usize] = o222;
    out[8usize] = o232;
    out[9usize] = o242
}

#[inline(always)]
pub fn fmul1(out: &mut [u64], f1: &[u64], f2: u64) {
    let f10 = f1[0usize];
    let f11 = f1[1usize];
    let f12 = f1[2usize];
    let f13 = f1[3usize];
    let f14 = f1[4usize];
    let tmp_w0 = fstar::uint128::mul_wide(f2, f10);
    let tmp_w1 = fstar::uint128::mul_wide(f2, f11);
    let tmp_w2 = fstar::uint128::mul_wide(f2, f12);
    let tmp_w3 = fstar::uint128::mul_wide(f2, f13);
    let tmp_w4 = fstar::uint128::mul_wide(f2, f14);
    let l· = fstar::uint128::add(tmp_w0, fstar::uint128::uint64_to_uint128(0u64));
    let tmp0 = uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0 = uint128_to_uint64(fstar::uint128::shift_right(l·, 51u32));
    let l·0 = fstar::uint128::add(tmp_w1, fstar::uint128::uint64_to_uint128(c0));
    let tmp1 = uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1 = uint128_to_uint64(fstar::uint128::shift_right(l·0, 51u32));
    let l·1 = fstar::uint128::add(tmp_w2, fstar::uint128::uint64_to_uint128(c1));
    let tmp2 = uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2 = uint128_to_uint64(fstar::uint128::shift_right(l·1, 51u32));
    let l·2 = fstar::uint128::add(tmp_w3, fstar::uint128::uint64_to_uint128(c2));
    let tmp3 = uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3 = uint128_to_uint64(fstar::uint128::shift_right(l·2, 51u32));
    let l·3 = fstar::uint128::add(tmp_w4, fstar::uint128::uint64_to_uint128(c3));
    let tmp4 = uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4 = uint128_to_uint64(fstar::uint128::shift_right(l·3, 51u32));
    let l·4 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0· = l·4 & 0x7ffffffffffffu64;
    let c5 = l·4.wrapping_shr(51u32);
    let o0 = tmp0·;
    let o1 = tmp1.wrapping_add(c5);
    let o2 = tmp2;
    let o3 = tmp3;
    let o4 = tmp4;
    out[0usize] = o0;
    out[1usize] = o1;
    out[2usize] = o2;
    out[3usize] = o3;
    out[4usize] = o4
}

#[inline(always)]
pub fn fsqr(out: &mut [u64], f: &[u64]) {
    let f0 = f[0usize];
    let f1 = f[1usize];
    let f2 = f[2usize];
    let f3 = f[3usize];
    let f4 = f[4usize];
    let d0 = 2u64.wrapping_mul(f0);
    let d1 = 2u64.wrapping_mul(f1);
    let d2 = 38u64.wrapping_mul(f2);
    let d3 = 19u64.wrapping_mul(f3);
    let d419 = 19u64.wrapping_mul(f4);
    let d4 = 2u64.wrapping_mul(d419);
    let s0 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(f0, f0),
            fstar::uint128::mul_wide(d4, f1),
        ),
        fstar::uint128::mul_wide(d2, f3),
    );
    let s1 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d0, f1),
            fstar::uint128::mul_wide(d4, f2),
        ),
        fstar::uint128::mul_wide(d3, f3),
    );
    let s2 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d0, f2),
            fstar::uint128::mul_wide(f1, f1),
        ),
        fstar::uint128::mul_wide(d4, f3),
    );
    let s3 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d0, f3),
            fstar::uint128::mul_wide(d1, f2),
        ),
        fstar::uint128::mul_wide(f4, d419),
    );
    let s4 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d0, f4),
            fstar::uint128::mul_wide(d1, f3),
        ),
        fstar::uint128::mul_wide(f2, f2),
    );
    let o0 = s0;
    let o1 = s1;
    let o2 = s2;
    let o3 = s3;
    let o4 = s4;
    let l· = fstar::uint128::add(o0, fstar::uint128::uint64_to_uint128(0u64));
    let tmp0 = uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0 = uint128_to_uint64(fstar::uint128::shift_right(l·, 51u32));
    let l·0 = fstar::uint128::add(o1, fstar::uint128::uint64_to_uint128(c0));
    let tmp1 = uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1 = uint128_to_uint64(fstar::uint128::shift_right(l·0, 51u32));
    let l·1 = fstar::uint128::add(o2, fstar::uint128::uint64_to_uint128(c1));
    let tmp2 = uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2 = uint128_to_uint64(fstar::uint128::shift_right(l·1, 51u32));
    let l·2 = fstar::uint128::add(o3, fstar::uint128::uint64_to_uint128(c2));
    let tmp3 = uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3 = uint128_to_uint64(fstar::uint128::shift_right(l·2, 51u32));
    let l·3 = fstar::uint128::add(o4, fstar::uint128::uint64_to_uint128(c3));
    let tmp4 = uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4 = uint128_to_uint64(fstar::uint128::shift_right(l·3, 51u32));
    let l·4 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0· = l·4 & 0x7ffffffffffffu64;
    let c5 = l·4.wrapping_shr(51u32);
    let o00 = tmp0·;
    let o10 = tmp1.wrapping_add(c5);
    let o20 = tmp2;
    let o30 = tmp3;
    let o40 = tmp4;
    out[0usize] = o00;
    out[1usize] = o10;
    out[2usize] = o20;
    out[3usize] = o30;
    out[4usize] = o40
}

#[inline(always)]
pub fn fsqr2(out: &mut [u64], f: &[u64]) {
    let f10 = f[0usize];
    let f11 = f[1usize];
    let f12 = f[2usize];
    let f13 = f[3usize];
    let f14 = f[4usize];
    let f20 = f[5usize];
    let f21 = f[6usize];
    let f22 = f[7usize];
    let f23 = f[8usize];
    let f24 = f[9usize];
    let d0 = 2u64.wrapping_mul(f10);
    let d1 = 2u64.wrapping_mul(f11);
    let d2 = 38u64.wrapping_mul(f12);
    let d3 = 19u64.wrapping_mul(f13);
    let d419 = 19u64.wrapping_mul(f14);
    let d4 = 2u64.wrapping_mul(d419);
    let s0 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(f10, f10),
            fstar::uint128::mul_wide(d4, f11),
        ),
        fstar::uint128::mul_wide(d2, f13),
    );
    let s1 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d0, f11),
            fstar::uint128::mul_wide(d4, f12),
        ),
        fstar::uint128::mul_wide(d3, f13),
    );
    let s2 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d0, f12),
            fstar::uint128::mul_wide(f11, f11),
        ),
        fstar::uint128::mul_wide(d4, f13),
    );
    let s3 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d0, f13),
            fstar::uint128::mul_wide(d1, f12),
        ),
        fstar::uint128::mul_wide(f14, d419),
    );
    let s4 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d0, f14),
            fstar::uint128::mul_wide(d1, f13),
        ),
        fstar::uint128::mul_wide(f12, f12),
    );
    let o10 = s0;
    let o11 = s1;
    let o12 = s2;
    let o13 = s3;
    let o14 = s4;
    let d00 = 2u64.wrapping_mul(f20);
    let d10 = 2u64.wrapping_mul(f21);
    let d20 = 38u64.wrapping_mul(f22);
    let d30 = 19u64.wrapping_mul(f23);
    let d4190 = 19u64.wrapping_mul(f24);
    let d40 = 2u64.wrapping_mul(d4190);
    let s00 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(f20, f20),
            fstar::uint128::mul_wide(d40, f21),
        ),
        fstar::uint128::mul_wide(d20, f23),
    );
    let s10 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d00, f21),
            fstar::uint128::mul_wide(d40, f22),
        ),
        fstar::uint128::mul_wide(d30, f23),
    );
    let s20 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d00, f22),
            fstar::uint128::mul_wide(f21, f21),
        ),
        fstar::uint128::mul_wide(d40, f23),
    );
    let s30 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d00, f23),
            fstar::uint128::mul_wide(d10, f22),
        ),
        fstar::uint128::mul_wide(f24, d4190),
    );
    let s40 = fstar::uint128::add(
        fstar::uint128::add(
            fstar::uint128::mul_wide(d00, f24),
            fstar::uint128::mul_wide(d10, f23),
        ),
        fstar::uint128::mul_wide(f22, f22),
    );
    let o20 = s00;
    let o21 = s10;
    let o22 = s20;
    let o23 = s30;
    let o24 = s40;
    let l· = fstar::uint128::add(o10, fstar::uint128::uint64_to_uint128(0u64));
    let tmp0 = uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0 = uint128_to_uint64(fstar::uint128::shift_right(l·, 51u32));
    let l·0 = fstar::uint128::add(o11, fstar::uint128::uint64_to_uint128(c0));
    let tmp1 = uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1 = uint128_to_uint64(fstar::uint128::shift_right(l·0, 51u32));
    let l·1 = fstar::uint128::add(o12, fstar::uint128::uint64_to_uint128(c1));
    let tmp2 = uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2 = uint128_to_uint64(fstar::uint128::shift_right(l·1, 51u32));
    let l·2 = fstar::uint128::add(o13, fstar::uint128::uint64_to_uint128(c2));
    let tmp3 = uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3 = uint128_to_uint64(fstar::uint128::shift_right(l·2, 51u32));
    let l·3 = fstar::uint128::add(o14, fstar::uint128::uint64_to_uint128(c3));
    let tmp4 = uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4 = uint128_to_uint64(fstar::uint128::shift_right(l·3, 51u32));
    let l·4 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0· = l·4 & 0x7ffffffffffffu64;
    let c5 = l·4.wrapping_shr(51u32);
    let o101 = tmp0·;
    let o111 = tmp1.wrapping_add(c5);
    let o121 = tmp2;
    let o131 = tmp3;
    let o141 = tmp4;
    let l·5 = fstar::uint128::add(o20, fstar::uint128::uint64_to_uint128(0u64));
    let tmp00 = uint128_to_uint64(l·5) & 0x7ffffffffffffu64;
    let c00 = uint128_to_uint64(fstar::uint128::shift_right(l·5, 51u32));
    let l·6 = fstar::uint128::add(o21, fstar::uint128::uint64_to_uint128(c00));
    let tmp10 = uint128_to_uint64(l·6) & 0x7ffffffffffffu64;
    let c10 = uint128_to_uint64(fstar::uint128::shift_right(l·6, 51u32));
    let l·7 = fstar::uint128::add(o22, fstar::uint128::uint64_to_uint128(c10));
    let tmp20 = uint128_to_uint64(l·7) & 0x7ffffffffffffu64;
    let c20 = uint128_to_uint64(fstar::uint128::shift_right(l·7, 51u32));
    let l·8 = fstar::uint128::add(o23, fstar::uint128::uint64_to_uint128(c20));
    let tmp30 = uint128_to_uint64(l·8) & 0x7ffffffffffffu64;
    let c30 = uint128_to_uint64(fstar::uint128::shift_right(l·8, 51u32));
    let l·9 = fstar::uint128::add(o24, fstar::uint128::uint64_to_uint128(c30));
    let tmp40 = uint128_to_uint64(l·9) & 0x7ffffffffffffu64;
    let c40 = uint128_to_uint64(fstar::uint128::shift_right(l·9, 51u32));
    let l·10 = tmp00.wrapping_add(c40.wrapping_mul(19u64));
    let tmp0·0 = l·10 & 0x7ffffffffffffu64;
    let c50 = l·10.wrapping_shr(51u32);
    let o201 = tmp0·0;
    let o211 = tmp10.wrapping_add(c50);
    let o221 = tmp20;
    let o231 = tmp30;
    let o241 = tmp40;
    let o100 = o101;
    let o110 = o111;
    let o120 = o121;
    let o130 = o131;
    let o140 = o141;
    let o200 = o201;
    let o210 = o211;
    let o220 = o221;
    let o230 = o231;
    let o240 = o241;
    out[0usize] = o100;
    out[1usize] = o110;
    out[2usize] = o120;
    out[3usize] = o130;
    out[4usize] = o140;
    out[5usize] = o200;
    out[6usize] = o210;
    out[7usize] = o220;
    out[8usize] = o230;
    out[9usize] = o240
}

#[inline(always)]
pub fn store_felem(u64s: &mut [u64], f: &[u64]) {
    let f0 = f[0usize];
    let f1 = f[1usize];
    let f2 = f[2usize];
    let f3 = f[3usize];
    let f4 = f[4usize];
    let l· = f0.wrapping_add(0u64);
    let tmp0 = l· & 0x7ffffffffffffu64;
    let c0 = l·.wrapping_shr(51u32);
    let l·0 = f1.wrapping_add(c0);
    let tmp1 = l·0 & 0x7ffffffffffffu64;
    let c1 = l·0.wrapping_shr(51u32);
    let l·1 = f2.wrapping_add(c1);
    let tmp2 = l·1 & 0x7ffffffffffffu64;
    let c2 = l·1.wrapping_shr(51u32);
    let l·2 = f3.wrapping_add(c2);
    let tmp3 = l·2 & 0x7ffffffffffffu64;
    let c3 = l·2.wrapping_shr(51u32);
    let l·3 = f4.wrapping_add(c3);
    let tmp4 = l·3 & 0x7ffffffffffffu64;
    let c4 = l·3.wrapping_shr(51u32);
    let l·4 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0· = l·4 & 0x7ffffffffffffu64;
    let c5 = l·4.wrapping_shr(51u32);
    let f01 = tmp0·;
    let f11 = tmp1.wrapping_add(c5);
    let f21 = tmp2;
    let f31 = tmp3;
    let f41 = tmp4;
    let m0 = fstar::uint64::gte_mask(f01, 0x7ffffffffffedu64);
    let m1 = fstar::uint64::eq_mask(f11, 0x7ffffffffffffu64);
    let m2 = fstar::uint64::eq_mask(f21, 0x7ffffffffffffu64);
    let m3 = fstar::uint64::eq_mask(f31, 0x7ffffffffffffu64);
    let m4 = fstar::uint64::eq_mask(f41, 0x7ffffffffffffu64);
    let mask = m0 & m1 & m2 & m3 & m4;
    let f0· = f01.wrapping_sub(mask & 0x7ffffffffffedu64);
    let f1· = f11.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f2· = f21.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f3· = f31.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f4· = f41.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f02 = f0·;
    let f12 = f1·;
    let f22 = f2·;
    let f32 = f3·;
    let f42 = f4·;
    let o0 = f02 | f12.wrapping_shl(51u32);
    let o1 = f12.wrapping_shr(13u32) | f22.wrapping_shl(38u32);
    let o2 = f22.wrapping_shr(26u32) | f32.wrapping_shl(25u32);
    let o3 = f32.wrapping_shr(39u32) | f42.wrapping_shl(12u32);
    let o00 = o0;
    let o10 = o1;
    let o20 = o2;
    let o30 = o3;
    u64s[0usize] = o00;
    u64s[1usize] = o10;
    u64s[2usize] = o20;
    u64s[3usize] = o30
}

// At the time of writing this appears to be safe, i.e. not being optimized
// away. But this may change in future or with different compilers.
#[inline(always)]
pub fn cswap2(bit: u64, p1: &mut [u64], p2: &mut [u64]) {
    let mask = 0u64.wrapping_sub(bit);
    krml::unroll_for!(10, "i", 0u32, 1u32, {
        let dummy = mask & (p1[i as usize] ^ p2[i as usize]);
        p1[i as usize] ^= dummy;
        p2[i as usize] ^= dummy
    })
}
