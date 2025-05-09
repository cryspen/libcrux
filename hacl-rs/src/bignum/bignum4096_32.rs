#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

use crate::prelude::*;

use libcrux_macros as krml;

/**
Write `a + b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint32_t[128]
*/
pub fn add(a: &[u32], b: &[u32], res: &mut [u32]) -> u32 {
    let mut c: [u32; 1] = [0u32; 1usize];
    krml::unroll_for!(32, "i", 0u32, 1u32, {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u32((&c)[0usize], t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c)[0usize], t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c)[0usize], t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u32((&c)[0usize], t12, t22, res_i2.1)
    });
    (&c)[0usize]
}

/**
Write `a - b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint32_t[128]
*/
pub fn sub(a: &[u32], b: &[u32], res: &mut [u32]) -> u32 {
    let mut c: [u32; 1] = [0u32; 1usize];
    krml::unroll_for!(32, "i", 0u32, 1u32, {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t12, t22, res_i2.1)
    });
    (&c)[0usize]
}

/**
Write `(a + b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
pub fn add_mod(n: &[u32], a: &[u32], b: &[u32], res: &mut [u32]) {
    let mut c: [u32; 1] = [0u32; 1usize];
    krml::unroll_for!(32, "i", 0u32, 1u32, {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u32((&c)[0usize], t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c)[0usize], t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c)[0usize], t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::add_carry_u32((&c)[0usize], t12, t22, res_i2.1)
    });
    let c0: u32 = (&c)[0usize];
    let mut tmp: [u32; 128] = [0u32; 128usize];
    let mut c1: [u32; 1] = [0u32; 1usize];
    krml::unroll_for!(32, "i", 0u32, 1u32, {
        let t1: u32 = res[4u32.wrapping_mul(i) as usize];
        let t2: u32 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = tmp.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c1)[0usize], t1, t2, res_i.1);
        let t10: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c1)[0usize], t10, t20, res_i0.1);
        let t11: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c1)[0usize], t11, t21, res_i1.1);
        let t12: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c1)[0usize], t12, t22, res_i2.1)
    });
    let c10: u32 = (&c1)[0usize];
    let c2: u32 = c0.wrapping_sub(c10);
    for i in 0u32..128u32 {
        let x: u32 = c2 & res[i as usize] | !c2 & (&tmp)[i as usize];
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

/**
Write `(a - b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
pub fn sub_mod(n: &[u32], a: &[u32], b: &[u32], res: &mut [u32]) {
    let mut c: [u32; 1] = [0u32; 1usize];
    krml::unroll_for!(32, "i", 0u32, 1u32, {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t12, t22, res_i2.1)
    });
    let c0: u32 = (&c)[0usize];
    let mut tmp: [u32; 128] = [0u32; 128usize];
    let mut c1: [u32; 1] = [0u32; 1usize];
    krml::unroll_for!(32, "i", 0u32, 1u32, {
        let t1: u32 = res[4u32.wrapping_mul(i) as usize];
        let t2: u32 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = tmp.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] = lib::inttypes_intrinsics::add_carry_u32((&c1)[0usize], t1, t2, res_i.1);
        let t10: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c1)[0usize], t10, t20, res_i0.1);
        let t11: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c1)[0usize], t11, t21, res_i1.1);
        let t12: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c1)[0usize], t12, t22, res_i2.1)
    });
    let c10: u32 = (&c1)[0usize];
    lowstar::ignore::ignore::<u32>(c10);
    let c2: u32 = 0u32.wrapping_sub(c0);
    for i in 0u32..128u32 {
        let x: u32 = c2 & (&tmp)[i as usize] | !c2 & res[i as usize];
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

/**
Write `a * b` in `res`.

  The arguments a and b are meant to be 4096-bit bignums, i.e. uint32_t[128].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint32_t[256].
*/
pub fn mul(a: &[u32], b: &[u32], res: &mut [u32]) {
    let mut tmp: [u32; 512] = [0u32; 512usize];
    super::base::bn_karatsuba_mul_uint32(128u32, a, b, &mut tmp, res)
}

/**
Write `a * a` in `res`.

  The argument a is meant to be a 4096-bit bignum, i.e. uint32_t[128].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint32_t[256].
*/
pub fn sqr(a: &[u32], res: &mut [u32]) {
    let mut tmp: [u32; 512] = [0u32; 512usize];
    super::base::bn_karatsuba_sqr_uint32(128u32, a, &mut tmp, res)
}

#[inline]
fn precompr2(nBits: u32, n: &[u32], res: &mut [u32]) {
    (res[0usize..128usize]).copy_from_slice(&[0u32; 128usize]);
    let i: u32 = nBits.wrapping_div(32u32);
    let j: u32 = nBits.wrapping_rem(32u32);
    res[i as usize] |= 1u32.wrapping_shl(j);
    for _i in 0u32..8192u32.wrapping_sub(nBits) {
        let mut a_copy: [u32; 128] = [0u32; 128usize];
        let mut b_copy: [u32; 128] = [0u32; 128usize];
        ((&mut a_copy)[0usize..128usize]).copy_from_slice(&res[0usize..128usize]);
        ((&mut b_copy)[0usize..128usize]).copy_from_slice(&res[0usize..128usize]);
        super::bignum4096_32::add_mod(n, &a_copy, &b_copy, res)
    }
}

#[inline]
fn reduction(n: &[u32], nInv: u32, c: &mut [u32], res: &mut [u32]) {
    let mut c0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..128u32 {
        let qj: u32 = nInv.wrapping_mul(c[i as usize]);
        let res_j: (&mut [u32], &mut [u32]) = c.split_at_mut(i as usize);
        let mut c1: [u32; 1] = [0u32; 1usize];
        krml::unroll_for!(32, "i0", 0u32, 1u32, {
            let a_i: u32 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            (&mut c1)[0usize] =
                super::bignum_base::mul_wide_add2_u32(a_i, qj, (&c1)[0usize], res_i.1);
            let a_i0: u32 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                super::bignum_base::mul_wide_add2_u32(a_i0, qj, (&c1)[0usize], res_i0.1);
            let a_i1: u32 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                super::bignum_base::mul_wide_add2_u32(a_i1, qj, (&c1)[0usize], res_i1.1);
            let a_i2: u32 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                super::bignum_base::mul_wide_add2_u32(a_i2, qj, (&c1)[0usize], res_i2.1)
        });
        let r: u32 = (&c1)[0usize];
        let c10: u32 = r;
        let res_j0: u32 = c[128u32.wrapping_add(i) as usize];
        let resb: (&mut [u32], &mut [u32]) = c.split_at_mut(i as usize + 128usize);
        (&mut c0)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c0)[0usize], c10, res_j0, resb.1)
    }
    (res[0usize..128usize]).copy_from_slice(&(&c[128usize..])[0usize..128usize]);
    let c00: u32 = (&c0)[0usize];
    let mut tmp: [u32; 128] = [0u32; 128usize];
    let mut c1: [u32; 1] = [0u32; 1usize];
    krml::unroll_for!(32, "i", 0u32, 1u32, {
        let t1: u32 = res[4u32.wrapping_mul(i) as usize];
        let t2: u32 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = tmp.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c1)[0usize], t1, t2, res_i.1);
        let t10: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c1)[0usize], t10, t20, res_i0.1);
        let t11: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c1)[0usize], t11, t21, res_i1.1);
        let t12: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c1)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c1)[0usize], t12, t22, res_i2.1)
    });
    let c10: u32 = (&c1)[0usize];
    let c2: u32 = c00.wrapping_sub(c10);
    for i in 0u32..128u32 {
        let x: u32 = c2 & res[i as usize] | !c2 & (&tmp)[i as usize];
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline]
fn to(n: &[u32], nInv: u32, r2: &[u32], a: &[u32], aM: &mut [u32]) {
    let mut c: [u32; 256] = [0u32; 256usize];
    super::bignum4096_32::mul(a, r2, &mut c);
    super::bignum4096_32::reduction(n, nInv, &mut c, aM)
}

#[inline]
fn from(n: &[u32], nInv_u64: u32, aM: &[u32], a: &mut [u32]) {
    let mut tmp: [u32; 256] = [0u32; 256usize];
    ((&mut tmp)[0usize..128usize]).copy_from_slice(&aM[0usize..128usize]);
    super::bignum4096_32::reduction(n, nInv_u64, &mut tmp, a)
}

#[inline]
fn areduction(n: &[u32], nInv: u32, c: &mut [u32], res: &mut [u32]) {
    let mut c0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..128u32 {
        let qj: u32 = nInv.wrapping_mul(c[i as usize]);
        let res_j: (&mut [u32], &mut [u32]) = c.split_at_mut(i as usize);
        let mut c1: [u32; 1] = [0u32; 1usize];
        krml::unroll_for!(32, "i0", 0u32, 1u32, {
            let a_i: u32 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            (&mut c1)[0usize] =
                super::bignum_base::mul_wide_add2_u32(a_i, qj, (&c1)[0usize], res_i.1);
            let a_i0: u32 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                super::bignum_base::mul_wide_add2_u32(a_i0, qj, (&c1)[0usize], res_i0.1);
            let a_i1: u32 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                super::bignum_base::mul_wide_add2_u32(a_i1, qj, (&c1)[0usize], res_i1.1);
            let a_i2: u32 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            (&mut c1)[0usize] =
                super::bignum_base::mul_wide_add2_u32(a_i2, qj, (&c1)[0usize], res_i2.1)
        });
        let r: u32 = (&c1)[0usize];
        let c10: u32 = r;
        let res_j0: u32 = c[128u32.wrapping_add(i) as usize];
        let resb: (&mut [u32], &mut [u32]) = c.split_at_mut(i as usize + 128usize);
        (&mut c0)[0usize] =
            lib::inttypes_intrinsics::add_carry_u32((&c0)[0usize], c10, res_j0, resb.1)
    }
    (res[0usize..128usize]).copy_from_slice(&(&c[128usize..])[0usize..128usize]);
    let c00: u32 = (&c0)[0usize];
    let mut tmp: [u32; 128] = [0u32; 128usize];
    let c1: u32 = super::bignum4096_32::sub(res, n, &mut tmp);
    lowstar::ignore::ignore::<u32>(c1);
    let m: u32 = 0u32.wrapping_sub(c00);
    for i in 0u32..128u32 {
        let x: u32 = m & (&tmp)[i as usize] | !m & res[i as usize];
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline]
fn amont_mul(n: &[u32], nInv_u64: u32, aM: &[u32], bM: &[u32], resM: &mut [u32]) {
    let mut c: [u32; 256] = [0u32; 256usize];
    super::bignum4096_32::mul(aM, bM, &mut c);
    super::bignum4096_32::areduction(n, nInv_u64, &mut c, resM)
}

#[inline]
fn amont_sqr(n: &[u32], nInv_u64: u32, aM: &[u32], resM: &mut [u32]) {
    let mut c: [u32; 256] = [0u32; 256usize];
    super::bignum4096_32::sqr(aM, &mut c);
    super::bignum4096_32::areduction(n, nInv_u64, &mut c, resM)
}

#[inline]
fn bn_slow_precomp(n: &[u32], mu: u32, r2: &[u32], a: &[u32], res: &mut [u32]) {
    let mut a_mod: [u32; 128] = [0u32; 128usize];
    let mut a1: [u32; 256] = [0u32; 256usize];
    ((&mut a1)[0usize..256usize]).copy_from_slice(&a[0usize..256usize]);
    super::bignum4096_32::areduction(n, mu, &mut a1, &mut a_mod);
    super::bignum4096_32::to(n, mu, r2, &a_mod, res)
}

/**
Write `a mod n` in `res`.

  The argument a is meant to be a 8192-bit bignum, i.e. uint32_t[256].
  The argument n and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1
*/
pub fn r#mod(n: &[u32], a: &[u32], res: &mut [u32]) -> bool {
    let mut one: [u32; 128] = [0u32; 128usize];
    ((&mut one)[0usize..128usize]).copy_from_slice(&[0u32; 128usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..128u32 {
        let beq: u32 = fstar::uint32::eq_mask((&one)[i as usize], n[i as usize]);
        let blt: u32 = !fstar::uint32::gte_mask((&one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] = beq & (&acc)[0usize] | !beq & blt
    }
    let m1: u32 = (&acc)[0usize];
    let is_valid_m: u32 = m0 & m1;
    let nBits: u32 = 32u32.wrapping_mul(super::bignum_base::bn_get_top_index_u32(128u32, n));
    if is_valid_m == 0xFFFFFFFFu32 {
        let mut r2: [u32; 128] = [0u32; 128usize];
        super::bignum4096_32::precompr2(nBits, n, &mut r2);
        let mu: u32 = super::base::mod_inv_uint32(n[0usize]);
        super::bignum4096_32::bn_slow_precomp(n, mu, &r2, a, res)
    } else {
        (res[0usize..128usize]).copy_from_slice(&[0u32; 128usize])
    };
    is_valid_m == 0xFFFFFFFFu32
}

fn exp_check(n: &[u32], a: &[u32], bBits: u32, b: &[u32]) -> u32 {
    let mut one: [u32; 128] = [0u32; 128usize];
    ((&mut one)[0usize..128usize]).copy_from_slice(&[0u32; 128usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..128u32 {
        let beq: u32 = fstar::uint32::eq_mask((&one)[i as usize], n[i as usize]);
        let blt: u32 = !fstar::uint32::gte_mask((&one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] = beq & (&acc)[0usize] | !beq & blt
    }
    let m1: u32 = (&acc)[0usize];
    let m00: u32 = m0 & m1;
    let bLen: u32 = if bBits == 0u32 {
        1u32
    } else {
        bBits
            .wrapping_sub(1u32)
            .wrapping_div(32u32)
            .wrapping_add(1u32)
    };
    let m10: u32 = if bBits < 32u32.wrapping_mul(bLen) {
        let mut b2: Box<[u32]> = vec![0u32; bLen as usize].into_boxed_slice();
        let i: u32 = bBits.wrapping_div(32u32);
        let j: u32 = bBits.wrapping_rem(32u32);
        (&mut b2)[i as usize] = (&b2)[i as usize] | 1u32.wrapping_shl(j);
        let mut acc0: [u32; 1] = [0u32; 1usize];
        for i0 in 0u32..bLen {
            let beq: u32 = fstar::uint32::eq_mask(b[i0 as usize], (&b2)[i0 as usize]);
            let blt: u32 = !fstar::uint32::gte_mask(b[i0 as usize], (&b2)[i0 as usize]);
            (&mut acc0)[0usize] = beq & (&acc0)[0usize] | !beq & blt
        }
        let res: u32 = (&acc0)[0usize];
        res
    } else {
        0xFFFFFFFFu32
    };
    let mut acc0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..128u32 {
        let beq: u32 = fstar::uint32::eq_mask(a[i as usize], n[i as usize]);
        let blt: u32 = !fstar::uint32::gte_mask(a[i as usize], n[i as usize]);
        (&mut acc0)[0usize] = beq & (&acc0)[0usize] | !beq & blt
    }
    let m2: u32 = (&acc0)[0usize];
    let m: u32 = m10 & m2;
    m00 & m
}

#[inline]
fn exp_vartime_precomp(
    n: &[u32],
    mu: u32,
    r2: &[u32],
    a: &[u32],
    bBits: u32,
    b: &[u32],
    res: &mut [u32],
) {
    if bBits < 200u32 {
        let mut aM: [u32; 128] = [0u32; 128usize];
        super::bignum4096_32::to(n, mu, r2, a, &mut aM);
        let mut resM: [u32; 128] = [0u32; 128usize];
        let mut ctx: [u32; 256] = [0u32; 256usize];
        ((&mut ctx)[0usize..128usize]).copy_from_slice(&n[0usize..128usize]);
        ((&mut ctx)[128usize..128usize + 128usize]).copy_from_slice(&r2[0usize..128usize]);
        let ctx_n: (&[u32], &[u32]) = ctx.split_at(0usize);
        let ctx_r2: (&[u32], &[u32]) = ctx_n.1.split_at(128usize);
        super::bignum4096_32::from(ctx_r2.0, mu, ctx_r2.1, &mut resM);
        lowstar::ignore::ignore::<&[u32]>(&ctx);
        for i in 0u32..bBits {
            let i1: u32 = i.wrapping_div(32u32);
            let j: u32 = i.wrapping_rem(32u32);
            let tmp: u32 = b[i1 as usize];
            let bit: u32 = tmp.wrapping_shr(j) & 1u32;
            if bit != 0u32 {
                let mut aM_copy: [u32; 128] = [0u32; 128usize];
                ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&(&resM)[0usize..128usize]);
                let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
                super::bignum4096_32::amont_mul(ctx_n0.1, mu, &aM_copy, &aM, &mut resM);
                lowstar::ignore::ignore::<&[u32]>(&ctx)
            };
            let mut aM_copy: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&(&aM)[0usize..128usize]);
            let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_sqr(ctx_n0.1, mu, &aM_copy, &mut aM);
            lowstar::ignore::ignore::<&[u32]>(&ctx)
        }
        super::bignum4096_32::from(n, mu, &resM, res)
    } else {
        let mut aM: [u32; 128] = [0u32; 128usize];
        super::bignum4096_32::to(n, mu, r2, a, &mut aM);
        let mut resM: [u32; 128] = [0u32; 128usize];
        let bLen: u32 = if bBits == 0u32 {
            1u32
        } else {
            bBits
                .wrapping_sub(1u32)
                .wrapping_div(32u32)
                .wrapping_add(1u32)
        };
        let mut ctx: [u32; 256] = [0u32; 256usize];
        ((&mut ctx)[0usize..128usize]).copy_from_slice(&n[0usize..128usize]);
        ((&mut ctx)[128usize..128usize + 128usize]).copy_from_slice(&r2[0usize..128usize]);
        let mut table: [u32; 2048] = [0u32; 2048usize];
        let mut tmp: [u32; 128] = [0u32; 128usize];
        let t0: (&mut [u32], &mut [u32]) = table.split_at_mut(0usize);
        let t1: (&mut [u32], &mut [u32]) = t0.1.split_at_mut(128usize);
        let ctx_n: (&[u32], &[u32]) = ctx.split_at(0usize);
        let ctx_r2: (&[u32], &[u32]) = ctx_n.1.split_at(128usize);
        super::bignum4096_32::from(ctx_r2.0, mu, ctx_r2.1, t1.0);
        lowstar::ignore::ignore::<&[u32]>(&ctx);
        (t1.1[0usize..128usize]).copy_from_slice(&(&aM)[0usize..128usize]);
        lowstar::ignore::ignore::<&[u32]>(&table);
        krml::unroll_for!(7, "i", 0u32, 1u32, {
            let t11: (&[u32], &[u32]) =
                table.split_at(i.wrapping_add(1u32).wrapping_mul(128u32) as usize);
            let mut aM_copy: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&t11.1[0usize..128usize]);
            let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_sqr(ctx_n0.1, mu, &aM_copy, &mut tmp);
            lowstar::ignore::ignore::<&[u32]>(&ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(128u32) as usize
                ..2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(128u32) as usize
                    + 128usize])
                .copy_from_slice(&(&tmp)[0usize..128usize]);
            let t2: (&[u32], &[u32]) = table
                .split_at(2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(128u32) as usize);
            let mut aM_copy0: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy0)[0usize..128usize]).copy_from_slice(&(&aM)[0usize..128usize]);
            let ctx_n1: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_mul(ctx_n1.1, mu, &aM_copy0, t2.1, &mut tmp);
            lowstar::ignore::ignore::<&[u32]>(&ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(128u32) as usize
                ..2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(128u32) as usize + 128usize])
                .copy_from_slice(&(&tmp)[0usize..128usize])
        });
        if bBits.wrapping_rem(4u32) != 0u32 {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u32 = super::bignum_base::bn_get_bits_u32(bLen, b, i, 4u32);
            let bits_l32: u32 = bits_c;
            let a_bits_l: (&[u32], &[u32]) = table.split_at(bits_l32.wrapping_mul(128u32) as usize);
            ((&mut resM)[0usize..128usize]).copy_from_slice(&a_bits_l.1[0usize..128usize])
        } else {
            let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
            let ctx_r20: (&[u32], &[u32]) = ctx_n0.1.split_at(128usize);
            super::bignum4096_32::from(ctx_r20.0, mu, ctx_r20.1, &mut resM);
            lowstar::ignore::ignore::<&[u32]>(&ctx)
        };
        let mut tmp0: [u32; 128] = [0u32; 128usize];
        for i in 0u32..bBits.wrapping_div(4u32) {
            krml::unroll_for!(4, "_i", 0u32, 1u32, {
                let mut aM_copy: [u32; 128] = [0u32; 128usize];
                ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&(&resM)[0usize..128usize]);
                let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
                super::bignum4096_32::amont_sqr(ctx_n0.1, mu, &aM_copy, &mut resM);
                lowstar::ignore::ignore::<&[u32]>(&ctx)
            });
            let k: u32 = bBits
                .wrapping_sub(bBits.wrapping_rem(4u32))
                .wrapping_sub(4u32.wrapping_mul(i))
                .wrapping_sub(4u32);
            let bits_l: u32 = super::bignum_base::bn_get_bits_u32(bLen, b, k, 4u32);
            lowstar::ignore::ignore::<&[u32]>(&table);
            let bits_l32: u32 = bits_l;
            let a_bits_l: (&[u32], &[u32]) = table.split_at(bits_l32.wrapping_mul(128u32) as usize);
            ((&mut tmp0)[0usize..128usize]).copy_from_slice(&a_bits_l.1[0usize..128usize]);
            let mut aM_copy: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&(&resM)[0usize..128usize]);
            let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_mul(ctx_n0.1, mu, &aM_copy, &tmp0, &mut resM);
            lowstar::ignore::ignore::<&[u32]>(&ctx)
        }
        super::bignum4096_32::from(n, mu, &resM, res)
    }
}

#[inline]
fn exp_consttime_precomp(
    n: &[u32],
    mu: u32,
    r2: &[u32],
    a: &[u32],
    bBits: u32,
    b: &[u32],
    res: &mut [u32],
) {
    if bBits < 200u32 {
        let mut aM: [u32; 128] = [0u32; 128usize];
        super::bignum4096_32::to(n, mu, r2, a, &mut aM);
        let mut resM: [u32; 128] = [0u32; 128usize];
        let mut ctx: [u32; 256] = [0u32; 256usize];
        ((&mut ctx)[0usize..128usize]).copy_from_slice(&n[0usize..128usize]);
        ((&mut ctx)[128usize..128usize + 128usize]).copy_from_slice(&r2[0usize..128usize]);
        let mut sw: [u32; 1] = [0u32; 1usize];
        let ctx_n: (&[u32], &[u32]) = ctx.split_at(0usize);
        let ctx_r2: (&[u32], &[u32]) = ctx_n.1.split_at(128usize);
        super::bignum4096_32::from(ctx_r2.0, mu, ctx_r2.1, &mut resM);
        lowstar::ignore::ignore::<&[u32]>(&ctx);
        for i in 0u32..bBits {
            let i1: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_div(32u32);
            let j: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_rem(32u32);
            let tmp: u32 = b[i1 as usize];
            let bit: u32 = tmp.wrapping_shr(j) & 1u32;
            let sw1: u32 = bit ^ (&sw)[0usize];
            for i0 in 0u32..128u32 {
                let dummy: u32 =
                    0u32.wrapping_sub(sw1) & ((&resM)[i0 as usize] ^ (&aM)[i0 as usize]);
                (&mut resM)[i0 as usize] = (&resM)[i0 as usize] ^ dummy;
                (&mut aM)[i0 as usize] = (&aM)[i0 as usize] ^ dummy
            }
            let mut aM_copy: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&(&aM)[0usize..128usize]);
            let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_mul(ctx_n0.1, mu, &aM_copy, &resM, &mut aM);
            lowstar::ignore::ignore::<&[u32]>(&ctx);
            let mut aM_copy0: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy0)[0usize..128usize]).copy_from_slice(&(&resM)[0usize..128usize]);
            let ctx_n1: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_sqr(ctx_n1.1, mu, &aM_copy0, &mut resM);
            lowstar::ignore::ignore::<&[u32]>(&ctx);
            (&mut sw)[0usize] = bit
        }
        let sw0: u32 = (&sw)[0usize];
        for i in 0u32..128u32 {
            let dummy: u32 = 0u32.wrapping_sub(sw0) & ((&resM)[i as usize] ^ (&aM)[i as usize]);
            (&mut resM)[i as usize] = (&resM)[i as usize] ^ dummy;
            (&mut aM)[i as usize] = (&aM)[i as usize] ^ dummy
        }
        super::bignum4096_32::from(n, mu, &resM, res)
    } else {
        let mut aM: [u32; 128] = [0u32; 128usize];
        super::bignum4096_32::to(n, mu, r2, a, &mut aM);
        let mut resM: [u32; 128] = [0u32; 128usize];
        let bLen: u32 = if bBits == 0u32 {
            1u32
        } else {
            bBits
                .wrapping_sub(1u32)
                .wrapping_div(32u32)
                .wrapping_add(1u32)
        };
        let mut ctx: [u32; 256] = [0u32; 256usize];
        ((&mut ctx)[0usize..128usize]).copy_from_slice(&n[0usize..128usize]);
        ((&mut ctx)[128usize..128usize + 128usize]).copy_from_slice(&r2[0usize..128usize]);
        let mut table: [u32; 2048] = [0u32; 2048usize];
        let mut tmp: [u32; 128] = [0u32; 128usize];
        let t0: (&mut [u32], &mut [u32]) = table.split_at_mut(0usize);
        let t1: (&mut [u32], &mut [u32]) = t0.1.split_at_mut(128usize);
        let ctx_n: (&[u32], &[u32]) = ctx.split_at(0usize);
        let ctx_r2: (&[u32], &[u32]) = ctx_n.1.split_at(128usize);
        super::bignum4096_32::from(ctx_r2.0, mu, ctx_r2.1, t1.0);
        lowstar::ignore::ignore::<&[u32]>(&ctx);
        (t1.1[0usize..128usize]).copy_from_slice(&(&aM)[0usize..128usize]);
        lowstar::ignore::ignore::<&[u32]>(&table);
        krml::unroll_for!(7, "i", 0u32, 1u32, {
            let t11: (&[u32], &[u32]) =
                table.split_at(i.wrapping_add(1u32).wrapping_mul(128u32) as usize);
            let mut aM_copy: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&t11.1[0usize..128usize]);
            let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_sqr(ctx_n0.1, mu, &aM_copy, &mut tmp);
            lowstar::ignore::ignore::<&[u32]>(&ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(128u32) as usize
                ..2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(128u32) as usize
                    + 128usize])
                .copy_from_slice(&(&tmp)[0usize..128usize]);
            let t2: (&[u32], &[u32]) = table
                .split_at(2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(128u32) as usize);
            let mut aM_copy0: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy0)[0usize..128usize]).copy_from_slice(&(&aM)[0usize..128usize]);
            let ctx_n1: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_mul(ctx_n1.1, mu, &aM_copy0, t2.1, &mut tmp);
            lowstar::ignore::ignore::<&[u32]>(&ctx);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(128u32) as usize
                ..2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(128u32) as usize + 128usize])
                .copy_from_slice(&(&tmp)[0usize..128usize])
        });
        if bBits.wrapping_rem(4u32) != 0u32 {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u32 = super::bignum_base::bn_get_bits_u32(bLen, b, i, 4u32);
            ((&mut resM)[0usize..128usize])
                .copy_from_slice(&(&(&table)[0usize..] as &[u32])[0usize..128usize]);
            krml::unroll_for!(15, "i0", 0u32, 1u32, {
                let c: u32 = fstar::uint32::eq_mask(bits_c, i0.wrapping_add(1u32));
                let res_j: (&[u32], &[u32]) =
                    table.split_at(i0.wrapping_add(1u32).wrapping_mul(128u32) as usize);
                for i1 in 0u32..128u32 {
                    let x: u32 = c & res_j.1[i1 as usize] | !c & (&resM)[i1 as usize];
                    let os: (&mut [u32], &mut [u32]) = resM.split_at_mut(0usize);
                    os.1[i1 as usize] = x
                }
            })
        } else {
            let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
            let ctx_r20: (&[u32], &[u32]) = ctx_n0.1.split_at(128usize);
            super::bignum4096_32::from(ctx_r20.0, mu, ctx_r20.1, &mut resM);
            lowstar::ignore::ignore::<&[u32]>(&ctx)
        };
        let mut tmp0: [u32; 128] = [0u32; 128usize];
        for i in 0u32..bBits.wrapping_div(4u32) {
            krml::unroll_for!(4, "_i", 0u32, 1u32, {
                let mut aM_copy: [u32; 128] = [0u32; 128usize];
                ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&(&resM)[0usize..128usize]);
                let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
                super::bignum4096_32::amont_sqr(ctx_n0.1, mu, &aM_copy, &mut resM);
                lowstar::ignore::ignore::<&[u32]>(&ctx)
            });
            let k: u32 = bBits
                .wrapping_sub(bBits.wrapping_rem(4u32))
                .wrapping_sub(4u32.wrapping_mul(i))
                .wrapping_sub(4u32);
            let bits_l: u32 = super::bignum_base::bn_get_bits_u32(bLen, b, k, 4u32);
            lowstar::ignore::ignore::<&[u32]>(&table);
            ((&mut tmp0)[0usize..128usize])
                .copy_from_slice(&(&(&table)[0usize..] as &[u32])[0usize..128usize]);
            krml::unroll_for!(15, "i0", 0u32, 1u32, {
                let c: u32 = fstar::uint32::eq_mask(bits_l, i0.wrapping_add(1u32));
                let res_j: (&[u32], &[u32]) =
                    table.split_at(i0.wrapping_add(1u32).wrapping_mul(128u32) as usize);
                for i1 in 0u32..128u32 {
                    let x: u32 = c & res_j.1[i1 as usize] | !c & (&tmp0)[i1 as usize];
                    let os: (&mut [u32], &mut [u32]) = tmp0.split_at_mut(0usize);
                    os.1[i1 as usize] = x
                }
            });
            let mut aM_copy: [u32; 128] = [0u32; 128usize];
            ((&mut aM_copy)[0usize..128usize]).copy_from_slice(&(&resM)[0usize..128usize]);
            let ctx_n0: (&[u32], &[u32]) = ctx.split_at(0usize);
            super::bignum4096_32::amont_mul(ctx_n0.1, mu, &aM_copy, &tmp0, &mut resM);
            lowstar::ignore::ignore::<&[u32]>(&ctx)
        }
        super::bignum4096_32::from(n, mu, &resM, res)
    }
}

#[inline]
fn exp_vartime(nBits: u32, n: &[u32], a: &[u32], bBits: u32, b: &[u32], res: &mut [u32]) {
    let mut r2: [u32; 128] = [0u32; 128usize];
    super::bignum4096_32::precompr2(nBits, n, &mut r2);
    let mu: u32 = super::base::mod_inv_uint32(n[0usize]);
    super::bignum4096_32::exp_vartime_precomp(n, mu, &r2, a, bBits, b, res)
}

#[inline]
fn exp_consttime(nBits: u32, n: &[u32], a: &[u32], bBits: u32, b: &[u32], res: &mut [u32]) {
    let mut r2: [u32; 128] = [0u32; 128usize];
    super::bignum4096_32::precompr2(nBits, n, &mut r2);
    let mu: u32 = super::base::mod_inv_uint32(n[0usize]);
    super::bignum4096_32::exp_consttime_precomp(n, mu, &r2, a, bBits, b, res)
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n
*/
pub fn mod_exp_vartime(n: &[u32], a: &[u32], bBits: u32, b: &[u32], res: &mut [u32]) -> bool {
    let is_valid_m: u32 = super::bignum4096_32::exp_check(n, a, bBits, b);
    let nBits: u32 = 32u32.wrapping_mul(super::bignum_base::bn_get_top_index_u32(128u32, n));
    if is_valid_m == 0xFFFFFFFFu32 {
        super::bignum4096_32::exp_vartime(nBits, n, a, bBits, b, res)
    } else {
        (res[0usize..128usize]).copy_from_slice(&[0u32; 128usize])
    };
    is_valid_m == 0xFFFFFFFFu32
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n
*/
pub fn mod_exp_consttime(n: &[u32], a: &[u32], bBits: u32, b: &[u32], res: &mut [u32]) -> bool {
    let is_valid_m: u32 = super::bignum4096_32::exp_check(n, a, bBits, b);
    let nBits: u32 = 32u32.wrapping_mul(super::bignum_base::bn_get_top_index_u32(128u32, n));
    if is_valid_m == 0xFFFFFFFFu32 {
        super::bignum4096_32::exp_consttime(nBits, n, a, bBits, b, res)
    } else {
        (res[0usize..128usize]).copy_from_slice(&[0u32; 128usize])
    };
    is_valid_m == 0xFFFFFFFFu32
}

/**
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n
*/
pub fn mod_inv_prime_vartime(n: &[u32], a: &[u32], res: &mut [u32]) -> bool {
    let mut one: [u32; 128] = [0u32; 128usize];
    ((&mut one)[0usize..128usize]).copy_from_slice(&[0u32; 128usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..128u32 {
        let beq: u32 = fstar::uint32::eq_mask((&one)[i as usize], n[i as usize]);
        let blt: u32 = !fstar::uint32::gte_mask((&one)[i as usize], n[i as usize]);
        (&mut acc)[0usize] = beq & (&acc)[0usize] | !beq & blt
    }
    let m1: u32 = (&acc)[0usize];
    let m00: u32 = m0 & m1;
    let bn_zero: [u32; 128] = [0u32; 128usize];
    let mut mask: [u32; 1] = [0xFFFFFFFFu32; 1usize];
    for i in 0u32..128u32 {
        let uu____0: u32 = fstar::uint32::eq_mask(a[i as usize], (&bn_zero)[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mask)[0usize]
    }
    let mask1: u32 = (&mask)[0usize];
    let res1: u32 = mask1;
    let m10: u32 = res1;
    let mut acc0: [u32; 1] = [0u32; 1usize];
    for i in 0u32..128u32 {
        let beq: u32 = fstar::uint32::eq_mask(a[i as usize], n[i as usize]);
        let blt: u32 = !fstar::uint32::gte_mask(a[i as usize], n[i as usize]);
        (&mut acc0)[0usize] = beq & (&acc0)[0usize] | !beq & blt
    }
    let m2: u32 = (&acc0)[0usize];
    let is_valid_m: u32 = m00 & !m10 & m2;
    let nBits: u32 = 32u32.wrapping_mul(super::bignum_base::bn_get_top_index_u32(128u32, n));
    if is_valid_m == 0xFFFFFFFFu32 {
        let mut n2: [u32; 128] = [0u32; 128usize];
        let c0: u32 = lib::inttypes_intrinsics::sub_borrow_u32(
            0u32,
            n[0usize],
            2u32,
            &mut (&mut n2)[0usize..],
        );
        let a1: (&[u32], &[u32]) = n.split_at(1usize);
        let res10: (&mut [u32], &mut [u32]) = n2.split_at_mut(1usize);
        let mut c: [u32; 1] = [c0; 1usize];
        krml::unroll_for!(31, "i", 0u32, 1u32, {
            let t1: u32 = a1.1[4u32.wrapping_mul(i) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res10.1.split_at_mut(4u32.wrapping_mul(i) as usize);
            (&mut c)[0usize] =
                lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, 0u32, res_i.1);
            let t10: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t10, 0u32, res_i0.1);
            let t11: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t11, 0u32, res_i1.1);
            let t12: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t12, 0u32, res_i2.1)
        });
        krml::unroll_for!(3, "i", 124u32, 1u32, {
            let t1: u32 = a1.1[i as usize];
            let res_i: (&mut [u32], &mut [u32]) = res10.1.split_at_mut(i as usize);
            (&mut c)[0usize] =
                lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, 0u32, res_i.1)
        });
        let c1: u32 = (&c)[0usize];
        let c2: u32 = c1;
        lowstar::ignore::ignore::<u32>(c2);
        super::bignum4096_32::exp_vartime(nBits, n, a, 4096u32, &n2, res)
    } else {
        (res[0usize..128usize]).copy_from_slice(&[0u32; 128usize])
    };
    is_valid_m == 0xFFFFFFFFu32
}

/**
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be a 4096-bit bignum, i.e. uint32_t[128].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum4096_mont_ctx_free on the return value
  to avoid memory leaks.
*/
pub fn mont_ctx_init(n: &[u32]) -> Box<[super::base::bn_mont_ctx_u32]> {
    let mut r2: Box<[u32]> = vec![0u32; 128usize].into_boxed_slice();
    let mut n1: Box<[u32]> = vec![0u32; 128usize].into_boxed_slice();
    let r21: &mut [u32] = &mut r2;
    let n11: &mut [u32] = &mut n1;
    (n11[0usize..128usize]).copy_from_slice(&n[0usize..128usize]);
    let nBits: u32 = 32u32.wrapping_mul(super::bignum_base::bn_get_top_index_u32(128u32, n));
    super::bignum4096_32::precompr2(nBits, n, r21);
    let mu: u32 = super::base::mod_inv_uint32(n[0usize]);
    let res: super::base::bn_mont_ctx_u32 = super::base::bn_mont_ctx_u32 {
        len: 128u32,
        n: (*n11).into(),
        mu,
        r2: (*r21).into(),
    };
    let buf: Box<[super::base::bn_mont_ctx_u32]> = vec![res].into_boxed_slice();
    buf
}

/**
Write `a mod n` in `res`.

  The argument a is meant to be a 8192-bit bignum, i.e. uint32_t[256].
  The outparam res is meant to be a 4096-bit bignum, i.e. uint32_t[128].
  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.
*/
pub fn mod_precomp(k: &[super::base::bn_mont_ctx_u32], a: &[u32], res: &mut [u32]) {
    let n: &[u32] = &(k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &[u32] = &(k[0usize]).r2;
    super::bignum4096_32::bn_slow_precomp(n, mu, r2, a, res)
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].
  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
pub fn mod_exp_vartime_precomp(
    k: &[super::base::bn_mont_ctx_u32],
    a: &[u32],
    bBits: u32,
    b: &[u32],
    res: &mut [u32],
) {
    let n: &[u32] = &(k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &[u32] = &(k[0usize]).r2;
    super::bignum4096_32::exp_vartime_precomp(n, mu, r2, a, bBits, b, res)
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].
  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
pub fn mod_exp_consttime_precomp(
    k: &[super::base::bn_mont_ctx_u32],
    a: &[u32],
    bBits: u32,
    b: &[u32],
    res: &mut [u32],
) {
    let n: &[u32] = &(k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &[u32] = &(k[0usize]).r2;
    super::bignum4096_32::exp_consttime_precomp(n, mu, r2, a, bBits, b, res)
}

/**
Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be 4096-bit bignums, i.e. uint32_t[128].
  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n
*/
pub fn mod_inv_prime_vartime_precomp(
    k: &[super::base::bn_mont_ctx_u32],
    a: &[u32],
    res: &mut [u32],
) {
    let n: &[u32] = &(k[0usize]).n;
    let mu: u32 = (k[0usize]).mu;
    let r2: &[u32] = &(k[0usize]).r2;
    let mut n2: [u32; 128] = [0u32; 128usize];
    let c0: u32 =
        lib::inttypes_intrinsics::sub_borrow_u32(0u32, n[0usize], 2u32, &mut (&mut n2)[0usize..]);
    let a1: (&[u32], &[u32]) = n.split_at(1usize);
    let res1: (&mut [u32], &mut [u32]) = n2.split_at_mut(1usize);
    let mut c: [u32; 1] = [c0; 1usize];
    krml::unroll_for!(31, "i", 0u32, 1u32, {
        let t1: u32 = a1.1[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res1.1.split_at_mut(4u32.wrapping_mul(i) as usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, 0u32, res_i.1);
        let t10: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t10, 0u32, res_i0.1);
        let t11: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t11, 0u32, res_i1.1);
        let t12: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        (&mut c)[0usize] =
            lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t12, 0u32, res_i2.1)
    });
    krml::unroll_for!(3, "i", 124u32, 1u32, {
        let t1: u32 = a1.1[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res1.1.split_at_mut(i as usize);
        (&mut c)[0usize] = lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, 0u32, res_i.1)
    });
    let c1: u32 = (&c)[0usize];
    let c2: u32 = c1;
    lowstar::ignore::ignore::<u32>(c2);
    super::bignum4096_32::exp_vartime_precomp(n, mu, r2, a, 4096u32, &n2, res)
}

/**
Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
pub fn new_bn_from_bytes_be(len: u32, b: &[u8]) -> Box<[u32]> {
    if len == 0u32 || len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) > 1073741823u32 {
        [].into()
    } else {
        let mut res: Box<[u32]> =
            vec![0u32; len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) as usize]
                .into_boxed_slice();
        if false {
            res
        } else {
            let res1: &mut [u32] = &mut res;
            let res2: &mut [u32] = res1;
            let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32);
            let tmpLen: u32 = 4u32.wrapping_mul(bnLen);
            let mut tmp: Box<[u8]> = vec![0u8; tmpLen as usize].into_boxed_slice();
            ((&mut tmp)[tmpLen.wrapping_sub(len) as usize
                ..tmpLen.wrapping_sub(len) as usize + len as usize])
                .copy_from_slice(&b[0usize..len as usize]);
            for i in 0u32..bnLen {
                let u: u32 = lowstar::endianness::load32_be(
                    &(&tmp)[bnLen.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(4u32) as usize..],
                );
                let x: u32 = u;
                let os: (&mut [u32], &mut [u32]) = res2.split_at_mut(0usize);
                os.1[i as usize] = x
            }
            (*res2).into()
        }
    }
}

/**
Load a little-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
pub fn new_bn_from_bytes_le(len: u32, b: &[u8]) -> Box<[u32]> {
    if len == 0u32 || len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) > 1073741823u32 {
        [].into()
    } else {
        let mut res: Box<[u32]> =
            vec![0u32; len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) as usize]
                .into_boxed_slice();
        if false {
            res
        } else {
            let res1: &mut [u32] = &mut res;
            let res2: &mut [u32] = res1;
            let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32);
            let tmpLen: u32 = 4u32.wrapping_mul(bnLen);
            let mut tmp: Box<[u8]> = vec![0u8; tmpLen as usize].into_boxed_slice();
            ((&mut tmp)[0usize..len as usize]).copy_from_slice(&b[0usize..len as usize]);
            for i in 0u32..len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32) {
                let bj: (&[u8], &[u8]) = tmp.split_at(i.wrapping_mul(4u32) as usize);
                let u: u32 = lowstar::endianness::load32_le(bj.1);
                let r1: u32 = u;
                let x: u32 = r1;
                let os: (&mut [u32], &mut [u32]) = res2.split_at_mut(0usize);
                os.1[i as usize] = x
            }
            (*res2).into()
        }
    }
}

/**
Serialize a bignum into big-endian memory.

  The argument b points to a 4096-bit bignum.
  The outparam res points to 512 bytes of valid memory.
*/
pub fn bn_to_bytes_be(b: &[u32], res: &mut [u8]) {
    let tmp: [u8; 512] = [0u8; 512usize];
    lowstar::ignore::ignore::<&[u8]>(&tmp);
    for i in 0u32..128u32 {
        lowstar::endianness::store32_be(
            &mut res[i.wrapping_mul(4u32) as usize..],
            b[128u32.wrapping_sub(i).wrapping_sub(1u32) as usize],
        )
    }
}

/**
Serialize a bignum into little-endian memory.

  The argument b points to a 4096-bit bignum.
  The outparam res points to 512 bytes of valid memory.
*/
pub fn bn_to_bytes_le(b: &[u32], res: &mut [u8]) {
    let tmp: [u8; 512] = [0u8; 512usize];
    lowstar::ignore::ignore::<&[u8]>(&tmp);
    for i in 0u32..128u32 {
        lowstar::endianness::store32_le(&mut res[i.wrapping_mul(4u32) as usize..], b[i as usize])
    }
}

/**
Returns 2^32 - 1 if a < b, otherwise returns 0.

 The arguments a and b are meant to be 4096-bit bignums, i.e. uint32_t[128].
*/
pub fn lt_mask(a: &[u32], b: &[u32]) -> u32 {
    let mut acc: [u32; 1] = [0u32; 1usize];
    for i in 0u32..128u32 {
        let beq: u32 = fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        let blt: u32 = !fstar::uint32::gte_mask(a[i as usize], b[i as usize]);
        (&mut acc)[0usize] = beq & (&acc)[0usize] | !beq & blt
    }
    (&acc)[0usize]
}

/**
Returns 2^32 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be 4096-bit bignums, i.e. uint32_t[128].
*/
pub fn eq_mask(a: &[u32], b: &[u32]) -> u32 {
    let mut mask: [u32; 1] = [0xFFFFFFFFu32; 1usize];
    for i in 0u32..128u32 {
        let uu____0: u32 = fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mask)[0usize]
    }
    let mask1: u32 = (&mask)[0usize];
    mask1
}
