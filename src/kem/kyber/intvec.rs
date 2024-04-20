use crate::hax_utils::hax_debug_assert;
use super::arithmetic::*;

pub(crate) const SIZE_VEC : usize = 8;

#[derive(Clone, Copy)]
pub(crate) struct IntVec{
    elements: [FieldElement; 8]
}

#[inline(always)]
pub(crate) fn int_vec_to_i32_array(a:IntVec) -> [i32;8] {
    a.elements
}

#[inline(always)]
pub(crate) fn int_vec_from_i32_array(a:[i32;8]) -> IntVec {
    IntVec {elements: a}
}

pub(crate) const ZERO_VEC : IntVec = 
    IntVec {elements: [0i32; 8]};

#[inline(always)]
pub(crate) fn add_int_vec(
    mut lhs: IntVec,
    rhs: &IntVec,
) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] += rhs.elements[i];
    }
    lhs
}

#[inline(always)]
pub(crate) fn sub_int_vec(
    mut lhs: IntVec,
    rhs: &IntVec,
) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] -= rhs.elements[i];
    }
    lhs
}

#[inline(always)]
pub(crate) fn mul_int_vec_constant(
    mut lhs: IntVec,
    rhs: i32,
) -> IntVec {
    for i in 0..SIZE_VEC {
        lhs.elements[i] *= rhs;
    }
    lhs
}

//#[inline(always)]
// pub(crate) fn mul_int_vec(
//     mut lhs: IntVec,
//     rhs: &IntVec,
// ) -> IntVec {
//     for i in 0..SIZE_VEC {
//         lhs.elements[i] *= rhs.elements[i];
//     }
//     lhs
// }


#[inline(always)]
pub(crate) fn barrett_reduce_int_vec(mut a:IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        a.elements[i] = barrett_reduce(a.elements[i]);
    }
    a
}

#[inline(always)]
pub(crate) fn montgomery_reduce_int_vec(mut a:IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        a.elements[i] = montgomery_reduce(a.elements[i]);
    }
    a
}

#[inline(always)]
pub(crate) fn to_standard_domain_int_vec(mut a:IntVec) -> IntVec {
    for i in 0..SIZE_VEC {
        a.elements[i] = to_standard_domain(a.elements[i]);
    }
    a
}

//#[inline(always)]
// pub(crate) fn montgomery_multiply_fe_by_fer_int_vec(mut a:IntVec, b:i32) -> IntVec {
//     for i in 0..SIZE_VEC {
//         a.elements[i] = montgomery_multiply_fe_by_fer(a.elements[i],b);
//     }
//     a
// }

#[inline(always)]
pub(crate) fn ntt_layer_int_vec_step(mut a:IntVec, mut b:IntVec, step:usize, zeta_r:i32) -> (IntVec,IntVec) {
    if step < 8 {
        //hax_debug_assert!(a == b);
        for i in 0..SIZE_VEC {
            let t = montgomery_multiply_fe_by_fer(
                    a.elements[i + step],
                    zeta_r);
            a.elements[i + step] = a.elements[i] - t;
            a.elements[i] = a.elements[i] + t;
        }
        (a,a)
    } else {
        for i in 0..SIZE_VEC {
            let t = montgomery_multiply_fe_by_fer(
                    b.elements[i + step],
                    zeta_r);
            b.elements[i + step] = a.elements[i] - t;
            a.elements[i] = a.elements[i] + t;
        }
        (a,b)
    }

}

#[inline(always)]
pub(crate) fn inv_ntt_layer_int_vec_step(mut a:IntVec, mut b:IntVec, step:usize, zeta_r:i32) -> (IntVec,IntVec) {
    if step < 8 {
        //hax_debug_assert!(a == b);
        for i in 0..SIZE_VEC {
            let a_minus_b = a.elements[i + step] - a.elements[i];
            a.elements[i] = a.elements[i] + a.elements[i + step];
            a.elements[i + step] =
                montgomery_reduce(a_minus_b * zeta_r);
         }
         (a,a)
    } else {
        for i in 0..SIZE_VEC {
            let a_minus_b = b.elements[i + step] - a.elements[i];
            a.elements[i] = a.elements[i] + b.elements[i + step];
            b.elements[i + step] =
                montgomery_reduce(a_minus_b * zeta_r);
         }
         (a,b)
    }
}

#[inline(always)]
pub(crate) fn ntt_multiply_int_vec(
    lhs: &IntVec,
    rhs: &IntVec,
    zeta0: i32,
    zeta1: i32
) -> IntVec {
    let mut out = ZERO_VEC;
    let product = ntt_multiply_binomials(
        (lhs.elements[0], lhs.elements[1]),
        (rhs.elements[0], rhs.elements[1]),
        zeta0,
    );
    out.elements[0] = product.0;
    out.elements[1] = product.1; 

    let product = ntt_multiply_binomials(
        (lhs.elements[2], lhs.elements[3]),
        (rhs.elements[2], rhs.elements[3]),
        -zeta0,
    );
    out.elements[2] = product.0;
    out.elements[3] = product.1; 

    let product = ntt_multiply_binomials(
        (lhs.elements[4], lhs.elements[5]),
        (rhs.elements[4], rhs.elements[5]),
        zeta1,
    );
    out.elements[4] = product.0;
    out.elements[5] = product.1; 

    let product = ntt_multiply_binomials(
        (lhs.elements[6], lhs.elements[7]),
        (rhs.elements[6], rhs.elements[7]),
        -zeta1,
    );
    out.elements[6] = product.0;
    out.elements[7] = product.1; 
    out
}