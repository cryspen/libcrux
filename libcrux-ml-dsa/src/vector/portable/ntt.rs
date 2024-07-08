use super::arithmetic::*;
use super::vector_type::*;

#[inline(always)]
pub fn ntt_at_layer_1(mut vector: PortableVector, zeta1: i32, zeta2: i32) -> PortableVector {
    let t = montgomery_multiply_fe_by_fer(vector.coefficients[2], zeta1);
    vector.coefficients[2] = vector.coefficients[0] - t;
    vector.coefficients[0] = vector.coefficients[0] + t;

    let t = montgomery_multiply_fe_by_fer(vector.coefficients[3], zeta1);
    vector.coefficients[3] = vector.coefficients[1] - t;
    vector.coefficients[1] = vector.coefficients[1] + t;

    let t = montgomery_multiply_fe_by_fer(vector.coefficients[6], zeta2);
    vector.coefficients[6] = vector.coefficients[4] - t;
    vector.coefficients[4] = vector.coefficients[4] + t;

    let t = montgomery_multiply_fe_by_fer(vector.coefficients[7], zeta2);
    vector.coefficients[7] = vector.coefficients[5] - t;
    vector.coefficients[5] = vector.coefficients[5] + t;

    vector
}

#[inline(always)]
pub fn ntt_at_layer_2(mut vector: PortableVector, zeta: i32) -> PortableVector {
    let t = montgomery_multiply_fe_by_fer(vector.coefficients[4], zeta);
    vector.coefficients[4] = vector.coefficients[0] - t;
    vector.coefficients[0] = vector.coefficients[0] + t;

    let t = montgomery_multiply_fe_by_fer(vector.coefficients[5], zeta);
    vector.coefficients[5] = vector.coefficients[1] - t;
    vector.coefficients[1] = vector.coefficients[1] + t;

    let t = montgomery_multiply_fe_by_fer(vector.coefficients[6], zeta);
    vector.coefficients[6] = vector.coefficients[2] - t;
    vector.coefficients[2] = vector.coefficients[2] + t;

    let t = montgomery_multiply_fe_by_fer(vector.coefficients[7], zeta);
    vector.coefficients[7] = vector.coefficients[3] - t;
    vector.coefficients[3] = vector.coefficients[3] + t;

    vector
}
