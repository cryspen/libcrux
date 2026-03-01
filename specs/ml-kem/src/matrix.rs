use crate::{
    ntt::multiply_ntts,
    parameters::*,
};

/// N.B.: According to the NIST FIPS 203 standard (Page 9, Line 519), a matrix is
/// a set of column vectors.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
///
pub(crate) fn add_polynomials(
    p1: &Polynomial,
    p2: &Polynomial,
) -> Polynomial {
    createi(|j| {
        (p1[j] as i32 + p2[j] as i32).rem_euclid(FIELD_MODULUS as i32) as i16
    })
}

pub(crate) fn sub_polynomials(
    p1: &Polynomial,
    p2: &Polynomial,
) -> Polynomial {
    createi(|j| {
        (p1[j] as i32 - p2[j] as i32).rem_euclid(FIELD_MODULUS as i32) as i16
    })
}

pub(crate) fn add_vectors<const RANK: usize>(
    v1: &Vector<RANK>,
    v2: &Vector<RANK>,
) -> Vector<RANK> {
    createi(|i| add_polynomials(&v1[i], &v2[i]))
}

pub(crate) fn multiply_matrix_by_column<const RANK:usize>(
    matrix: &Matrix<RANK>,
    vector: &Vector<RANK>,
) -> Vector<RANK> {
    createi(|i| {
        let mut result = [0; 256];
        for j in 0..RANK {
            let product = multiply_ntts(&matrix[j][i], &vector[j]);
            result = add_polynomials(&result, &product);
        }
        result
    })
}

pub(crate) fn multiply_vectors<const RANK:usize>(
    v1: &Vector<RANK>,
    v2: &Vector<RANK>,
) -> Polynomial {
    let mut result = [0; 256];
    for j in 0..RANK {
        let product = multiply_ntts(&v1[j], &v2[j]);
        result = add_polynomials(&result, &product);
    }
    result
}

pub(crate) fn transpose<const RANK: usize>(matrix: &Matrix<RANK>) -> Matrix<RANK> {
    createi(|i| createi(|j| matrix[j][i]))
}
