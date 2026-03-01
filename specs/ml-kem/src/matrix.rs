use crate::{
    ntt::multiply_ntts,
    parameters::*,
};

use hax_lib::int::*;

/// N.B.: According to the NIST FIPS 203 standard (Page 9, Line 519), a matrix is
/// a set of column vectors.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
/// 
fn add_polynomials(
    p1: &Polynomial,
    p2: &Polynomial,
) -> Polynomial {
    createi(|j| {
        (p1[j].to_int() + p2[j].to_int()).rem_euclid(FIELD_MODULUS.to_int()).to_i16()
    })          
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
