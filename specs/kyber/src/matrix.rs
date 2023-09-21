use crate::{
    ntt::multiply_ntts,
    parameters::{KyberPolynomialRingElement, RANK},
};

pub(crate) fn transpose(
    matrix: &[[KyberPolynomialRingElement; RANK]; RANK],
) -> [[KyberPolynomialRingElement; RANK]; RANK] {
    let mut transpose = [[KyberPolynomialRingElement::ZERO; RANK]; RANK];
    for (i, row) in matrix.iter().enumerate() {
        for (j, matrix_element) in row.iter().enumerate() {
            transpose[j][i] = *matrix_element;
        }
    }

    transpose
}

pub(crate) fn multiply_matrix_transpose_by_column(
    matrix: &[[KyberPolynomialRingElement; RANK]; RANK],
    vector: &[KyberPolynomialRingElement; RANK],
) -> [KyberPolynomialRingElement; RANK] {
    let mut result = [KyberPolynomialRingElement::ZERO; RANK];

    let transposed = transpose(&matrix);
    for (i, row) in transposed.iter().enumerate() {
        for (j, matrix_element) in row.iter().enumerate() {
            let product = multiply_ntts(matrix_element, &vector[j]);
            result[i] = result[i] + product;
        }
    }
    result
}

pub(crate) fn multiply_column_by_row(
    column_vector: &[KyberPolynomialRingElement; RANK],
    row_vector: &[KyberPolynomialRingElement; RANK],
) -> KyberPolynomialRingElement {
    let mut result = KyberPolynomialRingElement::ZERO;

    for (column_element, row_element) in column_vector.iter().zip(row_vector.iter()) {
        result = result + multiply_ntts(column_element, row_element);
    }

    result
}
