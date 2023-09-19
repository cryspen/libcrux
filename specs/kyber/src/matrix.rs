use crate::{
    ntt::multiply_ntts,
    parameters::{KyberMatrix, KyberPolynomialRingElement, KyberVector},
};

pub(crate) fn transpose(matrix: &KyberMatrix) -> KyberMatrix {
    let mut transpose = [KyberVector::new(), KyberVector::new(), KyberVector::new()];
    for (i, row) in matrix.iter().enumerate() {
        for (j, matrix_element) in row.iter().enumerate() {
            transpose[j][i] = *matrix_element;
        }
    }

    transpose
}

pub(crate) fn multiply_matrix_transpose_by_column(
    matrix: &KyberMatrix,
    vector: &KyberVector,
) -> KyberVector {
    let mut result = KyberVector::new();

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
    column_vector: &KyberVector,
    row_vector: &KyberVector,
) -> KyberPolynomialRingElement {
    let mut result = KyberPolynomialRingElement::ZERO;

    for (column_element, row_element) in column_vector.iter().zip(row_vector.iter()) {
        result = result + multiply_ntts(column_element, row_element);
    }

    result
}
