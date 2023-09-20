use crate::{
    ntt::multiply_ntts,
    parameters::{KyberPolynomialRingElement, BYTES_PER_RING_ELEMENT, RANK},
    serialize::{byte_decode, byte_encode},
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

/// N.B.: According to the NIST FIPS 203 standard (Page 9, Line 519), a matrix is
/// a set of column vectors.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub(crate) fn multiply_matrix_by_column(
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

pub(crate) fn encode_vector_12(
    re_vector: [KyberPolynomialRingElement; RANK],
) -> [u8; RANK * BYTES_PER_RING_ELEMENT] {
    let mut out = [0u8; RANK * BYTES_PER_RING_ELEMENT];

    for (i, re) in re_vector.into_iter().enumerate() {
        out[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT]
            .copy_from_slice(&byte_encode(12, re));
    }

    out
}

pub(crate) fn decode_vector_12(
    encoded: &[u8; RANK * BYTES_PER_RING_ELEMENT],
) -> [KyberPolynomialRingElement; RANK] {
    let mut out = [KyberPolynomialRingElement::ZERO; RANK];

    for (i, bytes) in encoded.chunks(BYTES_PER_RING_ELEMENT).enumerate() {
        out[i] = byte_decode(12, bytes);
    }

    out
}
