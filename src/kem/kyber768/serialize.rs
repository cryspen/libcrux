use crate::kem::kyber768::parameters::{
    KyberPolynomialRingElement, BITS_PER_COEFFICIENT, BYTES_PER_RING_ELEMENT,
    COEFFICIENTS_IN_RING_ELEMENT
};

use crate::kem::kyber768::field_element::KyberFieldElement;

pub fn serialize_little_endian_1(re: KyberPolynomialRingElement) -> [u8; COEFFICIENTS_IN_RING_ELEMENT / 8] {
    let mut serialized = [0u8; COEFFICIENTS_IN_RING_ELEMENT / 8];

    for (i, chunk) in re.coefficients.chunks_exact(8).enumerate() {
        for (j, coefficient) in chunk.iter().enumerate() {
            serialized[i] |= (coefficient.value as u8) << j
        }
    }

    serialized
}
pub fn deserialize_little_endian_1(serialized: [u8; COEFFICIENTS_IN_RING_ELEMENT / 8]) -> KyberPolynomialRingElement {
    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, byte) in serialized.iter().enumerate() {
        for j in 0..8 {
            re.coefficients[8 * i + j].value = ((byte >> j) & 0x1) as u16;
        }
    }

    re
}

pub fn serialize_little_endian_4(re: KyberPolynomialRingElement) -> [u8; (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8] {
    let mut serialized = [0u8; (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8];

    for (i, chunk) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient1 = chunk[0].value as u8;
        let coefficient2 = chunk[1].value as u8;

        serialized[i] = (coefficient2 << 4) | coefficient1;
    }

    serialized
}
pub fn deserialize_little_endian_4(serialized: [u8; (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8]) -> KyberPolynomialRingElement {
    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, byte) in serialized.iter().enumerate() {
        re.coefficients[2 * i].value = (byte & 0x0F) as u16;
        re.coefficients[2 * i + 1].value = ((byte >> 4) & 0x0F) as u16;
    }

    re
}

pub fn serialize_little_endian_10(re: KyberPolynomialRingElement) -> [u8; (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8] {
    let mut serialized = [0u8; (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8];

    for (i, chunk) in re.coefficients.chunks_exact(4).enumerate() {
        let coefficient1 = chunk[0].value;
        let coefficient2 = chunk[1].value;
        let coefficient3 = chunk[2].value;
        let coefficient4 = chunk[3].value;

        serialized[5 * i] = (coefficient1 & 0xFF) as u8;
        serialized[5 * i + 1] = ((coefficient2 & 0x3F) as u8) << 2 | ((coefficient1 >> 8) & 0x03) as u8;
        serialized[5 * i + 2] = ((coefficient3 & 0x0F) as u8) << 4 | ((coefficient2 >> 6) & 0x0F) as u8;
        serialized[5 * i + 3] = ((coefficient4 & 0x03) as u8) << 6 | ((coefficient3 >> 4) & 0x3F) as u8;
        serialized[5 * i + 4] = ((coefficient4 >> 2) & 0xFF) as u8;
    }

    serialized
}
pub fn deserialize_little_endian_10(serialized: [u8; (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8]) -> KyberPolynomialRingElement {
    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, bytes) in serialized.chunks(5).enumerate() {
        let byte1 = bytes[0] as u16;
        let byte2 = bytes[1] as u16;
        let byte3 = bytes[2] as u16;
        let byte4 = bytes[3] as u16;
        let byte5 = bytes[4] as u16;

        re.coefficients[4 * i].value = (byte2 & 0x03) << 8 | (byte1 & 0xFF);
        re.coefficients[4 * i + 1].value = (byte3 & 0x0F) << 6 | (byte2 >> 2);
        re.coefficients[4 * i + 2].value = (byte4 & 0x3F) << 4 | (byte3 >> 4);
        re.coefficients[4 * i + 3].value = byte5 << 2 | (byte4 >> 6);
    }

    re
}

pub fn serialize_little_endian_12(re: KyberPolynomialRingElement) -> [u8; BYTES_PER_RING_ELEMENT] {
    let mut serialized = [0u8; BYTES_PER_RING_ELEMENT];

    for (i, chunks) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient1 = chunks[0].value;
        let coefficient2 = chunks[1].value;

        serialized[3 * i] = (coefficient1 & 0xFF) as u8;
        serialized[3 * i + 1] = ((coefficient1 >> 8) | ((coefficient2 & 0xF) << 4)) as u8;
        serialized[3 * i + 2] = ((coefficient2 >> 4) & 0xFF) as u8;
    }

    serialized
}
pub fn deserialize_little_endian_12(serialized: [u8; BYTES_PER_RING_ELEMENT]) -> KyberPolynomialRingElement {
    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, bytes) in serialized.chunks_exact(3).enumerate() {
        let byte1 = bytes[0] as u16;
        let byte2 = bytes[1] as u16;
        let byte3 = bytes[2] as u16;

        re.coefficients[2 * i].value = (byte2 & 0x0F) << 8 | (byte1 & 0xFF);
        re.coefficients[2 * i + 1].value = (byte3 << 4) | ((byte2 >> 4) & 0x0F);
    }

    re
}
