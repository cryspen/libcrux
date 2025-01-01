use crate::{constants::Eta, helper::cloop, simd::portable::vector_type::Coefficients};

#[inline(always)]
fn serialize_when_eta_is_2(simd_unit: &Coefficients, serialized: &mut [u8]) {
    debug_assert!(serialized.len() == 3);

    const ETA: i32 = 2;

    let coefficient0 = (ETA - simd_unit[0]) as u8;
    let coefficient1 = (ETA - simd_unit[1]) as u8;
    let coefficient2 = (ETA - simd_unit[2]) as u8;
    let coefficient3 = (ETA - simd_unit[3]) as u8;
    let coefficient4 = (ETA - simd_unit[4]) as u8;
    let coefficient5 = (ETA - simd_unit[5]) as u8;
    let coefficient6 = (ETA - simd_unit[6]) as u8;
    let coefficient7 = (ETA - simd_unit[7]) as u8;

    serialized[0] = (coefficient2 << 6) | (coefficient1 << 3) | coefficient0;
    serialized[1] =
        (coefficient5 << 7) | (coefficient4 << 4) | (coefficient3 << 1) | (coefficient2 >> 2);
    serialized[2] = (coefficient7 << 5) | (coefficient6 << 2) | (coefficient5 >> 1);
}

#[inline(always)]
fn serialize_when_eta_is_4(simd_unit: &Coefficients, serialized: &mut [u8]) {
    const ETA: i32 = 4;

    cloop! {
        for (i, coefficients) in simd_unit.chunks_exact(2).enumerate() {
            let coefficient0 = (ETA - coefficients[0]) as u8;
            let coefficient1 = (ETA - coefficients[1]) as u8;

            serialized[i] = (coefficient1 << 4) | coefficient0;
        }
    }
    ()
}

#[inline(always)]
pub(crate) fn serialize(eta: Eta, simd_unit: &Coefficients, serialized: &mut [u8]) {
    match eta {
        Eta::Two => serialize_when_eta_is_2(simd_unit, serialized),
        Eta::Four => serialize_when_eta_is_4(simd_unit, serialized),
    }
}

#[inline(always)]
fn deserialize_when_eta_is_2(serialized: &[u8], simd_unit: &mut Coefficients) {
    debug_assert!(serialized.len() == 3);

    const ETA: i32 = 2;

    let byte0 = serialized[0] as i32;
    let byte1 = serialized[1] as i32;
    let byte2 = serialized[2] as i32;

    simd_unit[0] = ETA - (byte0 & 7);
    simd_unit[1] = ETA - ((byte0 >> 3) & 7);
    simd_unit[2] = ETA - (((byte0 >> 6) | (byte1 << 2)) & 7);
    simd_unit[3] = ETA - ((byte1 >> 1) & 7);
    simd_unit[4] = ETA - ((byte1 >> 4) & 7);
    simd_unit[5] = ETA - (((byte1 >> 7) | (byte2 << 1)) & 7);
    simd_unit[6] = ETA - ((byte2 >> 2) & 7);
    simd_unit[7] = ETA - ((byte2 >> 5) & 7);
}

#[inline(always)]
fn deserialize_when_eta_is_4(serialized: &[u8], simd_units: &mut Coefficients) {
    debug_assert!(serialized.len() == 4);

    const ETA: i32 = 4;

    cloop! {
        for (i, byte) in serialized.iter().enumerate() {
            simd_units[2 * i] = ETA - ((byte & 0xF) as i32);
            simd_units[2 * i + 1] = ETA - ((byte >> 4) as i32);
        }
    }
}
#[inline(always)]
pub(crate) fn deserialize(eta: Eta, serialized: &[u8], out: &mut Coefficients) {
    match eta {
        Eta::Two => deserialize_when_eta_is_2(serialized, out),
        Eta::Four => deserialize_when_eta_is_4(serialized, out),
    }
}
