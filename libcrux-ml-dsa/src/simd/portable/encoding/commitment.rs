use crate::{helper::cloop, simd::portable::vector_type::Coefficients};

#[inline(always)]
pub fn serialize(simd_unit: &Coefficients, serialized: &mut [u8]) {
    match serialized.len() as u8 {
        4 => {
            // The commitment has coefficients in [0,15] => each coefficient occupies
            // 4 bits.
            cloop! {
                for (i, coefficients) in simd_unit.chunks_exact(2).enumerate() {
                    let coefficient0 = coefficients[0] as u8;
                    let coefficient1 = coefficients[1] as u8;

                    serialized[i] = (coefficient1 << 4) | coefficient0;
                }
            }
            ()
        }

        6 => {
            // The commitment has coefficients in [0,43] => each coefficient occupies
            // 6 bits.
            cloop! {
                for (i, coefficients) in simd_unit.chunks_exact(4).enumerate() {
                    let coefficient0 = coefficients[0] as u8;
                    let coefficient1 = coefficients[1] as u8;
                    let coefficient2 = coefficients[2] as u8;
                    let coefficient3 = coefficients[3] as u8;

                    serialized[3 * i] = (coefficient1 << 6) | coefficient0;
                    serialized[3 * i + 1] = (coefficient2 << 4) | coefficient1 >> 2;
                    serialized[3 * i + 2] = (coefficient3 << 2) | coefficient2 >> 4;
                }
            }
            ()
        }

        _ => unreachable!(),
    }
}
