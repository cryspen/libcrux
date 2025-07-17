use crate::{helper::cloop, simd::portable::vector_type::Coefficients};

#[inline(always)]
#[hax_lib::requires(fstar!(r#"(forall i. bounded (Seq.index ${simd_unit.values} i) 17) /\ Seq.length $serialized == 18"#))]
fn serialize_when_gamma1_is_2_pow_17(simd_unit: &Coefficients, serialized: &mut [u8]) {
    const GAMMA1: i32 = 1 << 17;

    cloop! {
        for (i, coefficients) in simd_unit.values.chunks_exact(4).enumerate() {
            hax_lib::loop_invariant!(|_i: usize| serialized.len() == 18);

            let coefficient0 = GAMMA1 - coefficients[0];
            let coefficient1 = GAMMA1 - coefficients[1];
            let coefficient2 = GAMMA1 - coefficients[2];
            let coefficient3 = GAMMA1 - coefficients[3];

            serialized[9 * i] = coefficient0 as u8;
            serialized[9 * i + 1] = (coefficient0 >> 8) as u8;

            serialized[9 * i + 2] = (coefficient0 >> 16) as u8;
            serialized[9 * i + 2] |= (coefficient1 << 2) as u8;

            serialized[9 * i + 3] = (coefficient1 >> 6) as u8;

            serialized[9 * i + 4] = (coefficient1 >> 14) as u8;
            serialized[9 * i + 4] |= (coefficient2 << 4) as u8;

            serialized[9 * i + 5] = (coefficient2 >> 4) as u8;

            serialized[9 * i + 6] = (coefficient2 >> 12) as u8;
            serialized[9 * i + 6] |= (coefficient3 << 6) as u8;

            serialized[9 * i + 7] = (coefficient3 >> 2) as u8;
            serialized[9 * i + 8] = (coefficient3 >> 10) as u8;
        }
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"(forall i. bounded (Seq.index ${simd_unit.values} i) 19) /\ Seq.length $serialized == 20"#))]
fn serialize_when_gamma1_is_2_pow_19(simd_unit: &Coefficients, serialized: &mut [u8]) {
    const GAMMA1: i32 = 1 << 19;

    cloop! {
        for (i, coefficients) in simd_unit.values.chunks_exact(2).enumerate() {
            hax_lib::loop_invariant!(|_i: usize| serialized.len() == 20);

            let coefficient0 = GAMMA1 - coefficients[0];
            let coefficient1 = GAMMA1 - coefficients[1];

            serialized[5 * i] = coefficient0 as u8;
            serialized[5 * i + 1] = (coefficient0 >> 8) as u8;

            serialized[5 * i + 2] = (coefficient0 >> 16) as u8;
            serialized[5 * i + 2] |= (coefficient1 << 4) as u8;

            serialized[5 * i + 3] = (coefficient1 >> 4) as u8;
            serialized[5 * i + 4] = (coefficient1 >> 12) as u8;
        }
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
       (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19)
    /\ (forall i. bounded (Seq.index ${simd_unit.values} i) (v $gamma1_exponent))
    /\ Seq.length $serialized == (1 + v $gamma1_exponent)
"#))]
pub(crate) fn serialize(simd_unit: &Coefficients, serialized: &mut [u8], gamma1_exponent: usize) {
    match gamma1_exponent {
        17 => serialize_when_gamma1_is_2_pow_17(simd_unit, serialized),
        19 => serialize_when_gamma1_is_2_pow_19(simd_unit, serialized),
        _ => unreachable!(),
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"Seq.length $serialized == 18"#))]
fn deserialize_when_gamma1_is_2_pow_17(serialized: &[u8], simd_unit: &mut Coefficients) {
    // Each set of 9 bytes deserializes to 4 elements, and since each PortableSIMDUnit
    // can hold 8, we process 18 bytes in this function.
    debug_assert!(serialized.len() == 18);

    const GAMMA1: i32 = 1 << 17;
    const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

    cloop! {
        for (i, bytes) in serialized.chunks_exact(9).enumerate() {
            hax_lib::loop_invariant!(|_i: usize| serialized.len() == 18);
            let mut coefficient0 = bytes[0] as i32;
            coefficient0 |= (bytes[1] as i32) << 8;
            coefficient0 |= (bytes[2] as i32) << 16;
            coefficient0 &= GAMMA1_TIMES_2_BITMASK;

            let mut coefficient1 = (bytes[2] as i32) >> 2;
            coefficient1 |= (bytes[3] as i32) << 6;
            coefficient1 |= (bytes[4] as i32) << 14;
            coefficient1 &= GAMMA1_TIMES_2_BITMASK;

            let mut coefficient2 = (bytes[4] as i32) >> 4;
            coefficient2 |= (bytes[5] as i32) << 4;
            coefficient2 |= (bytes[6] as i32) << 12;
            coefficient2 &= GAMMA1_TIMES_2_BITMASK;

            let mut coefficient3 = (bytes[6] as i32) >> 6;
            coefficient3 |= (bytes[7] as i32) << 2;
            coefficient3 |= (bytes[8] as i32) << 10;
            coefficient3 &= GAMMA1_TIMES_2_BITMASK;

            hax_lib::fstar!("let (): squash (forall (x: int_t I32). get_bit x (mk_int 31) == 0 ==> v x >= 0) = reveal_opaque (`%get_bit) (get_bit #I32) in ()");

            simd_unit.values[4 * i] = GAMMA1 - coefficient0;
            simd_unit.values[4 * i + 1] = GAMMA1 - coefficient1;
            simd_unit.values[4 * i + 2] = GAMMA1 - coefficient2;
            simd_unit.values[4 * i + 3] = GAMMA1 - coefficient3;
        }
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"Seq.length $serialized == 20"#))]
fn deserialize_when_gamma1_is_2_pow_19(serialized: &[u8], simd_unit: &mut Coefficients) {
    // Each set of 5 bytes deserializes to 2 elements, and since each PortableSIMDUnit
    // can hold 8, we process 5 * (8 / 2) = 20 bytes in this function.
    debug_assert!(serialized.len() == 20);

    const GAMMA1: i32 = 1 << 19;
    const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

    cloop! {
        for (i, bytes) in serialized.chunks_exact(5).enumerate() {
            let mut coefficient0 = bytes[0] as i32;
            coefficient0 |= (bytes[1] as i32) << 8;
            coefficient0 |= (bytes[2] as i32) << 16;
            coefficient0 &= GAMMA1_TIMES_2_BITMASK;

            let mut coefficient1 = (bytes[2] as i32) >> 4;
            coefficient1 |= (bytes[3] as i32) << 4;
            coefficient1 |= (bytes[4] as i32) << 12;

            hax_lib::fstar!("let (): squash (forall (x: int_t I32). get_bit x (mk_int 31) == 0 ==> v x >= 0) = reveal_opaque (`%get_bit) (get_bit #I32) in ()");

            simd_unit.values[2 * i] = GAMMA1 - coefficient0;
            simd_unit.values[2 * i + 1] = GAMMA1 - coefficient1;
        }
    }
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"Seq.length $serialized == 1 + v $gamma1_exponent"#))]
pub(crate) fn deserialize(serialized: &[u8], out: &mut Coefficients, gamma1_exponent: usize) {
    match gamma1_exponent {
        17 => deserialize_when_gamma1_is_2_pow_17(serialized, out),
        19 => deserialize_when_gamma1_is_2_pow_19(serialized, out),
        _ => unreachable!(),
    }
}
