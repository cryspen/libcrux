use libcrux_intrinsics::arm64::*;
#[derive(Clone, Copy)]
#[hax_lib::fstar::after(interface, "val repr (x:t_SIMD128Vector) : t_Array i16 (sz 16)")]
#[hax_lib::fstar::after("let repr (x:t_SIMD128Vector) = admit()")]
pub struct SIMD128Vector {
    pub low: _int16x8_t,
    pub high: _int16x8_t,
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("${result} == repr ${v}"))]
pub(crate) fn to_i16_array(v: SIMD128Vector) -> [i16; 16] {
    let mut out = [0i16; 16];
    _vst1q_s16(&mut out[0..8], v.low);
    _vst1q_s16(&mut out[8..16], v.high);
    out
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("repr ${result} == $array"))]
pub(crate) fn from_i16_array(array: &[i16]) -> SIMD128Vector {
    SIMD128Vector {
        low: _vld1q_s16(&array[0..8]),
        high: _vld1q_s16(&array[8..16]),
    }
}

#[allow(non_snake_case)]
#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("repr result == Seq.create 16 (mk_i16 0)"))]
pub(crate) fn ZERO() -> SIMD128Vector {
    SIMD128Vector {
        low: _vdupq_n_s16(0),
        high: _vdupq_n_s16(0),
    }
}
