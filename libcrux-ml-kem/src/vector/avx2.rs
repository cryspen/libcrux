use super::traits::Operations;
use crate::vector::traits::Repr;
pub(crate) use libcrux_intrinsics::avx2::*;

mod arithmetic;
mod compress;
mod ntt;
mod sampling;
mod serialize;

#[derive(Clone, Copy)]
#[hax_lib::fstar::after(interface,"val repr (x:t_SIMD256Vector) : t_Array i16 (sz 16)")]
#[hax_lib::fstar::after("let repr (x:t_SIMD256Vector) = Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 x.elements")]
pub struct SIMD256Vector {
    elements: Vec256,
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("to_i16_array ${result} == Seq.create 16 0s"))]
fn zero() -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_setzero_si256(),
    }
}


#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("${result} == repr ${v}"))]
fn to_i16_array(v: SIMD256Vector) -> [i16; 16] {
    let mut output = [0i16; 16];
    mm256_storeu_si256_i16(&mut output, v.elements);

    output
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("repr ${result} == ${array}"))]
fn from_i16_array(array: &[i16]) -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_loadu_si256_i16(array),
    }
}

impl Repr for SIMD256Vector {
    fn repr(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }
}

#[hax_lib::attributes]
impl Operations for SIMD256Vector {
    #[ensures(|result| fstar!("impl.f_repr out == Seq.create 16 0s"))]
    fn ZERO() -> Self {
        zero()
    }

    #[requires(array.len() == 16)]
    #[ensures(|result| fstar!("impl.f_repr out == $array"))]
    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array)
    }

    #[ensures(|result| fstar!("out == impl.f_repr $x"))]
    fn to_i16_array(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }

    #[ensures(|result| fstar!("impl.f_repr out == Spec.Utils.map2 (+.) (impl.f_repr $lhs) (impl.f_repr $rhs)"))]
    fn add(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::add(lhs.elements, rhs.elements),
        }
    }

    #[ensures(|result| fstar!("impl.f_repr out == Spec.Utils.map2 (-.) (impl.f_repr $lhs) (impl.f_repr $rhs)"))]
    fn sub(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::sub(lhs.elements, rhs.elements),
        }
    }

    #[ensures(|result| fstar!("impl.f_repr out == Spec.Utils.map_array (fun x -> x *. c) (impl.f_repr $v)"))]
    fn multiply_by_constant(v: Self, c: i16) -> Self {
        Self {
            elements: arithmetic::multiply_by_constant(v.elements, c),
        }
    }

    #[ensures(|result| fstar!("impl.f_repr out == Spec.Utils.map_array (fun x -> x &. $constant) (impl.f_repr $vector)"))]
    fn bitwise_and_with_constant(vector: Self, constant: i16) -> Self {
        Self {
            elements: arithmetic::bitwise_and_with_constant(vector.elements, constant),
        }
    }

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|result| fstar!("(v_SHIFT_BY >=. 0l /\\ v_SHIFT_BY <. 16l) ==> impl.f_repr out == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (impl.f_repr $vector)"))]
    fn shift_right<const SHIFT_BY: i32>(vector: Self) -> Self {
        Self {
            elements: arithmetic::shift_right::<{ SHIFT_BY }>(vector.elements),
        }
    }

    #[requires(true)]
    #[ensures(|result| fstar!("impl.f_repr out == Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) (impl.f_repr $vector)"))]
    fn cond_subtract_3329(vector: Self) -> Self {
        Self {
            elements: arithmetic::cond_subtract_3329(vector.elements),
        }
    }

    fn barrett_reduce(vector: Self) -> Self {
        Self {
            elements: arithmetic::barrett_reduce(vector.elements),
        }
    }

    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self {
        Self {
            elements: arithmetic::montgomery_multiply_by_constant(vector.elements, constant),
        }
    }

    fn compress_1(vector: Self) -> Self {
        Self {
            elements: compress::compress_message_coefficient(vector.elements),
        }
    }

    fn compress<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        Self {
            elements: compress::compress_ciphertext_coefficient::<COEFFICIENT_BITS>(
                vector.elements,
            ),
        }
    }

    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        Self {
            elements: compress::decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(
                vector.elements,
            ),
        }
    }

    fn ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    fn ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_2_step(vector.elements, zeta0, zeta1),
        }
    }

    fn ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_3_step(vector.elements, zeta),
        }
    }

    fn inv_ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    fn inv_ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_2_step(vector.elements, zeta0, zeta1),
        }
    }

    fn inv_ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_3_step(vector.elements, zeta),
        }
    }

    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        Self {
            elements: ntt::ntt_multiply(lhs.elements, rhs.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    fn serialize_1(vector: Self) -> [u8; 2] {
        serialize::serialize_1(vector.elements)
    }

    fn deserialize_1(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_1(bytes),
        }
    }

    fn serialize_4(vector: Self) -> [u8; 8] {
        serialize::serialize_4(vector.elements)
    }

    fn deserialize_4(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_4(bytes),
        }
    }

    fn serialize_5(vector: Self) -> [u8; 10] {
        serialize::serialize_5(vector.elements)
    }

    fn deserialize_5(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_5(bytes),
        }
    }

    fn serialize_10(vector: Self) -> [u8; 20] {
        serialize::serialize_10(vector.elements)
    }

    fn deserialize_10(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_10(bytes),
        }
    }

    fn serialize_11(vector: Self) -> [u8; 22] {
        serialize::serialize_11(vector.elements)
    }

    fn deserialize_11(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_11(bytes),
        }
    }

    fn serialize_12(vector: Self) -> [u8; 24] {
        serialize::serialize_12(vector.elements)
    }

    fn deserialize_12(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_12(bytes),
        }
    }

    fn rej_sample(input: &[u8], output: &mut [i16]) -> usize {
        sampling::rejection_sample(input, output)
    }
}
