use super::traits::*;
pub(crate) use libcrux_intrinsics::avx2::*;

mod arithmetic;
mod compress;
mod ntt;
mod sampling;
mod serialize;

#[derive(Clone, Copy)]
#[hax_lib::fstar::before(interface,"noeq")]
#[hax_lib::fstar::after(interface,"let repr (x:t_SIMD256Vector) : t_Array i16 (sz 16) = Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 x.f_elements")]
pub struct SIMD256Vector {
    elements: Vec256,
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("repr ${result} == Seq.create 16 0s"))]
fn vec_zero() -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_setzero_si256(),
    }
}


#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("${result} == repr ${v}"))]
fn vec_to_i16_array(v: SIMD256Vector) -> [i16; 16] {
    let mut output = [0i16; 16];
    mm256_storeu_si256_i16(&mut output, v.elements);

    output
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!("repr ${result} == ${array}"))]
fn vec_from_i16_array(array: &[i16]) -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_loadu_si256_i16(array),
    }
}

#[cfg(not(eurydice))]
impl Repr for SIMD256Vector {
    fn repr(x: Self) -> [i16; 16] {
        vec_to_i16_array(x)
    }
}

#[hax_lib::attributes]
#[cfg(not(eurydice))]
impl ArithOperations for SIMD256Vector {
    #[inline(always)]
    #[ensures(|out| fstar!("impl.f_repr out == Seq.create 16 0s"))]
    fn ZERO() -> Self {
        vec_zero()
    }

    #[requires(array.len() == 16)]
    #[ensures(|out| fstar!("impl.f_repr out == $array"))]
    fn from_i16_array(array: &[i16]) -> Self {
        vec_from_i16_array(array)
    }

    #[ensures(|out| fstar!("out == impl.f_repr $x"))]
    fn to_i16_array(x: Self) -> [i16; 16] {
        vec_to_i16_array(x)
    }

    #[requires(fstar!("forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (impl.f_repr ${lhs}) i) + v (Seq.index (impl.f_repr ${rhs}) i))"))]
    #[ensures(|result| fstar!("forall i. i < 16 ==> 
        (v (Seq.index (impl.f_repr ${result}) i) == 
         v (Seq.index (impl.f_repr ${lhs}) i) + v (Seq.index (impl.f_repr ${rhs}) i))"))]
    fn add(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::add(lhs.elements, rhs.elements),
        }
    }

    #[requires(fstar!("forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (impl.f_repr ${lhs}) i) - v (Seq.index (impl.f_repr ${rhs}) i))"))]
    #[ensures(|result| fstar!("forall i. i < 16 ==> 
        (v (Seq.index (impl.f_repr ${result}) i) == 
         v (Seq.index (impl.f_repr ${lhs}) i) - v (Seq.index (impl.f_repr ${rhs}) i))"))]
    fn sub(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::sub(lhs.elements, rhs.elements),
        }
    }

    #[requires(fstar!("forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (impl.f_repr ${vec}) i) * v c)"))]
    #[ensures(|result| fstar!("forall i. i < 16 ==> 
        (v (Seq.index (impl.f_repr ${result}) i) == 
         v (Seq.index (impl.f_repr ${vec}) i) * v c)"))]
    fn multiply_by_constant(vec: Self, c: i16) -> Self {
        Self {
            elements: arithmetic::multiply_by_constant(vec.elements, c),
        }
    }

    #[ensures(|out| fstar!("impl.f_repr out == Spec.Utils.map_array (fun x -> x &. $constant) (impl.f_repr $vector)"))]
    fn bitwise_and_with_constant(vector: Self, constant: i16) -> Self {
        Self {
            elements: arithmetic::bitwise_and_with_constant(vector.elements, constant),
        }
    }

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|out| fstar!("(v_SHIFT_BY >=. 0l /\\ v_SHIFT_BY <. 16l) ==> impl.f_repr out == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (impl.f_repr $vector)"))]
    fn shift_right<const SHIFT_BY: i32>(vector: Self) -> Self {
        Self {
            elements: arithmetic::shift_right::<{ SHIFT_BY }>(vector.elements),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b_array (pow2 12 - 1) (impl.f_repr $vector)"))]
    #[ensures(|out| fstar!("impl.f_repr out == Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) (impl.f_repr $vector)"))]
    fn cond_subtract_3329(vector: Self) -> Self {
        Self {
            elements: arithmetic::cond_subtract_3329(vector.elements),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b_array 28296 (impl.f_repr ${vector})"))]
    fn barrett_reduce(vector: Self) -> Self {
        Self {
            elements: arithmetic::barrett_reduce(vector.elements),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 $constant"))]
    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self {
        Self {
            elements: arithmetic::montgomery_multiply_by_constant(vector.elements, constant),
        }
    }
}

#[hax_lib::attributes]
#[cfg(not(eurydice))]
impl SerializeOperations for SIMD256Vector {
    fn compress_1(vector: Self) -> Self {
        Self {
            elements: compress::compress_message_coefficient(vector.elements),
        }
    }

    #[requires(COEFFICIENT_BITS == 4 || COEFFICIENT_BITS == 5 ||
        COEFFICIENT_BITS == 10 || COEFFICIENT_BITS == 11)]
    fn compress<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        Self {
            elements: compress::compress_ciphertext_coefficient::<COEFFICIENT_BITS>(
                vector.elements,
            ),
        }
    }

    #[requires(COEFFICIENT_BITS == 4 || COEFFICIENT_BITS == 5 ||
        COEFFICIENT_BITS == 10 || COEFFICIENT_BITS == 11)]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        Self {
            elements: compress::decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(
                vector.elements,
            ),
        }
    }

    #[requires(fstar!("Spec.MLKEM.serialize_pre 1 (impl.f_repr $vector)"))]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("Spec.MLKEM.serialize_pre 1 (impl.f_repr $vector) ==> Spec.MLKEM.serialize_post 1 (impl.f_repr $vector) $out"))]
    fn serialize_1(vector: Self) -> [u8; 2] {
        hax_lib::fstar!("admit()");
        serialize::serialize_1(vector.elements)
    }

    #[requires(bytes.len() == 2)]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("sz (Seq.length $bytes) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $bytes (impl.f_repr $out)"))]
    fn deserialize_1(bytes: &[u8]) -> Self {
        hax_lib::fstar!("admit()");
        Self {
            elements: serialize::deserialize_1(bytes),
        }
    }

    #[requires(fstar!("Spec.MLKEM.serialize_pre 4 (impl.f_repr $vector)"))]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("Spec.MLKEM.serialize_pre 4 (impl.f_repr $vector) ==> Spec.MLKEM.serialize_post 4 (impl.f_repr $vector) $out"))]
    fn serialize_4(vector: Self) -> [u8; 8] {
        hax_lib::fstar!("admit()");
        serialize::serialize_4(vector.elements)
    }

    #[requires(bytes.len() == 8)]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("sz (Seq.length $bytes) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $bytes (impl.f_repr $out)"))]
    fn deserialize_4(bytes: &[u8]) -> Self {
        hax_lib::fstar!("admit()");
        Self {
            elements: serialize::deserialize_4(bytes),
        }
    }

    fn serialize_5(vector: Self) -> [u8; 10] {
        serialize::serialize_5(vector.elements)
    }

    #[requires(bytes.len() == 10)]
    fn deserialize_5(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_5(bytes),
        }
    }

    #[requires(fstar!("Spec.MLKEM.serialize_pre 10 (impl.f_repr $vector)"))]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("Spec.MLKEM.serialize_pre 10 (impl.f_repr $vector) ==> Spec.MLKEM.serialize_post 10 (impl.f_repr $vector) $out"))]
    fn serialize_10(vector: Self) -> [u8; 20] {
        hax_lib::fstar!("admit()");
        serialize::serialize_10(vector.elements)
    }

    #[requires(bytes.len() == 20)]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("sz (Seq.length $bytes) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 $bytes (impl.f_repr $out)"))]
    fn deserialize_10(bytes: &[u8]) -> Self {
        hax_lib::fstar!("admit()");
        Self {
            elements: serialize::deserialize_10(bytes),
        }
    }

    fn serialize_11(vector: Self) -> [u8; 22] {
        serialize::serialize_11(vector.elements)
    }

    #[requires(bytes.len() == 22)]
    fn deserialize_11(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_11(bytes),
        }
    }

    #[requires(fstar!("Spec.MLKEM.serialize_pre 12 (impl.f_repr $vector)"))]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("Spec.MLKEM.serialize_pre 12 (impl.f_repr $vector) ==> Spec.MLKEM.serialize_post 12 (impl.f_repr $vector) $out"))]
    fn serialize_12(vector: Self) -> [u8; 24] {
        hax_lib::fstar!("admit()");
        serialize::serialize_12(vector.elements)
    }

    #[requires(bytes.len() == 24)]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("sz (Seq.length $bytes) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $bytes (impl.f_repr $out)"))]
    fn deserialize_12(bytes: &[u8]) -> Self {
        hax_lib::fstar!("admit()");
        Self {
            elements: serialize::deserialize_12(bytes),
        }
    }

    #[requires(input.len() == 24 && output.len() == 16)]
    #[ensures(|result|
        fstar!("Seq.length $output_future == Seq.length $output /\\ v $result <= 16")
    )]
    fn rej_sample(input: &[u8], output: &mut [i16]) -> usize {
        sampling::rejection_sample(input, output)
    }
}

#[hax_lib::attributes]
#[cfg(not(eurydice))]
impl NTTOperations for SIMD256Vector {
    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\\ Spec.Utils.is_i16b 1664 zeta3 /\\
                       Spec.Utils.is_i16b_array (11207+5*3328) (impl.f_repr ${vector})"))]
    #[ensures(|out| fstar!("Spec.Utils.is_i16b_array (11207+6*3328) (impl.f_repr $out)"))]
    fn ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\
                       Spec.Utils.is_i16b_array (11207+4*3328) (impl.f_repr ${vector})"))]
    #[ensures(|out| fstar!("Spec.Utils.is_i16b_array (11207+5*3328) (impl.f_repr $out)"))]
    fn ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_2_step(vector.elements, zeta0, zeta1),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta /\\
                       Spec.Utils.is_i16b_array (11207+3*3328) (impl.f_repr ${vector})"))]
    #[ensures(|out| fstar!("Spec.Utils.is_i16b_array (11207+4*3328) (impl.f_repr $out)"))]
    fn ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        Self {
            elements: ntt::ntt_layer_3_step(vector.elements, zeta),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\\ Spec.Utils.is_i16b 1664 zeta3  /\\
                       Spec.Utils.is_i16b_array (4*3328) (impl.f_repr ${vector})"))]
    #[ensures(|out| fstar!("Spec.Utils.is_i16b_array 3328 (impl.f_repr $out)"))]
    fn inv_ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${vector})"))]
    #[ensures(|out| fstar!("Spec.Utils.is_i16b_array 3328 (impl.f_repr $out)"))]
    fn inv_ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_2_step(vector.elements, zeta0, zeta1),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta /\\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${vector})"))]
    #[ensures(|out| fstar!("Spec.Utils.is_i16b_array 3328 (impl.f_repr $out)"))]
    fn inv_ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        Self {
            elements: ntt::inv_ntt_layer_3_step(vector.elements, zeta),
        }
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\
                       Spec.Utils.is_i16b 1664 zeta2 /\\ Spec.Utils.is_i16b 1664 zeta3 /\\
                       Spec.Utils.is_i16b_array 3228 (impl.f_repr ${lhs}) /\\
                       Spec.Utils.is_i16b_array 3228 (impl.f_repr ${rhs})"))]
    #[ensures(|out| fstar!("Spec.Utils.is_i16b_array 3328 (impl.f_repr $out)"))]
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
}

#[cfg(not(eurydice))]
impl Operations for SIMD256Vector {}

#[cfg(eurydice)]
impl Operations for SIMD256Vector {
    fn ZERO() -> Self {
        zero()
    }

    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array)
    }

    fn to_i16_array(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    fn multiply_by_constant(vec: Self, c: i16) -> Self {
        multiply_by_constant(vec, c)
    }

    fn bitwise_and_with_constant(v: Self, c: i16) -> Self {
        bitwise_and_with_constant(v, c)
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_right::<{ SHIFT_BY }>(v)
    }

    fn cond_subtract_3329(v: Self) -> Self {
        cond_subtract_3329(v)
    }

    fn barrett_reduce(v: Self) -> Self {
        barrett_reduce(v)
    }

    fn montgomery_multiply_by_constant(v: Self, r: i16) -> Self {
        montgomery_multiply_by_constant(v, r)
    }

    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        ntt_layer_2_step(a, zeta0, zeta1)
    }

    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        ntt_layer_3_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        inv_ntt_layer_2_step(a, zeta0, zeta1)
    }

    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        inv_ntt_layer_3_step(a, zeta)
    }

    
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2, zeta3)
    }   

    fn compress_1(v: Self) -> Self {
        compress_1(v)
    }

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::<COEFFICIENT_BITS>(v)
    }

    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(v)
    }
    
    fn serialize_1(a: Self) -> [u8; 2] {
        serialize_1(a)
    }

    fn deserialize_1(a: &[u8]) -> Self {
        deserialize_1(a)
    }

    fn serialize_4(a: Self) -> [u8; 8] {
        serialize_4(a)
    }

    fn deserialize_4(a: &[u8]) -> Self {
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 10] {
        serialize_5(a)
    }

    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    fn serialize_10(a: Self) -> [u8; 20] {
        serialize_10(a)
    }

    fn deserialize_10(a: &[u8]) -> Self {
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 22] {
        serialize_11(a)
    }

    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    fn serialize_12(a: Self) -> [u8; 24] {
        serialize_12(a)
    }

    fn deserialize_12(a: &[u8]) -> Self {
        deserialize_12(a)
    }

    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize {
        rej_sample(a, out)
    }
}
