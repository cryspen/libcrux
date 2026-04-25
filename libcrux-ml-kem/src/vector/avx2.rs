use super::traits::Operations;
pub(crate) use libcrux_intrinsics::avx2::*;

#[cfg(hax)]
use super::traits::{spec, Repr};

mod arithmetic;
mod compress;
mod ntt;
mod sampling;
mod serialize;

#[cfg(hax)]
use hax_lib::prop::ToProp;

#[derive(Clone, Copy)]
#[hax_lib::fstar::before(interface, "noeq")]
#[hax_lib::fstar::after(interface,"let repr (x:t_SIMD256Vector) : t_Array i16 (sz 16) = Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 x.f_elements")]
pub struct SIMD256Vector {
    elements: Vec256,
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!(r#"repr ${result} == Seq.create 16 (mk_i16 0)"#))]
fn vec_zero() -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_setzero_si256(),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!(r#"${result} == repr ${v}"#))]
fn vec_to_i16_array(v: SIMD256Vector) -> [i16; 16] {
    let mut output = [0i16; 16];
    mm256_storeu_si256_i16(&mut output, v.elements);

    output
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!(r#"repr ${result} == ${array}"#))]
fn vec_from_i16_array(array: &[i16]) -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_loadu_si256_i16(array),
    }
}

#[inline(always)]
#[hax_lib::requires(array.len() >= 32)]
pub(super) fn from_bytes(array: &[u8]) -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_loadu_si256_u8(&array[0..32]),
    }
}

// `to_bytes` stays `lax` — same as pre-C4f.  Discharging
// panic-freedom of `update_at_range bytes [0..32]` from `bytes.len() >= 32`
// fails with `incomplete quantifiers` at rlimit 200; this is an F*/hax
// modeling issue around `&mut` slice bounds, not a C4'/trait-impl concern.
// Out of C4' scope.
#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() >= 32)]
#[hax_lib::ensures(|_| future(bytes).len() == bytes.len())]
pub(super) fn to_bytes(x: SIMD256Vector, bytes: &mut [u8]) {
    mm256_storeu_si256_u8(&mut bytes[0..32], x.elements)
}

#[cfg(hax)]
impl crate::vector::traits::Repr for SIMD256Vector {
    fn repr(&self) -> [i16; 16] {
        vec_to_i16_array(self.clone())
    }
}

#[cfg(any(eurydice, not(hax)))]
impl crate::vector::traits::Repr for SIMD256Vector {}

// =====================================================================
// `op_*` wrappers — same pattern as `src/vector/portable.rs`.
//
// Each `op_*` carries the *exact* trait pre/post for its
// `impl Operations for SIMD256Vector` counterpart, so the impl method
// body collapses to a one-line `op_<name>(args)` call (the trait
// subtyping check is then `P ==> P`, trivial).  Each `op_*` verifies in
// its own SMT scope; `impl_1`'s VC is uniformly trivial.
//
// Methods omitted from this section (no `op_*` needed):
//   ZERO, from_i16_array, to_i16_array, from_bytes, to_bytes,
//   add, sub, multiply_by_constant
// — for these the underlying `arithmetic::*` primitive's pre/post
// already matches the trait's exactly, so the impl method body is
// already a one-line call (mirrors portable.rs).
//
// `op_*` for compress/decompress/NTT-layer/ntt_multiply carry
// `panic_free` because the strengthened C4f trait posts (FE-form for
// NTT-layer + ntt_multiply, hacspec FE-equation form for
// compress/decompress) are not yet discharged from the AVX2 body —
// that is the C4′ AVX2 mirror task.  `panic_free` skips the body
// post-condition obligation while still checking panic-freedom and
// the pre-condition of the underlying primitive call.
//
// **Removal plan**: drop `panic_free` and prove each body when the
// corresponding portable proof's helper lemmas (in
// `Hacspec_ml_kem.Commute.Chunk.fst`) close, plus the AVX2-specific
// per-lane lemmas needed to bridge `Vec256` ↔ array form.  Tracked
// in `proofs/commutativity-handoff.md` progress tracker row C4′.
// =====================================================================

#[inline(always)]
#[hax_lib::requires(spec::cond_subtract_3329_pre(&vector.repr()))]
#[hax_lib::ensures(|out| spec::cond_subtract_3329_post(&vector.repr(), &out.repr()))]
fn op_cond_subtract_3329(vector: SIMD256Vector) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    let result = SIMD256Vector {
        elements: arithmetic::cond_subtract_3329(vector.elements),
    };
    hax_lib::fstar!(
        r#"Seq.lemma_eq_intro (repr ${result})
                  (Spec.Utils.map_array
                     (fun (x:i16) -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x)
                     (repr ${vector}))"#
    );
    result
}

#[inline(always)]
#[hax_lib::requires(spec::barrett_reduce_pre(&vector.repr()))]
#[hax_lib::ensures(|out| spec::barrett_reduce_post(&vector.repr(), &out.repr()))]
fn op_barrett_reduce(vector: SIMD256Vector) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: arithmetic::barrett_reduce(vector.elements),
    }
}

#[inline(always)]
#[hax_lib::requires(spec::montgomery_multiply_by_constant_pre(&vector.repr(), constant))]
#[hax_lib::ensures(|out| spec::montgomery_multiply_by_constant_post(&vector.repr(), constant, &out.repr()))]
fn op_montgomery_multiply_by_constant(vector: SIMD256Vector, constant: i16) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: arithmetic::montgomery_multiply_by_constant(vector.elements, constant),
    }
}

#[inline(always)]
#[hax_lib::requires(spec::to_unsigned_representative_pre(&a.repr()))]
#[hax_lib::ensures(|out| spec::to_unsigned_representative_post(&a.repr(), &out.repr()))]
fn op_to_unsigned_representative(a: SIMD256Vector) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: arithmetic::to_unsigned_representative(a.elements),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::compress_1_pre} (impl.f_repr ${vector})"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::compress_1_post} (impl.f_repr ${vector}) (impl.f_repr ${out})"#))]
fn op_compress_1(vector: SIMD256Vector) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.bounded_i16_array)
                    (Libcrux_ml_kem.Vector.Traits.Spec.bounded_i16_array)"#
    );
    SIMD256Vector {
        elements: compress::compress_message_coefficient(vector.elements),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::compress_pre} (impl.f_repr ${vector}) $COEFFICIENT_BITS"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::compress_post} (impl.f_repr ${vector}) $COEFFICIENT_BITS (impl.f_repr ${out})"#))]
fn op_compress<const COEFFICIENT_BITS: i32>(vector: SIMD256Vector) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.bounded_i16_array)
                    (Libcrux_ml_kem.Vector.Traits.Spec.bounded_i16_array)"#
    );
    SIMD256Vector {
        elements: compress::compress_ciphertext_coefficient::<COEFFICIENT_BITS>(vector.elements),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::decompress_1_pre} (impl.f_repr ${a})"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::decompress_1_post} (impl.f_repr ${a}) (impl.f_repr ${out})"#))]
fn op_decompress_1(a: SIMD256Vector) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.bounded_i16_array)
                    (Libcrux_ml_kem.Vector.Traits.Spec.bounded_i16_array)"#
    );
    SIMD256Vector {
        elements: compress::decompress_1(a.elements),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::decompress_ciphertext_coefficient_pre} (impl.f_repr ${vector}) $COEFFICIENT_BITS"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::decompress_ciphertext_coefficient_post} (impl.f_repr ${vector}) $COEFFICIENT_BITS (impl.f_repr ${out})"#))]
fn op_decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vector: SIMD256Vector) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.bounded_i16_array)
                    (Libcrux_ml_kem.Vector.Traits.Spec.bounded_i16_array)"#
    );
    SIMD256Vector {
        elements: compress::decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(vector.elements),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::ntt_layer_1_step_pre} (impl.f_repr ${vector}) zeta0 zeta1 zeta2 zeta3"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::ntt_layer_1_step_post} (impl.f_repr ${vector}) zeta0 zeta1 zeta2 zeta3 (impl.f_repr ${out})"#))]
fn op_ntt_layer_1_step(
    vector: SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: ntt::ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::ntt_layer_2_step_pre} (impl.f_repr ${vector}) zeta0 zeta1"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::ntt_layer_2_step_post} (impl.f_repr ${vector}) zeta0 zeta1 (impl.f_repr ${out})"#))]
fn op_ntt_layer_2_step(vector: SIMD256Vector, zeta0: i16, zeta1: i16) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: ntt::ntt_layer_2_step(vector.elements, zeta0, zeta1),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::ntt_layer_3_step_pre} (impl.f_repr ${vector}) zeta"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::ntt_layer_3_step_post} (impl.f_repr ${vector}) zeta (impl.f_repr ${out})"#))]
fn op_ntt_layer_3_step(vector: SIMD256Vector, zeta: i16) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: ntt::ntt_layer_3_step(vector.elements, zeta),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::inv_ntt_layer_1_step_pre} (impl.f_repr ${vector}) zeta0 zeta1 zeta2 zeta3"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::inv_ntt_layer_1_step_post} (impl.f_repr ${vector}) zeta0 zeta1 zeta2 zeta3 (impl.f_repr ${out})"#))]
fn op_inv_ntt_layer_1_step(
    vector: SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: ntt::inv_ntt_layer_1_step(vector.elements, zeta0, zeta1, zeta2, zeta3),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::inv_ntt_layer_2_step_pre} (impl.f_repr ${vector}) zeta0 zeta1"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::inv_ntt_layer_2_step_post} (impl.f_repr ${vector}) zeta0 zeta1 (impl.f_repr ${out})"#))]
fn op_inv_ntt_layer_2_step(vector: SIMD256Vector, zeta0: i16, zeta1: i16) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: ntt::inv_ntt_layer_2_step(vector.elements, zeta0, zeta1),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::inv_ntt_layer_3_step_pre} (impl.f_repr ${vector}) zeta"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::inv_ntt_layer_3_step_post} (impl.f_repr ${vector}) zeta (impl.f_repr ${out})"#))]
fn op_inv_ntt_layer_3_step(vector: SIMD256Vector, zeta: i16) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: ntt::inv_ntt_layer_3_step(vector.elements, zeta),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"${spec::ntt_multiply_pre} (impl.f_repr ${lhs}) (impl.f_repr ${rhs}) zeta0 zeta1 zeta2 zeta3"#))]
#[hax_lib::ensures(|out| fstar!(r#"${spec::ntt_multiply_post} (impl.f_repr ${lhs}) (impl.f_repr ${rhs}) zeta0 zeta1 zeta2 zeta3 (impl.f_repr ${out})"#))]
fn op_ntt_multiply(
    lhs: &SIMD256Vector,
    rhs: &SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                    (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
    );
    SIMD256Vector {
        elements: ntt::ntt_multiply(lhs.elements, rhs.elements, zeta0, zeta1, zeta2, zeta3),
    }
}

// `op_serialize_*` / `op_deserialize_*`: `lax` because the underlying
// `Avx2.Serialize.*` primitives state pre/post in bit-vector form
// (e.g. `forall i. i % 16 >= 1 ==> vector i == 0`), while the trait's
// `serialize_pre_N` / `deserialize_post_N` use array/`bounded` form.
// Bridging requires BitVec lemmas — out of C4′ scope; same status as
// pre-C4′ AVX2 (which had `lax` too).  **Removal plan**: drop `lax`
// and add the BitVec bridge when AVX2 serialize proofs are
// reconstructed (separate task).
#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 1 (impl.f_repr ${vector})"#))]
#[hax_lib::ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 1 (impl.f_repr ${vector}) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 1 (impl.f_repr ${vector}) ${out}"#))]
fn op_serialize_1(vector: SIMD256Vector) -> [u8; 2] {
    serialize::serialize_1(vector.elements)
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() == 2)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $bytes) =. sz 2 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 1 $bytes (impl.f_repr ${out})"#))]
fn op_deserialize_1(bytes: &[u8]) -> SIMD256Vector {
    SIMD256Vector {
        elements: serialize::deserialize_1(bytes),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 4 (impl.f_repr ${vector})"#))]
#[hax_lib::ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 4 (impl.f_repr ${vector}) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 4 (impl.f_repr ${vector}) ${out}"#))]
fn op_serialize_4(vector: SIMD256Vector) -> [u8; 8] {
    serialize::serialize_4(vector.elements)
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() == 8)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $bytes) =. sz 8 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 4 $bytes (impl.f_repr ${out})"#))]
fn op_deserialize_4(bytes: &[u8]) -> SIMD256Vector {
    SIMD256Vector {
        elements: serialize::deserialize_4(bytes),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 10 (impl.f_repr ${vector})"#))]
#[hax_lib::ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 10 (impl.f_repr ${vector}) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 10 (impl.f_repr ${vector}) ${out}"#))]
fn op_serialize_10(vector: SIMD256Vector) -> [u8; 20] {
    serialize::serialize_10(vector.elements)
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() == 20)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $bytes) =. sz 20 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 10 $bytes (impl.f_repr ${out})"#))]
fn op_deserialize_10(bytes: &[u8]) -> SIMD256Vector {
    SIMD256Vector {
        elements: serialize::deserialize_10(bytes),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 12 (impl.f_repr ${vector})"#))]
#[hax_lib::ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 12 (impl.f_repr ${vector}) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 12 (impl.f_repr ${vector}) ${out}"#))]
fn op_serialize_12(vector: SIMD256Vector) -> [u8; 24] {
    serialize::serialize_12(vector.elements)
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() == 24)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $bytes) =. sz 24 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 12 $bytes (impl.f_repr ${out})"#))]
fn op_deserialize_12(bytes: &[u8]) -> SIMD256Vector {
    SIMD256Vector {
        elements: serialize::deserialize_12(bytes),
    }
}

// =====================================================================
// `impl Operations for SIMD256Vector`
//
// Every method is a one-line call to its `op_*` (with matching trait
// pre/post — subtyping check is `P ==> P`) or to a free helper
// (`vec_zero`, `vec_to_i16_array`, `vec_from_i16_array`, `from_bytes`,
// `to_bytes`).  No proof code lives inside the impl.
// =====================================================================
#[hax_lib::attributes]
impl Operations for SIMD256Vector {
    #[inline(always)]
    #[ensures(|out| fstar!(r#"impl.f_repr out == Seq.create 16 (mk_i16 0)"#))]
    fn ZERO() -> Self {
        vec_zero()
    }

    #[requires(array.len() == 16)]
    #[ensures(|out| fstar!(r#"impl.f_repr out == $array"#))]
    #[inline(always)]
    fn from_i16_array(array: &[i16]) -> Self {
        vec_from_i16_array(array)
    }

    #[ensures(|out| fstar!(r#"out == impl.f_repr $x"#))]
    #[inline(always)]
    fn to_i16_array(x: Self) -> [i16; 16] {
        vec_to_i16_array(x)
    }

    #[requires(array.len() >= 32)]
    #[inline(always)]
    fn from_bytes(array: &[u8]) -> Self {
        from_bytes(array)
    }

    #[requires(bytes.len() >= 32)]
    #[inline(always)]
    #[ensures(|_| future(bytes).len() == bytes.len())]
    fn to_bytes(x: Self, bytes: &mut [u8]) {
        to_bytes(x, bytes)
    }

    #[requires(fstar!(r#"${spec::add_pre} (impl.f_repr ${lhs}) (impl.f_repr ${rhs})"#))]
    #[ensures(|result| fstar!(r#"${spec::add_post} (impl.f_repr ${lhs}) (impl.f_repr ${rhs}) (impl.f_repr ${result})"#))]
    #[inline(always)]
    fn add(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::add(lhs.elements, rhs.elements),
        }
    }

    #[requires(fstar!(r#"${spec::sub_pre} (impl.f_repr ${lhs}) (impl.f_repr ${rhs})"#))]
    #[ensures(|result| fstar!(r#"${spec::sub_post} (impl.f_repr ${lhs}) (impl.f_repr ${rhs}) (impl.f_repr ${result})"#))]
    #[inline(always)]
    fn sub(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: arithmetic::sub(lhs.elements, rhs.elements),
        }
    }

    #[requires(fstar!(r#"${spec::multiply_by_constant_pre} (impl.f_repr ${vec}) c"#))]
    #[ensures(|result| fstar!(r#"${spec::multiply_by_constant_post} (impl.f_repr ${vec}) c (impl.f_repr ${result})"#))]
    #[inline(always)]
    fn multiply_by_constant(vec: Self, c: i16) -> Self {
        Self {
            elements: arithmetic::multiply_by_constant(vec.elements, c),
        }
    }

    #[requires(spec::cond_subtract_3329_pre(&vector.repr()))]
    #[ensures(|out| spec::cond_subtract_3329_post(&vector.repr(), &out.repr()))]
    #[inline(always)]
    fn cond_subtract_3329(vector: Self) -> Self {
        op_cond_subtract_3329(vector)
    }

    #[requires(spec::barrett_reduce_pre(&vector.repr()))]
    #[ensures(|result| spec::barrett_reduce_post(&vector.repr(), &result.repr()))]
    #[inline(always)]
    fn barrett_reduce(vector: Self) -> Self {
        op_barrett_reduce(vector)
    }

    #[inline(always)]
    #[requires(spec::montgomery_multiply_by_constant_pre(&vector.repr(), constant))]
    #[ensures(|result| spec::montgomery_multiply_by_constant_post(&vector.repr(), constant, &result.repr()))]
    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self {
        op_montgomery_multiply_by_constant(vector, constant)
    }

    #[requires(spec::to_unsigned_representative_pre(&a.repr()))]
    #[ensures(|result| spec::to_unsigned_representative_post(&a.repr(), &result.repr()))]
    fn to_unsigned_representative(a: Self) -> Self {
        op_to_unsigned_representative(a)
    }

    #[requires(fstar!(r#"${spec::compress_1_pre} (impl.f_repr $vector)"#))]
    #[ensures(|out| fstar!(r#"${spec::compress_1_post} (impl.f_repr $vector) (impl.f_repr $out)"#))]
    #[inline(always)]
    fn compress_1(vector: Self) -> Self {
        op_compress_1(vector)
    }

    #[requires(fstar!(r#"${spec::compress_pre} (impl.f_repr $vector) $COEFFICIENT_BITS"#))]
    #[ensures(|out| fstar!(r#"${spec::compress_post} (impl.f_repr $vector) $COEFFICIENT_BITS (impl.f_repr $out)"#))]
    #[inline(always)]
    fn compress<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        op_compress::<COEFFICIENT_BITS>(vector)
    }

    #[requires(fstar!(r#"${spec::decompress_1_pre} (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"${spec::decompress_1_post} (impl.f_repr $a) (impl.f_repr $out)"#))]
    fn decompress_1(a: Self) -> Self {
        op_decompress_1(a)
    }

    #[requires(fstar!(r#"${spec::decompress_ciphertext_coefficient_pre} (impl.f_repr $vector) $COEFFICIENT_BITS"#))]
    #[ensures(|out| fstar!(r#"${spec::decompress_ciphertext_coefficient_post} (impl.f_repr $vector) $COEFFICIENT_BITS (impl.f_repr $out)"#))]
    #[inline(always)]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vector: Self) -> Self {
        op_decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(vector)
    }

    #[requires(fstar!(r#"${spec::ntt_layer_1_step_pre} (impl.f_repr ${vector}) zeta0 zeta1 zeta2 zeta3"#))]
    #[ensures(|out| fstar!(r#"${spec::ntt_layer_1_step_post} (impl.f_repr ${vector}) zeta0 zeta1 zeta2 zeta3 (impl.f_repr ${out})"#))]
    #[inline(always)]
    fn ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        op_ntt_layer_1_step(vector, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"${spec::ntt_layer_2_step_pre} (impl.f_repr ${vector}) zeta0 zeta1"#))]
    #[ensures(|out| fstar!(r#"${spec::ntt_layer_2_step_post} (impl.f_repr ${vector}) zeta0 zeta1 (impl.f_repr ${out})"#))]
    #[inline(always)]
    fn ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        op_ntt_layer_2_step(vector, zeta0, zeta1)
    }

    #[requires(fstar!(r#"${spec::ntt_layer_3_step_pre} (impl.f_repr ${vector}) zeta"#))]
    #[ensures(|out| fstar!(r#"${spec::ntt_layer_3_step_post} (impl.f_repr ${vector}) zeta (impl.f_repr ${out})"#))]
    #[inline(always)]
    fn ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        op_ntt_layer_3_step(vector, zeta)
    }

    #[requires(fstar!(r#"${spec::inv_ntt_layer_1_step_pre} (impl.f_repr ${vector}) zeta0 zeta1 zeta2 zeta3"#))]
    #[ensures(|out| fstar!(r#"${spec::inv_ntt_layer_1_step_post} (impl.f_repr ${vector}) zeta0 zeta1 zeta2 zeta3 (impl.f_repr ${out})"#))]
    #[inline(always)]
    fn inv_ntt_layer_1_step(vector: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        op_inv_ntt_layer_1_step(vector, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"${spec::inv_ntt_layer_2_step_pre} (impl.f_repr ${vector}) zeta0 zeta1"#))]
    #[ensures(|out| fstar!(r#"${spec::inv_ntt_layer_2_step_post} (impl.f_repr ${vector}) zeta0 zeta1 (impl.f_repr ${out})"#))]
    #[inline(always)]
    fn inv_ntt_layer_2_step(vector: Self, zeta0: i16, zeta1: i16) -> Self {
        op_inv_ntt_layer_2_step(vector, zeta0, zeta1)
    }

    #[requires(fstar!(r#"${spec::inv_ntt_layer_3_step_pre} (impl.f_repr ${vector}) zeta"#))]
    #[ensures(|out| fstar!(r#"${spec::inv_ntt_layer_3_step_post} (impl.f_repr ${vector}) zeta (impl.f_repr ${out})"#))]
    #[inline(always)]
    fn inv_ntt_layer_3_step(vector: Self, zeta: i16) -> Self {
        op_inv_ntt_layer_3_step(vector, zeta)
    }

    #[requires(fstar!(r#"${spec::ntt_multiply_pre} (impl.f_repr ${lhs}) (impl.f_repr ${rhs}) zeta0 zeta1 zeta2 zeta3"#))]
    #[ensures(|out| fstar!(r#"${spec::ntt_multiply_post} (impl.f_repr ${lhs}) (impl.f_repr ${rhs}) zeta0 zeta1 zeta2 zeta3 (impl.f_repr ${out})"#))]
    #[inline(always)]
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        op_ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 1 (impl.f_repr $vector)"#))]
    #[ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 1 (impl.f_repr $vector) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 1 (impl.f_repr $vector) $out"#))]
    #[inline(always)]
    fn serialize_1(vector: Self) -> [u8; 2] {
        op_serialize_1(vector)
    }

    #[requires(bytes.len() == 2)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $bytes) =. sz 2 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 1 $bytes (impl.f_repr $out)"#))]
    #[inline(always)]
    fn deserialize_1(bytes: &[u8]) -> Self {
        op_deserialize_1(bytes)
    }

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 4 (impl.f_repr $vector)"#))]
    #[ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 4 (impl.f_repr $vector) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 4 (impl.f_repr $vector) $out"#))]
    #[inline(always)]
    fn serialize_4(vector: Self) -> [u8; 8] {
        op_serialize_4(vector)
    }

    #[requires(bytes.len() == 8)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $bytes) =. sz 8 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 4 $bytes (impl.f_repr $out)"#))]
    #[inline(always)]
    fn deserialize_4(bytes: &[u8]) -> Self {
        op_deserialize_4(bytes)
    }

    #[inline(always)]
    fn serialize_5(vector: Self) -> [u8; 10] {
        serialize::serialize_5(vector.elements)
    }

    #[requires(bytes.len() == 10)]
    #[inline(always)]
    fn deserialize_5(bytes: &[u8]) -> Self {
        hax_lib::fstar!(r#"assert (v (Core_models.Slice.impl__len $bytes) == Seq.length $bytes)"#);
        Self {
            elements: serialize::deserialize_5(bytes),
        }
    }

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 10 (impl.f_repr $vector)"#))]
    #[ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 10 (impl.f_repr $vector) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 10 (impl.f_repr $vector) $out"#))]
    #[inline(always)]
    fn serialize_10(vector: Self) -> [u8; 20] {
        op_serialize_10(vector)
    }

    #[requires(bytes.len() == 20)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $bytes) =. sz 20 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 10 $bytes (impl.f_repr $out)"#))]
    #[inline(always)]
    fn deserialize_10(bytes: &[u8]) -> Self {
        op_deserialize_10(bytes)
    }

    #[inline(always)]
    fn serialize_11(vector: Self) -> [u8; 22] {
        serialize::serialize_11(vector.elements)
    }

    #[requires(bytes.len() == 22)]
    #[inline(always)]
    fn deserialize_11(bytes: &[u8]) -> Self {
        Self {
            elements: serialize::deserialize_11(bytes),
        }
    }

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 12 (impl.f_repr $vector)"#))]
    #[ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 12 (impl.f_repr $vector) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 12 (impl.f_repr $vector) $out"#))]
    #[inline(always)]
    fn serialize_12(vector: Self) -> [u8; 24] {
        op_serialize_12(vector)
    }

    #[requires(bytes.len() == 24)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $bytes) =. sz 24 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 12 $bytes (impl.f_repr $out)"#))]
    #[inline(always)]
    fn deserialize_12(bytes: &[u8]) -> Self {
        op_deserialize_12(bytes)
    }

    #[inline(always)]
    #[requires(input.len() == 24 && out.len() == 16)]
    #[ensures(|result| (future(out).len() == 16 && result <= 16).to_prop() & (
            hax_lib::forall(|j: usize|
                hax_lib::implies(j < result,
                    future(out)[j] >= 0 && future(out)[j] <= 3328))))]
    fn rej_sample(input: &[u8], out: &mut [i16]) -> usize {
        sampling::rejection_sample(input, out)
    }
}
