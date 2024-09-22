module Libcrux_ml_kem.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let to_unsigned_field_modulus
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a: v_Vector)
     =
  let _:Prims.unit = reveal_opaque (`%field_modulus_range) (field_modulus_range #v_Vector) in
  let result:v_Vector = Libcrux_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector a in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let _:Prims.unit = assert_norm (pow2 10 == 1024) in
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun serialized i ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i:usize = i in
          v i >= 0 /\ v i <= 16 /\ v i < 16 ==> coefficients_field_modulus_range re)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i:usize = i in
          let _:Prims.unit = assert (20 * v i + 20 <= 320) in
          let _:Prims.unit =
            reveal_opaque (`%coefficients_field_modulus_range)
              (coefficients_field_modulus_range #v_Vector)
          in
          let coefficient:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_compress #v_Vector
              #FStar.Tactics.Typeclasses.solve
              10l
              (to_unsigned_field_modulus #v_Vector
                  (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 20) =
            Libcrux_ml_kem.Vector.Traits.f_serialize_10_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 20 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 20 *! i <: usize) +! sz 20 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start = sz 20 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 20 *! i <: usize) +! sz 20 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  let result:t_Array u8 v_OUT_LEN = serialized in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

#push-options "--admit_smt_queries true"

let compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i:usize = i in
          let coefficient:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_compress #v_Vector
              #FStar.Tactics.Typeclasses.solve
              11l
              (Libcrux_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector
                  (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 22) =
            Libcrux_ml_kem.Vector.Traits.f_serialize_11_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 22 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 22 *! i <: usize) +! sz 22 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start = sz 22 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 22 *! i <: usize) +! sz 22 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  serialized

#pop-options

let compress_then_serialize_4_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit = assert_norm (pow2 4 == 16) in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun serialized i ->
          let serialized:t_Slice u8 = serialized in
          let i:usize = i in
          v i >= 0 /\ v i <= 16 /\ v i < 16 ==>
          (Seq.length serialized == 128 /\ coefficients_field_modulus_range re))
      serialized
      (fun serialized i ->
          let serialized:t_Slice u8 = serialized in
          let i:usize = i in
          let _:Prims.unit = assert (8 * v i + 8 <= 128) in
          let _:Prims.unit =
            reveal_opaque (`%coefficients_field_modulus_range)
              (coefficients_field_modulus_range #v_Vector)
          in
          let coefficient:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_compress #v_Vector
              #FStar.Tactics.Typeclasses.solve
              4l
              (to_unsigned_field_modulus #v_Vector
                  (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 8) =
            Libcrux_ml_kem.Vector.Traits.f_serialize_4_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 8 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 8 *! i <: usize) +! sz 8 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start = sz 8 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 8 *! i <: usize) +! sz 8 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  let result:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = admit () (* Panic freedom *) in
  let hax_temp_output:Prims.unit = result in
  serialized

#push-options "--admit_smt_queries true"

let compress_then_serialize_5_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized i ->
          let serialized:t_Slice u8 = serialized in
          let i:usize = i in
          let coefficients:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_compress #v_Vector
              #FStar.Tactics.Typeclasses.solve
              5l
              (Libcrux_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector
                  (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 10) =
            Libcrux_ml_kem.Vector.Traits.f_serialize_5_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficients
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 10 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 10 *! i <: usize) +! sz 10 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start = sz 10 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 10 *! i <: usize) +! sz 10 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  serialized

#pop-options

let compress_then_serialize_message
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 16)
      (fun serialized i ->
          let serialized:t_Array u8 (sz 32) = serialized in
          let i:usize = i in
          v i < 16 ==> coefficients_field_modulus_range re)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 (sz 32) = serialized in
          let i:usize = i in
          let _:Prims.unit = assert (2 * v i + 2 <= 32) in
          let _:Prims.unit =
            reveal_opaque (`%coefficients_field_modulus_range)
              (coefficients_field_modulus_range #v_Vector)
          in
          let coefficient:v_Vector =
            to_unsigned_field_modulus #v_Vector
              (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
          in
          let coefficient_compressed:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_compress_1_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient
          in
          let bytes:t_Array u8 (sz 2) =
            Libcrux_ml_kem.Vector.Traits.f_serialize_1_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient_compressed
          in
          let serialized:t_Array u8 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 2 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 2 *! i <: usize) +! sz 2 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start = sz 2 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 2 *! i <: usize) +! sz 2 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  let result:t_Array u8 (sz 32) = serialized in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let _:Prims.unit =
    assert ((v (cast v_COMPRESSION_FACTOR <: u32) == 10) \/
        (v (cast v_COMPRESSION_FACTOR <: u32) == 11));
    Rust_primitives.Integers.mk_int_equiv_lemma #usize_inttype (v v_COMPRESSION_FACTOR)
  in
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 10ul -> compress_then_serialize_10_ v_OUT_LEN #v_Vector re
  | 11ul -> compress_then_serialize_11_ v_OUT_LEN #v_Vector re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let compress_then_serialize_ring_element_v
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    assert ((v (cast v_COMPRESSION_FACTOR <: u32) == 4) \/
        (v (cast v_COMPRESSION_FACTOR <: u32) == 5));
    Rust_primitives.Integers.mk_int_equiv_lemma #usize_inttype (v v_COMPRESSION_FACTOR)
  in
  let out, hax_temp_output:(t_Slice u8 & Prims.unit) =
    match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
    | 4ul -> compress_then_serialize_4_ #v_Vector re out, () <: (t_Slice u8 & Prims.unit)
    | 5ul -> compress_then_serialize_5_ #v_Vector re out, () <: (t_Slice u8 & Prims.unit)
    | _ ->
      out,
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
      <:
      (t_Slice u8 & Prims.unit)
  in
  out

let deserialize_then_decompress_10_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    assert (v ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 10) /! sz 8) == 320)
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
  in
  let v__coefficients_length:usize =
    Core.Slice.impl__len #v_Vector (re.Libcrux_ml_kem.Polynomial.f_coefficients <: t_Slice v_Vector)
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 20)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_deserialize_10_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              bytes
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    10l
                    coefficient
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_11_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    assert (v ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 11) /! sz 8) == 352)
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 22)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_deserialize_11_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              bytes
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    11l
                    coefficient
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_4_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    assert (v ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 4) /! sz 8) == 128)
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 8)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_deserialize_4_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              bytes
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    4l
                    coefficient
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_5_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    assert (v ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 5) /! sz 8) == 160)
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 10)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_deserialize_5_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    bytes
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    5l
                    (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

#push-options "--admit_smt_queries true"

let deserialize_then_decompress_message
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Array u8 (sz 32))
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 16)
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re i ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i:usize = i in
          let coefficient_compressed:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_deserialize_1_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (serialized.[ {
                    Core.Ops.Range.f_start = sz 2 *! i <: usize;
                    Core.Ops.Range.f_end = (sz 2 *! i <: usize) +! sz 2 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.decompress_1_ #v_Vector coefficient_compressed
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

#pop-options

let deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    assert ((v (cast v_COMPRESSION_FACTOR <: u32) == 10) \/
        (v (cast v_COMPRESSION_FACTOR <: u32) == 11))
  in
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 10ul -> deserialize_then_decompress_10_ #v_Vector serialized
  | 11ul -> deserialize_then_decompress_11_ #v_Vector serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_then_decompress_ring_element_v
      (v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    assert ((v (cast v_COMPRESSION_FACTOR <: u32) == 4) \/
        (v (cast v_COMPRESSION_FACTOR <: u32) == 5))
  in
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 4ul -> deserialize_then_decompress_4_ #v_Vector serialized
  | 5ul -> deserialize_then_decompress_5_ #v_Vector serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

#push-options "--admit_smt_queries true"

let deserialize_to_reduced_ring_element
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit = assert (v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT / 24 == 16) in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 24)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_deserialize_12_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              bytes
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_cond_subtract_3329_ #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    coefficient
                  <:
                  v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

#pop-options

let deserialize_ring_elements_reduced
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: t_Slice u8)
     =
  let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun v__i ->
          let v__i:usize = v__i in
          Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
      public_key
      (fun deserialized_pk temp_1_ ->
          let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            v_K =
            deserialized_pk
          in
          let _:usize = temp_1_ in
          true)
      deserialized_pk
      (fun deserialized_pk temp_1_ ->
          let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            v_K =
            deserialized_pk
          in
          let i, ring_element:(usize & t_Slice u8) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize deserialized_pk
            i
            (deserialize_to_reduced_ring_element #v_Vector ring_element
              <:
              Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          <:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
  in
  deserialized_pk

let deserialize_to_uncompressed_ring_element
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit = assert (v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT / 24 == 16) in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 24)
      serialized
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          {
            re with
            Libcrux_ml_kem.Polynomial.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux_ml_kem.Polynomial.f_coefficients
              i
              (Libcrux_ml_kem.Vector.Traits.f_deserialize_12_ #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  bytes
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  re

let serialize_uncompressed_ring_element
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let _:Prims.unit = assert_norm (pow2 12 == 4096) in
  let serialized:t_Array u8 (sz 384) = Rust_primitives.Hax.repeat 0uy (sz 384) in
  let serialized:t_Array u8 (sz 384) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
      (fun serialized i ->
          let serialized:t_Array u8 (sz 384) = serialized in
          let i:usize = i in
          v i >= 0 /\ v i <= 16 /\ v i < 16 ==> coefficients_field_modulus_range re)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 (sz 384) = serialized in
          let i:usize = i in
          let _:Prims.unit = assert (24 * v i + 24 <= 384) in
          let _:Prims.unit =
            reveal_opaque (`%coefficients_field_modulus_range)
              (coefficients_field_modulus_range #v_Vector)
          in
          let coefficient:v_Vector =
            to_unsigned_field_modulus #v_Vector
              (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
          in
          let bytes:t_Array u8 (sz 24) =
            Libcrux_ml_kem.Vector.Traits.f_serialize_12_ #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 24 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 24 *! i <: usize) +! sz 24 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (serialized.[ {
                        Core.Ops.Range.f_start = sz 24 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 24 *! i <: usize) +! sz 24 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  let result:t_Array u8 (sz 384) = serialized in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result
