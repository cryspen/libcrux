module Libcrux_ml_kem.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i:usize = i in
          let coefficient:v_Vector =
            Libcrux_traits.f_compress 10l
              (Libcrux_traits.f_to_unsigned_representative (re
                      .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                    <:
                    v_Vector)
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 20) = Libcrux_traits.f_serialize_10_ coefficient in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 20 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 20 *! i <: usize) +! sz 20 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice (serialized.[ {
                        Core.Ops.Range.f_start = sz 20 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 20 *! i <: usize) +! sz 20 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Rust_primitives.unsize bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i:usize = i in
          let coefficient:v_Vector =
            Libcrux_traits.f_compress 11l
              (Libcrux_traits.f_to_unsigned_representative (re
                      .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                    <:
                    v_Vector)
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 22) = Libcrux_traits.f_serialize_11_ coefficient in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 22 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 22 *! i <: usize) +! sz 22 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice (serialized.[ {
                        Core.Ops.Range.f_start = sz 22 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 22 *! i <: usize) +! sz 22 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Rust_primitives.unsize bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_4_
      (v_OUT_LEN: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i:usize = i in
          let coefficient:v_Vector =
            Libcrux_traits.f_compress 4l
              (Libcrux_traits.f_to_unsigned_representative (re
                      .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                    <:
                    v_Vector)
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 8) = Libcrux_traits.f_serialize_4_ coefficient in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 8 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 8 *! i <: usize) +! sz 8 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice (serialized.[ {
                        Core.Ops.Range.f_start = sz 8 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 8 *! i <: usize) +! sz 8 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Rust_primitives.unsize bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_5_
      (v_OUT_LEN: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i:usize = i in
          let coefficients:v_Vector =
            Libcrux_traits.f_compress 5l
              (Libcrux_traits.f_to_unsigned_representative (re
                      .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                    <:
                    v_Vector)
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 10) = Libcrux_traits.f_serialize_5_ coefficients in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 10 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 10 *! i <: usize) +! sz 10 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice (serialized.[ {
                        Core.Ops.Range.f_start = sz 10 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 10 *! i <: usize) +! sz 10 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Rust_primitives.unsize bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_message
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let serialized:t_Array u8 (sz 32) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 16
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 (sz 32) = serialized in
          let i:usize = i in
          let coefficient:v_Vector =
            Libcrux_traits.f_to_unsigned_representative (re.Libcrux_ml_kem.Polynomial.f_coefficients.[
                  i ]
                <:
                v_Vector)
          in
          let coefficient_compressed:v_Vector = Libcrux_traits.f_compress_1_ coefficient in
          let bytes:t_Array u8 (sz 2) = Libcrux_traits.f_serialize_1_ coefficient_compressed in
          let serialized:t_Array u8 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 2 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 2 *! i <: usize) +! sz 2 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice (serialized.[ {
                        Core.Ops.Range.f_start = sz 2 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 2 *! i <: usize) +! sz 2 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Rust_primitives.unsize bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 10ul -> compress_then_serialize_10_ v_OUT_LEN re
  | 11ul -> compress_then_serialize_11_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let compress_then_serialize_ring_element_v
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 4ul -> compress_then_serialize_4_ v_OUT_LEN re
  | 5ul -> compress_then_serialize_5_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_then_decompress_10_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 20) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:v_Vector = Libcrux_traits.f_deserialize_10_ bytes in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_traits.f_decompress 10l coefficient <: v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_11_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 22) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:v_Vector = Libcrux_traits.f_deserialize_11_ bytes in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_traits.f_decompress 11l coefficient <: v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_4_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 8) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:v_Vector = Libcrux_traits.f_deserialize_4_ bytes in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_traits.f_decompress 4l coefficient <: v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_5_
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 10) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
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
                (Libcrux_traits.f_deserialize_5_ bytes <: v_Vector)
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
                (Libcrux_traits.f_decompress 5l
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

let deserialize_then_decompress_message
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Array u8 (sz 32))
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 16
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i:usize = i in
          let coefficient_compressed:v_Vector =
            Libcrux_traits.f_deserialize_1_ (serialized.[ {
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
                (Libcrux_traits.f_decompress_1_ coefficient_compressed <: v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 10ul -> deserialize_then_decompress_10_ serialized
  | 11ul -> deserialize_then_decompress_11_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_then_decompress_ring_element_v
      (v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 4ul -> deserialize_then_decompress_4_ serialized
  | 5ul -> deserialize_then_decompress_5_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_to_reduced_ring_element
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 24) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:v_Vector = Libcrux_traits.f_deserialize_12_ bytes in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_traits.f_cond_subtract_3329_ coefficient <: v_Vector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector
          in
          re)
  in
  re

let deserialize_ring_elements_reduced
      (v_PUBLIC_KEY_SIZE v_K: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (public_key: t_Slice u8)
     =
  let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl__ZERO ()
        <:
        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
  in
  let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact public_key
                  Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      deserialized_pk
      (fun deserialized_pk temp_1_ ->
          let deserialized_pk:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            v_K =
            deserialized_pk
          in
          let i, ring_element:(usize & t_Slice u8) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize deserialized_pk
            i
            (deserialize_to_reduced_ring_element ring_element
              <:
              Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          <:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
  in
  deserialized_pk

let deserialize_to_uncompressed_ring_element
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (serialized: t_Slice u8)
     =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 24) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
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
              (Libcrux_traits.f_deserialize_12_ bytes <: v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  re

let serialize_uncompressed_ring_element
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_traits.t_Operations v_Vector)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let serialized:t_Array u8 (sz 384) = Rust_primitives.Hax.repeat 0uy (sz 384) in
  let serialized:t_Array u8 (sz 384) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 (sz 384) = serialized in
          let i:usize = i in
          let coefficient:v_Vector =
            Libcrux_traits.f_to_unsigned_representative (re.Libcrux_ml_kem.Polynomial.f_coefficients.[
                  i ]
                <:
                v_Vector)
          in
          let bytes:t_Array u8 (sz 24) = Libcrux_traits.f_serialize_12_ coefficient in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
              ({
                  Core.Ops.Range.f_start = sz 24 *! i <: usize;
                  Core.Ops.Range.f_end = (sz 24 *! i <: usize) +! sz 24 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice (serialized.[ {
                        Core.Ops.Range.f_start = sz 24 *! i <: usize;
                        Core.Ops.Range.f_end = (sz 24 *! i <: usize) +! sz 24 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Rust_primitives.unsize bytes <: t_Slice u8)
                <:
                t_Slice u8)
          in
          serialized)
  in
  serialized
