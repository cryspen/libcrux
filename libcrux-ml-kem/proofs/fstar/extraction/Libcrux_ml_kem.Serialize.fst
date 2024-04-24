module Libcrux_ml_kem.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
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
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_compress 10uy
              (Libcrux_ml_kem.Simd.Simd_trait.f_to_unsigned_representative (re
                      .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                    <:
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let bytes:t_Array u8 (sz 10) =
            Libcrux_ml_kem.Simd.Simd_trait.f_serialize_10_ coefficient
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 10 *! i <: usize)
              (bytes.[ sz 0 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 1 <: usize)
              (bytes.[ sz 1 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 2 <: usize)
              (bytes.[ sz 2 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 3 <: usize)
              (bytes.[ sz 3 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 4 <: usize)
              (bytes.[ sz 4 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 5 <: usize)
              (bytes.[ sz 5 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 6 <: usize)
              (bytes.[ sz 6 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 7 <: usize)
              (bytes.[ sz 7 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 8 <: usize)
              (bytes.[ sz 8 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 10 *! i <: usize) +! sz 9 <: usize)
              (bytes.[ sz 9 ] <: u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
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
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_compress 11uy
              (Libcrux_ml_kem.Simd.Simd_trait.f_to_unsigned_representative (re
                      .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                    <:
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let bytes:t_Array u8 (sz 11) =
            Libcrux_ml_kem.Simd.Simd_trait.f_serialize_11_ coefficient
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 11 *! i <: usize)
              (bytes.[ sz 0 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 1 <: usize)
              (bytes.[ sz 1 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 2 <: usize)
              (bytes.[ sz 2 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 3 <: usize)
              (bytes.[ sz 3 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 4 <: usize)
              (bytes.[ sz 4 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 5 <: usize)
              (bytes.[ sz 5 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 6 <: usize)
              (bytes.[ sz 6 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 7 <: usize)
              (bytes.[ sz 7 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 8 <: usize)
              (bytes.[ sz 8 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 9 <: usize)
              (bytes.[ sz 9 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 10 <: usize)
              (bytes.[ sz 10 ] <: u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_4_
      (v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
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
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_compress 4uy
              (Libcrux_ml_kem.Simd.Simd_trait.f_to_unsigned_representative (re
                      .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                    <:
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let bytes:t_Array u8 (sz 4) = Libcrux_ml_kem.Simd.Simd_trait.f_serialize_4_ coefficient in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 4 *! i <: usize)
              (bytes.[ sz 0 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 4 *! i <: usize) +! sz 1 <: usize)
              (bytes.[ sz 1 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 4 *! i <: usize) +! sz 2 <: usize)
              (bytes.[ sz 2 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 4 *! i <: usize) +! sz 3 <: usize)
              (bytes.[ sz 3 ] <: u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_5_
      (v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
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
          let coefficients:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_compress 5uy
              (Libcrux_ml_kem.Simd.Simd_trait.f_to_unsigned_representative (re
                      .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                    <:
                    Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let bytes5:t_Array u8 (sz 5) =
            Libcrux_ml_kem.Simd.Simd_trait.f_serialize_5_ coefficients
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              (bytes5.[ sz 0 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              (bytes5.[ sz 1 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (bytes5.[ sz 2 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              (bytes5.[ sz 3 ] <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              (bytes5.[ sz 4 ] <: u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_message (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let serialized:t_Array u8 (sz 32) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      serialized
      (fun serialized i ->
          let serialized:t_Array u8 (sz 32) = serialized in
          let i:usize = i in
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_to_unsigned_representative (re
                  .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let coefficient_compressed:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_compress_1_ coefficient
          in
          let serialized:t_Array u8 (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              i
              (Libcrux_ml_kem.Simd.Simd_trait.f_serialize_1_ coefficient_compressed <: u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
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
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
     =
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 4ul -> compress_then_serialize_4_ v_OUT_LEN re
  | 5ul -> compress_then_serialize_5_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_then_decompress_10_ (serialized: t_Slice u8) =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Libcrux_ml_kem.Polynomial.impl__PolynomialRingElement__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 10) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_10_ bytes
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_decompress 10l coefficient
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_11_ (serialized: t_Slice u8) =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Libcrux_ml_kem.Polynomial.impl__PolynomialRingElement__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 11) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_11_ bytes
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_decompress 11l coefficient
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_4_ (serialized: t_Slice u8) =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Libcrux_ml_kem.Polynomial.impl__PolynomialRingElement__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 4) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_4_ bytes
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_decompress 4l coefficient
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_5_ (serialized: t_Slice u8) =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Libcrux_ml_kem.Polynomial.impl__PolynomialRingElement__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 5) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_5_ bytes
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_decompress 5l
                    (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                      <:
                      Libcrux_ml_kem.Simd.Portable.t_PortableVector)
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_message (serialized: t_Array u8 (sz 32)) =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Libcrux_ml_kem.Polynomial.impl__PolynomialRingElement__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 32
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement = re in
          let i:usize = i in
          let coefficient_compressed:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_1_ (serialized.[ i ] <: u8)
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_decompress_1_ coefficient_compressed
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
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
      (serialized: t_Slice u8)
     =
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 4ul -> deserialize_then_decompress_4_ serialized
  | 5ul -> deserialize_then_decompress_5_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_to_reduced_ring_element (serialized: t_Slice u8) =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Libcrux_ml_kem.Polynomial.impl__PolynomialRingElement__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 12) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_12_ bytes
          in
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
            {
              re with
              Libcrux_ml_kem.Polynomial.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux_ml_kem.Polynomial.f_coefficients
                i
                (Libcrux_ml_kem.Simd.Simd_trait.f_cond_subtract_3329_ coefficient
                  <:
                  Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            }
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_ring_elements_reduced (v_PUBLIC_KEY_SIZE v_K: usize) (public_key: t_Slice u8) =
  let deserialized_pk:t_Array Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl__PolynomialRingElement__ZERO ()
        <:
        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
      v_K
  in
  let deserialized_pk:t_Array Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_K =
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
          let deserialized_pk:t_Array Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_K =
            deserialized_pk
          in
          let i, ring_element:(usize & t_Slice u8) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize deserialized_pk
            i
            (deserialize_to_reduced_ring_element ring_element
              <:
              Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
          <:
          t_Array Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_K)
  in
  deserialized_pk

let deserialize_to_uncompressed_ring_element (serialized: t_Slice u8) =
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Libcrux_ml_kem.Polynomial.impl__PolynomialRingElement__ZERO ()
  in
  let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 12) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          {
            re with
            Libcrux_ml_kem.Polynomial.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux_ml_kem.Polynomial.f_coefficients
              i
              (Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_12_ bytes
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
            <:
            t_Array Libcrux_ml_kem.Simd.Portable.t_PortableVector (sz 32)
          }
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
  in
  re

let serialize_uncompressed_ring_element (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement) =
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
          let coefficient:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
            Libcrux_ml_kem.Simd.Simd_trait.f_to_unsigned_representative (re
                  .Libcrux_ml_kem.Polynomial.f_coefficients.[ i ]
                <:
                Libcrux_ml_kem.Simd.Portable.t_PortableVector)
          in
          let bytes:t_Array u8 (sz 12) =
            Libcrux_ml_kem.Simd.Simd_trait.f_serialize_12_ coefficient
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 12 *! i <: usize)
              (bytes.[ sz 0 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 1 <: usize)
              (bytes.[ sz 1 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 2 <: usize)
              (bytes.[ sz 2 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 3 <: usize)
              (bytes.[ sz 3 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 4 <: usize)
              (bytes.[ sz 4 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 5 <: usize)
              (bytes.[ sz 5 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 6 <: usize)
              (bytes.[ sz 6 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 7 <: usize)
              (bytes.[ sz 7 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 8 <: usize)
              (bytes.[ sz 8 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 9 <: usize)
              (bytes.[ sz 9 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 10 <: usize)
              (bytes.[ sz 10 ] <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 12 *! i <: usize) +! sz 11 <: usize)
              (bytes.[ sz 11 ] <: u8)
          in
          serialized)
  in
  serialized
