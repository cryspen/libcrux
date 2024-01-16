module Hacspec_kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let bits_to_bytes (bits: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let _:Prims.unit =
    if ~.(((Alloc.Vec.impl_1__len bits <: usize) %! sz 8 <: usize) =. sz 0 <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits.len() % 8 == 0"
          <:
          Rust_primitives.Hax.t_Never)
  in
  let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new in
  let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks (
                Core.Ops.Deref.f_deref bits <: t_Slice u8)
              (sz 8)
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      bytes
      (fun bytes bit_chunk ->
          let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = bytes in
          let bit_chunk:t_Slice u8 = bit_chunk in
          let byte_value:u8 = 0uy in
          let byte_value:u8 =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                      (Core.Iter.Traits.Collect.f_into_iter bit_chunk <: Core.Slice.Iter.t_Iter u8)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
                <:
                Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
              byte_value
              (fun byte_value temp_1_ ->
                  let byte_value:u8 = byte_value in
                  let i, bit:(usize & u8) = temp_1_ in
                  byte_value +!
                  (bit *! (Core.Num.impl__u8__pow 2uy (cast (i <: usize) <: u32) <: u8) <: u8)
                  <:
                  u8)
          in
          let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push bytes byte_value
          in
          bytes)
  in
  bytes

let byte_encode
      (bits_per_coefficient: usize)
      (re:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let _:Prims.unit =
    if ~.(bits_per_coefficient <=. Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits_per_coefficient <= BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new in
  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Hacspec_lib.Ring.impl_2__coefficients
              (sz 256)
              re
            <:
            t_Array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
        <:
        Core.Slice.Iter.t_Iter (Hacspec_lib.Field.t_PrimeFieldElement 3329us))
      re_bits
      (fun re_bits coefficient ->
          let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = re_bits in
          let coefficient:Hacspec_lib.Field.t_PrimeFieldElement 3329us = coefficient in
          let coefficient_value:u16 = coefficient.Hacspec_lib.Field.f_value in
          let coefficient_value, re_bits:(u16 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = bits_per_coefficient
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Core.Ops.Range.t_Range usize)
              (coefficient_value, re_bits <: (u16 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
              (fun temp_0_ temp_1_ ->
                  let coefficient_value, re_bits:(u16 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
                    temp_0_
                  in
                  let _:usize = temp_1_ in
                  let bit:u16 = coefficient_value %! 2us in
                  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                    Alloc.Vec.impl_1__push re_bits (cast (bit <: u16) <: u8)
                  in
                  let coefficient_value:u16 = (coefficient_value -! bit <: u16) /! 2us in
                  coefficient_value, re_bits <: (u16 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
          in
          re_bits)
  in
  bits_to_bytes re_bits

let bytes_to_bits (bytes: t_Slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new in
  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__iter bytes

            <:
            Core.Slice.Iter.t_Iter u8)
        <:
        Core.Slice.Iter.t_Iter u8)
      bits
      (fun bits byte ->
          let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = bits in
          let byte:u8 = byte in
          let byte_value:u8 = byte in
          let bits, byte_value:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & u8) =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = 0ul;
                      Core.Ops.Range.f_end = Core.Num.impl__u8__BITS
                    }
                    <:
                    Core.Ops.Range.t_Range u32)
                <:
                Core.Ops.Range.t_Range u32)
              (bits, byte_value <: (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & u8))
              (fun temp_0_ temp_1_ ->
                  let bits, byte_value:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & u8) = temp_0_ in
                  let _:u32 = temp_1_ in
                  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                    Alloc.Vec.impl_1__push bits (byte_value %! 2uy <: u8)
                  in
                  let byte_value:u8 = byte_value /! 2uy in
                  bits, byte_value <: (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & u8))
          in
          bits)
  in
  bits

let field_element_from_bits (bits: t_Slice u8) : Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  let _:Prims.unit =
    if
      ~.((Core.Slice.impl__len bits <: usize) <=. Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT
        <:
        bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits.len() <= BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let modulus:u16 =
    Core.Num.impl__u16__pow 2us (Hacspec_lib.f_as_u32 (Core.Slice.impl__len bits <: usize) <: u32)
  in
  let (value: u16):u16 = 0us in
  let value:u16 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Iter.Traits.Collect.f_into_iter bits <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
      value
      (fun value temp_1_ ->
          let value:u16 = value in
          let i, bit:(usize & u8) = temp_1_ in
          value +! (((cast (bit <: u8) <: u16) *! (1us <<! i <: u16) <: u16) %! modulus <: u16)
          <:
          u16)
  in
  Core.Convert.f_into value

let byte_decode (bits_per_coefficient: usize) (re_bytes: t_Slice u8)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  let _:Prims.unit =
    if ~.(bits_per_coefficient <=. Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits_per_coefficient <= BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let _:Prims.unit =
    match Core.Slice.impl__len re_bytes, sz 32 *! bits_per_coefficient <: (usize & usize) with
    | left_val, right_val ->
      if ~.(left_val =. right_val <: bool)
      then
        let kind:Core.Panicking.t_AssertKind =
          Core.Panicking.AssertKind_Eq <: Core.Panicking.t_AssertKind
        in
        Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
              left_val
              right_val
              (Core.Option.Option_None <: Core.Option.t_Option Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
  in
  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = bytes_to_bits re_bytes in
  let re_bit_chunks:Core.Slice.Iter.t_Chunks u8 =
    Core.Slice.impl__chunks (Core.Ops.Deref.f_deref re_bits <: t_Slice u8) bits_per_coefficient
  in
  let re:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    Hacspec_lib.Ring.impl_2__ZERO
  in
  let re, re_bit_chunks:(Hacspec_lib.Ring.t_PolynomialRingElement
      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
    Core.Slice.Iter.t_Chunks u8) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_lib.Ring.impl_2__len (sz 256) re <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (re, re_bit_chunks
        <:
        (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256) &
          Core.Slice.Iter.t_Chunks u8))
      (fun temp_0_ i ->
          let re, re_bit_chunks:(Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
            Core.Slice.Iter.t_Chunks u8) =
            temp_0_
          in
          let i:usize = i in
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option (t_Slice u8)) =
            Core.Iter.Traits.Iterator.f_next re_bit_chunks
          in
          let re_bit_chunks:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist5:Core.Option.t_Option (t_Slice u8) = out in
          let hoist6:t_Slice u8 = Core.Option.impl__unwrap hoist5 in
          let hoist7:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
            field_element_from_bits hoist6
          in
          let hoist8:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re i hoist7
          in
          hoist8, re_bit_chunks
          <:
          (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256) &
            Core.Slice.Iter.t_Chunks u8))
  in
  re

let vector_encode_12_
      (vector:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
        )
    : t_Array u8 (sz 1152) =
  let out:t_Array u8 (sz 1152) = Rust_primitives.Hax.repeat 0uy (sz 1152) in
  let out:t_Array u8 (sz 1152) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Hacspec_lib.Vector.impl__into_iter (sz 3) (sz 256) vector
                <:
                Core.Array.Iter.t_IntoIter
                  (Hacspec_lib.Ring.t_PolynomialRingElement
                      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3)))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Array.Iter.t_IntoIter
            (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                (sz 256)) (sz 3)))
      out
      (fun out temp_1_ ->
          let out:t_Array u8 (sz 1152) = out in
          let i, re:(usize &
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256)) =
            temp_1_
          in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
            ({
                Core.Ops.Range.f_start
                =
                i *! Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.f_end
                =
                (i +! sz 1 <: usize) *! Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
            (Core.Slice.impl__copy_from_slice (out.[ {
                      Core.Ops.Range.f_start
                      =
                      i *! Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                      <:
                      usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                (Core.Ops.Deref.f_deref (byte_encode (sz 12) re
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
          <:
          t_Array u8 (sz 1152))
  in
  out

let vector_decode_12_ (encoded: t_Array u8 (sz 1152))
    : Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
  let out:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
  =
    Hacspec_lib.Vector.impl__ZERO
  in
  let out:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
  =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks (Rust_primitives.unsize encoded <: t_Slice u8)
                  Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
      out
      (fun out temp_1_ ->
          let out:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256)
            (sz 3) =
            out
          in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (byte_decode (sz 12) bytes
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
      )
  in
  out
