module Hacspec_kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

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
          let byte_value:u8 = 0uy in
          let byte_value:u8 =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                      (Core.Iter.Traits.Collect.f_into_iter bit_chunk <: Core.Slice.Iter.t_Iter u8)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
                <:
                Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
              byte_value
              (fun byte_value (i, bit) ->
                  byte_value +! (bit *! (Core.Num.impl__u8__pow 2uy (cast i <: u32) <: u8) <: u8)
                  <:
                  u8)
          in
          let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push bytes byte_value
          in
          bytes)
  in
  bytes

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
          let byte_value:u8 = byte in
          let bits, byte_value:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & u8) =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = 0ul;
                      Core.Ops.Range.f_end = Core.Num.impl__u8__BITS
                    })
                <:
                Core.Ops.Range.t_Range u32)
              (bits, byte_value)
              (fun (bits, byte_value) _ ->
                  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                    Alloc.Vec.impl_1__push bits (byte_value %! 2uy <: u8)
                  in
                  let byte_value:u8 = byte_value /! 2uy in
                  bits, byte_value)
          in
          bits)
  in
  bits

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
              re
            <:
            t_Array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
        <:
        Core.Slice.Iter.t_Iter (Hacspec_lib.Field.t_PrimeFieldElement 3329us))
      re_bits
      (fun re_bits coefficient ->
          let coefficient_value:u16 = coefficient.Hacspec_lib.Field.f_value in
          let coefficient_value, re_bits:(u16 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = bits_per_coefficient
                    })
                <:
                Core.Ops.Range.t_Range usize)
              (coefficient_value, re_bits)
              (fun (coefficient_value, re_bits) _ ->
                  let bit:u16 = coefficient_value %! 2us in
                  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                    Alloc.Vec.impl_1__push re_bits (cast bit <: u8)
                  in
                  let coefficient_value:u16 = (coefficient_value -! bit <: u16) /! 2us in
                  coefficient_value, re_bits)
          in
          re_bits)
  in
  bits_to_bytes re_bits

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
      (fun value (i, bit) ->
          value +! (((cast bit <: u16) *! (1us <<! i <: u16) <: u16) %! modulus <: u16) <: u16)
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
    match Core.Slice.impl__len re_bytes, sz 32 *! bits_per_coefficient with
    | left_val, right_val ->
      if ~.(left_val =. right_val <: bool)
      then
        let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
        Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
              left_val
              right_val
              Core.Option.Option_None
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
              Core.Ops.Range.f_end = Hacspec_lib.Ring.impl_2__len re <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, re_bit_chunks)
      (fun (re, re_bit_chunks) i ->
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option (t_Slice u8)) =
            Core.Iter.Traits.Iterator.f_next re_bit_chunks
          in
          let re_bit_chunks:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist13:Core.Option.t_Option (t_Slice u8) = out in
          let hoist14:t_Slice u8 = Core.Option.impl__unwrap hoist13 in
          let hoist15:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
            field_element_from_bits hoist14
          in
          let hoist16:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            Rust_primitives.Hax.update_at re i hoist15
          in
          hoist16, re_bit_chunks)
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
              (Hacspec_lib.Vector.impl__into_iter vector
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
      (fun out (i, re) ->
          Rust_primitives.Hax.update_at out
            ({
                Core.Ops.Range.f_start
                =
                i *! Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.f_end
                =
                (i +! sz 1 <: usize) *! Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize
              })
            (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut out
                    ({
                        Core.Ops.Range.f_start
                        =
                        i *! Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! sz 1 <: usize) *! Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                        <:
                        usize
                      })
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
      (fun out (i, bytes) ->
          Rust_primitives.Hax.update_at out
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