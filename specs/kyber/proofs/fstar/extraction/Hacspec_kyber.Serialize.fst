module Hacspec_kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let bits_to_bytes (bits: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let _:Prims.unit =
    if ~.(((Alloc.Vec.len_under_impl_1 bits <: usize) %. 8sz <: usize) =. 0sz <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits.len() % 8 == 0"
          <:
          Rust_primitives.Hax.t_Never)
  in
  let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks_under_impl
              (Core.Ops.Deref.Deref.deref bits <: slice u8)
              8sz
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        _)
      bytes
      (fun bytes bit_chunk ->
          let byte_value:u8 = 0uy in
          let byte_value:Prims.unit =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  (Core.Iter.Traits.Iterator.Iterator.enumerate (Core.Iter.Traits.Collect.IntoIterator.into_iter
                          bit_chunk
                        <:
                        _)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
                <:
                _)
              byte_value
              (fun byte_value (i, bit) ->
                  byte_value +. (bit *. (Core.Num.pow_under_impl_6 2uy (cast i) <: u8) <: _)
                  <:
                  Prims.unit)
          in
          let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.push_under_impl_1 bytes byte_value
          in
          bytes)
  in
  bytes

let bytes_to_bits (bytes: slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.iter_under_impl
              bytes
            <:
            Core.Slice.Iter.t_Iter u8)
        <:
        _)
      bits
      (fun bits byte ->
          let byte_value:u8 = byte in
          let bits, byte_value:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Prims.unit) =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = 0ul;
                      Core.Ops.Range.Range.f_end = Core.Num.v_BITS_under_impl_6
                    })
                <:
                _)
              (bits, byte_value)
              (fun (bits, byte_value) _ ->
                  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                    Alloc.Vec.push_under_impl_1 bits (byte_value %. 2uy <: u8)
                  in
                  let byte_value:Prims.unit = byte_value /. 2uy in
                  bits, byte_value)
          in
          bits)
  in
  bits

let byte_encode
      (bits_per_coefficient: usize)
      (re:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let _:Prims.unit =
    if ~.(bits_per_coefficient <=. Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits_per_coefficient <= BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Hacspec_lib.Ring.coefficients_under_impl_2
              re
            <:
            array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
        <:
        _)
      re_bits
      (fun re_bits coefficient ->
          let coefficient_value:u16 = coefficient.Hacspec_lib.Field.PrimeFieldElement.f_value in
          let coefficient_value, re_bits:(u16 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = 0sz;
                      Core.Ops.Range.Range.f_end = bits_per_coefficient
                    })
                <:
                _)
              (coefficient_value, re_bits)
              (fun (coefficient_value, re_bits) _ ->
                  let bit:u16 = coefficient_value %. 2us in
                  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                    Alloc.Vec.push_under_impl_1 re_bits (cast bit)
                  in
                  let coefficient_value:u16 = (coefficient_value -. bit <: u16) /. 2us in
                  coefficient_value, re_bits)
          in
          re_bits)
  in
  bits_to_bytes re_bits

let field_element_from_bits (bits: slice u8) : Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  let _:Prims.unit =
    if
      ~.((Core.Slice.len_under_impl bits <: usize) <=.
        Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT
        <:
        bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits.len() <= BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let modulus:u16 =
    Core.Num.pow_under_impl_7 2us
      (Hacspec_lib.PanickingIntegerCasts.as_u32 (Core.Slice.len_under_impl bits <: usize) <: u32)
  in
  let (value: u16):u16 = 0us in
  let value:Prims.unit =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Iter.Traits.Collect.IntoIterator.into_iter bits <: _)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        _)
      value
      (fun value (i, bit) ->
          value +. ((cast bit *. (1us >>. i <: u16) <: u16) %. modulus <: u16) <: Prims.unit)
  in
  Core.Convert.Into.into value

let byte_decode (bits_per_coefficient: usize) (re_bytes: slice u8)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
  let _:Prims.unit =
    if ~.(bits_per_coefficient <=. Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits_per_coefficient <= BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let _:Prims.unit =
    match Core.Slice.len_under_impl re_bytes, 32sz *. bits_per_coefficient with
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
    Core.Slice.chunks_under_impl (Core.Ops.Deref.Deref.deref re_bits <: slice u8)
      bits_per_coefficient
  in
  let re:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz =
    Hacspec_lib.Ring.v_ZERO_under_impl_2
  in
  let re, re_bit_chunks:(Hacspec_lib.Ring.t_PolynomialRingElement
      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz &
    Core.Slice.Iter.t_Chunks u8) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Ring.len_under_impl_2 re <: usize
            })
        <:
        _)
      (re, re_bit_chunks)
      (fun (re, re_bit_chunks) i ->
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option _) =
            Core.Iter.Traits.Iterator.Iterator.next re_bit_chunks
          in
          let re_bit_chunks:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist13:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option _) = out in
          let hoist14:slice u8 = Core.Option.unwrap_under_impl hoist13 in
          let hoist15:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
            field_element_from_bits hoist14
          in
          let hoist16:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
            Rust_primitives.Hax.update_at re i hoist15
          in
          hoist16, re_bit_chunks)
  in
  re

let vector_encode_12_
      (vector: Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
    : array u8 1152sz =
  let out:array u8 1152sz = Rust_primitives.Hax.repeat 0uy 1152sz in
  let out:array u8 1152sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Hacspec_lib.Vector.into_iter_under_impl vector
                <:
                Core.Array.Iter.t_IntoIter
                  (Hacspec_lib.Ring.t_PolynomialRingElement
                      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) 3sz)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) 3sz))
        <:
        _)
      out
      (fun out (i, re) ->
          Rust_primitives.Hax.update_at out
            ({
                Core.Ops.Range.Range.f_start
                =
                i *. Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.Range.f_end
                =
                (i +. 1sz <: usize) *. Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize
              })
            (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut out
                    ({
                        Core.Ops.Range.Range.f_start
                        =
                        i *. Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT <: usize;
                        Core.Ops.Range.Range.f_end
                        =
                        (i +. 1sz <: usize) *. Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                        <:
                        usize
                      })
                  <:
                  slice u8)
                (Core.Ops.Deref.Deref.deref (byte_encode 12sz re
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  slice u8)
              <:
              slice u8)
          <:
          array u8 1152sz)
  in
  out

let vector_decode_12_ (encoded: array u8 1152sz)
    : Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
  let out:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let out:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_under_impl (Rust_primitives.unsize encoded <: slice u8)
                  Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        _)
      out
      (fun out (i, bytes) ->
          Rust_primitives.Hax.update_at out
            i
            (byte_decode 12sz bytes
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
  in
  out