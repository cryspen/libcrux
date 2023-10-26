module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let compress_then_serialize_message (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : t_Array u8 (sz 32) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let serialized:t_Array u8 (sz 32) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized (i, coefficients) ->
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                    (Core.Slice.impl__iter coefficients <: Core.Slice.Iter.t_Iter i32)
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
              <:
              Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
            serialized
            (fun serialized (j, coefficient) ->
                let coefficient:u16 =
                  Libcrux.Kem.Kyber.Conversions.to_unsigned_representative coefficient
                in
                let coefficient_compressed:i32 =
                  Libcrux.Kem.Kyber.Compress.compress_q coefficient
                in
                let _:Prims.unit =
                  if true
                  then
                    let _:Prims.unit =
                      if
                        ~.((coefficient_compressed =. 0l <: bool) ||
                          (coefficient_compressed =. 1l <: bool))
                      then
                        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: coefficient_compressed == 0 || coefficient_compressed == 1"

                            <:
                            Rust_primitives.Hax.t_Never)
                    in
                    ()
                in
                Rust_primitives.Hax.update_at serialized
                  i
                  ((serialized.[ i ] <: u8) |. ((cast coefficient_compressed <: u8) <<! j <: u8)
                    <:
                    u8))
          <:
          t_Array u8 (sz 32))
  in
  serialized

let deserialize_then_decompress_message (serialized: t_Array u8 (sz 32))
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter (Rust_primitives.unsize serialized <: t_Slice u8)
                <:
                Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
      re
      (fun re (i, byte) ->
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = sz 8
                  })
              <:
              Core.Ops.Range.t_Range usize)
            re
            (fun re j ->
                let coefficient_compressed:i32 = cast ((byte >>! j <: u8) &. 1uy) <: i32 in
                let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                  {
                    re with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      ((sz 8 *! i <: usize) +! j <: usize)
                      (Libcrux.Kem.Kyber.Compress.decompress_q coefficient_compressed <: i32)
                  }
                in
                re)
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  re

let serialize_little_endian_4_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:u8 = cast chunk.[ sz 0 ] <: u8 in
          let coefficient2:u8 = cast chunk.[ sz 1 ] <: u8 in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              i
              ((coefficient2 <<! 4l <: u8) |. coefficient1 <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_4_ (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 4 <: usize) /! sz 8
        with
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
      ()
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
      re
      (fun re (i, byte) ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                (cast (byte &. 15uy <: u8) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                (cast ((byte >>! 4l <: u8) &. 15uy <: u8) <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_5_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized (i, coefficients) ->
          let coefficient1:u8 = cast coefficients.[ sz 0 ] <: u8 in
          let coefficient2:u8 = cast coefficients.[ sz 1 ] <: u8 in
          let coefficient3:u8 = cast coefficients.[ sz 2 ] <: u8 in
          let coefficient4:u8 = cast coefficients.[ sz 3 ] <: u8 in
          let coefficient5:u8 = cast coefficients.[ sz 4 ] <: u8 in
          let coefficient6:u8 = cast coefficients.[ sz 5 ] <: u8 in
          let coefficient7:u8 = cast coefficients.[ sz 6 ] <: u8 in
          let coefficient8:u8 = cast coefficients.[ sz 7 ] <: u8 in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              (sz 5 *! i <: usize)
              (((coefficient2 &. 7uy <: u8) <<! 5l <: u8) |. coefficient1 <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              ((((coefficient4 &. 1uy <: u8) <<! 7l <: u8) |. (coefficient3 <<! 2l <: u8) <: u8) |.
                (coefficient2 >>! 3l <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (((coefficient5 &. 15uy <: u8) <<! 4l <: u8) |. (coefficient4 >>! 1l <: u8) <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              ((((coefficient7 &. 3uy <: u8) <<! 6l <: u8) |. (coefficient6 <<! 1l <: u8) <: u8) |.
                (coefficient5 >>! 4l <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              ((coefficient8 <<! 3l <: u8) |. (coefficient7 >>! 2l <: u8) <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_5_ (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 5 <: usize) /! sz 8
        with
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
      ()
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 5) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ sz 0 ] <: i32 in
          let byte2:i32 = cast bytes.[ sz 1 ] <: i32 in
          let byte3:i32 = cast bytes.[ sz 2 ] <: i32 in
          let byte4:i32 = cast bytes.[ sz 3 ] <: i32 in
          let byte5:i32 = cast bytes.[ sz 4 ] <: i32 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 8 *! i <: usize)
                (byte1 &. 31l <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 1 <: usize)
                (((byte2 &. 3l <: i32) <<! 3l <: i32) |. (byte1 >>! 5l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 2 <: usize)
                ((byte2 >>! 2l <: i32) &. 31l <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 3 <: usize)
                (((byte3 &. 15l <: i32) <<! 1l <: i32) |. (byte2 >>! 7l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 4 <: usize)
                (((byte4 &. 1l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 5 <: usize)
                ((byte4 >>! 1l <: i32) &. 31l <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 6 <: usize)
                (((byte5 &. 7l <: i32) <<! 2l <: i32) |. (byte4 >>! 6l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 7 <: usize)
                (byte5 >>! 3l <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_10_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 4)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:i32 = chunk.[ sz 0 ] in
          let coefficient2:i32 = chunk.[ sz 1 ] in
          let coefficient3:i32 = chunk.[ sz 2 ] in
          let coefficient4:i32 = chunk.[ sz 3 ] in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              (sz 5 *! i <: usize)
              (cast (coefficient1 &. 255l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              (((cast (coefficient2 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
                (cast ((coefficient1 >>! 8l <: i32) &. 3l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (((cast (coefficient3 &. 15l <: i32) <: u8) <<! 4l <: u8) |.
                (cast ((coefficient2 >>! 6l <: i32) &. 15l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              (((cast (coefficient4 &. 3l <: i32) <: u8) <<! 6l <: u8) |.
                (cast ((coefficient3 >>! 4l <: i32) &. 63l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              (cast ((coefficient4 >>! 2l <: i32) &. 255l <: i32) <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_10_ (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 10 <: usize) /! sz 8
        with
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
      ()
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 5) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ sz 0 ] <: i32 in
          let byte2:i32 = cast bytes.[ sz 1 ] <: i32 in
          let byte3:i32 = cast bytes.[ sz 2 ] <: i32 in
          let byte4:i32 = cast bytes.[ sz 3 ] <: i32 in
          let byte5:i32 = cast bytes.[ sz 4 ] <: i32 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 4 *! i <: usize)
                (((byte2 &. 3l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                (((byte3 &. 15l <: i32) <<! 6l <: i32) |. (byte2 >>! 2l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                (((byte4 &. 63l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                ((byte5 <<! 2l <: i32) |. (byte4 >>! 6l <: i32) <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_11_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized (i, coefficients) ->
          let coefficient1:i32 = coefficients.[ sz 0 ] in
          let coefficient2:i32 = coefficients.[ sz 1 ] in
          let coefficient3:i32 = coefficients.[ sz 2 ] in
          let coefficient4:i32 = coefficients.[ sz 3 ] in
          let coefficient5:i32 = coefficients.[ sz 4 ] in
          let coefficient6:i32 = coefficients.[ sz 5 ] in
          let coefficient7:i32 = coefficients.[ sz 6 ] in
          let coefficient8:i32 = coefficients.[ sz 7 ] in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized (sz 11 *! i <: usize) (cast coefficient1 <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 1 <: usize)
              (((cast (coefficient2 &. 31l <: i32) <: u8) <<! 3l <: u8) |.
                (cast (coefficient1 >>! 8l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 2 <: usize)
              (((cast (coefficient3 &. 3l <: i32) <: u8) <<! 6l <: u8) |.
                (cast (coefficient2 >>! 5l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 3 <: usize)
              (cast ((coefficient3 >>! 2l <: i32) &. 255l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 4 <: usize)
              (((cast (coefficient4 &. 127l <: i32) <: u8) <<! 1l <: u8) |.
                (cast (coefficient3 >>! 10l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 5 <: usize)
              (((cast (coefficient5 &. 15l <: i32) <: u8) <<! 4l <: u8) |.
                (cast (coefficient4 >>! 7l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 6 <: usize)
              (((cast (coefficient6 &. 1l <: i32) <: u8) <<! 7l <: u8) |.
                (cast (coefficient5 >>! 4l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 7 <: usize)
              (cast ((coefficient6 >>! 1l <: i32) &. 255l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 8 <: usize)
              (((cast (coefficient7 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
                (cast (coefficient6 >>! 9l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 9 <: usize)
              (((cast (coefficient8 &. 7l <: i32) <: u8) <<! 5l <: u8) |.
                (cast (coefficient7 >>! 6l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 11 *! i <: usize) +! sz 10 <: usize)
              (cast (coefficient8 >>! 3l <: i32) <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_11_ (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 11 <: usize) /! sz 8
        with
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
      ()
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 11) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ sz 0 ] <: i32 in
          let byte2:i32 = cast bytes.[ sz 1 ] <: i32 in
          let byte3:i32 = cast bytes.[ sz 2 ] <: i32 in
          let byte4:i32 = cast bytes.[ sz 3 ] <: i32 in
          let byte5:i32 = cast bytes.[ sz 4 ] <: i32 in
          let byte6:i32 = cast bytes.[ sz 5 ] <: i32 in
          let byte7:i32 = cast bytes.[ sz 6 ] <: i32 in
          let byte8:i32 = cast bytes.[ sz 7 ] <: i32 in
          let byte9:i32 = cast bytes.[ sz 8 ] <: i32 in
          let byte10:i32 = cast bytes.[ sz 9 ] <: i32 in
          let byte11:i32 = cast bytes.[ sz 10 ] <: i32 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 8 *! i <: usize)
                (((byte2 &. 7l <: i32) <<! 8l <: i32) |. byte1 <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 1 <: usize)
                (((byte3 &. 63l <: i32) <<! 5l <: i32) |. (byte2 >>! 3l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 2 <: usize)
                ((((byte5 &. 1l <: i32) <<! 10l <: i32) |. (byte4 <<! 2l <: i32) <: i32) |.
                  (byte3 >>! 6l <: i32)
                  <:
                  i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 3 <: usize)
                (((byte6 &. 15l <: i32) <<! 7l <: i32) |. (byte5 >>! 1l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 4 <: usize)
                (((byte7 &. 127l <: i32) <<! 4l <: i32) |. (byte6 >>! 4l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 5 <: usize)
                ((((byte9 &. 3l <: i32) <<! 9l <: i32) |. (byte8 <<! 1l <: i32) <: i32) |.
                  (byte7 >>! 7l <: i32)
                  <:
                  i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 6 <: usize)
                (((byte10 &. 31l <: i32) <<! 6l <: i32) |. (byte9 >>! 2l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 7 <: usize)
                ((byte11 <<! 3l <: i32) |. (byte10 >>! 5l <: i32) <: i32)
            }
          in
          re)
  in
  re

let serialize_uncompressed_ring_element
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : t_Array u8 (sz 384) =
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (coefficient >=.
                (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)
                <:
                bool) &&
              (coefficient <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: bool))
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        coefficient >= -FIELD_MODULUS && coefficient < FIELD_MODULUS)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let serialized:t_Array u8 (sz 384) = Rust_primitives.Hax.repeat 0uy (sz 384) in
  let serialized:t_Array u8 (sz 384) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized (i, chunks) ->
          let coefficient1:u16 =
            Libcrux.Kem.Kyber.Conversions.to_unsigned_representative (chunks.[ sz 0 ] <: i32)
          in
          let coefficient2:u16 =
            Libcrux.Kem.Kyber.Conversions.to_unsigned_representative (chunks.[ sz 1 ] <: i32)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.update_at serialized
              (sz 3 *! i <: usize)
              (cast (coefficient1 &. 255us <: u16) <: u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.update_at serialized
              ((sz 3 *! i <: usize) +! sz 1 <: usize)
              (cast ((coefficient1 >>! 8l <: u16) |. ((coefficient2 &. 15us <: u16) <<! 4l <: u16)
                    <:
                    u16)
                <:
                u8)
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.update_at serialized
              ((sz 3 *! i <: usize) +! sz 2 <: usize)
              (cast ((coefficient2 >>! 4l <: u16) &. 255us <: u16) <: u8)
          in
          serialized)
  in
  serialized

let deserialize_to_uncompressed_ring_element (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len serialized, Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
        with
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
      ()
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 3) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ sz 0 ] <: i32 in
          let byte2:i32 = cast bytes.[ sz 1 ] <: i32 in
          let byte3:i32 = cast bytes.[ sz 2 ] <: i32 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                (((byte2 &. 15l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                ((byte3 <<! 4l <: i32) |. ((byte2 >>! 4l <: i32) &. 15l <: i32) <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian
      (#v_COMPRESSION_FACTOR #v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.(((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_COMPRESSION_FACTOR
                <:
                usize) /!
              sz 8
              <:
              usize) =.
            v_OUT_LEN
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                        (let list = [""; " != "] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                          Rust_primitives.Hax.array_of_list list)
                      <:
                      t_Slice string)
                    (Rust_primitives.unsize (let list =
                            [
                              Core.Fmt.Rt.impl_1__new_display ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
                                    v_COMPRESSION_FACTOR
                                    <:
                                    usize) /!
                                  sz 8
                                  <:
                                  usize)
                              <:
                              Core.Fmt.Rt.t_Argument;
                              Core.Fmt.Rt.impl_1__new_display v_OUT_LEN <: Core.Fmt.Rt.t_Argument
                            ]
                          in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                          Rust_primitives.Hax.array_of_list list)
                      <:
                      t_Slice Core.Fmt.Rt.t_Argument)
                  <:
                  Core.Fmt.t_Arguments)
              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  match cast v_COMPRESSION_FACTOR <: u32 with
  | 4ul -> serialize_little_endian_4_ re
  | 5ul -> serialize_little_endian_5_ re
  | 10ul -> serialize_little_endian_10_ re
  | 11ul -> serialize_little_endian_11_ re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: factor "] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice string)
              (Rust_primitives.unsize (let list =
                      [
                        Core.Fmt.Rt.impl_1__new_display v_COMPRESSION_FACTOR
                        <:
                        Core.Fmt.Rt.t_Argument
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
        <:
        Rust_primitives.Hax.t_Never)

let deserialize_little_endian (#v_COMPRESSION_FACTOR: usize) (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_COMPRESSION_FACTOR
            <:
            usize) /!
          sz 8
        with
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
      ()
  in
  match cast v_COMPRESSION_FACTOR <: u32 with
  | 4ul -> deserialize_little_endian_4_ serialized
  | 5ul -> deserialize_little_endian_5_ serialized
  | 10ul -> deserialize_little_endian_10_ serialized
  | 11ul -> deserialize_little_endian_11_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: factor "] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice string)
              (Rust_primitives.unsize (let list =
                      [
                        Core.Fmt.Rt.impl_1__new_display v_COMPRESSION_FACTOR
                        <:
                        Core.Fmt.Rt.t_Argument
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
        <:
        Rust_primitives.Hax.t_Never)