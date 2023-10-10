module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let serialize_little_endian
      (#v_COMPRESSION_FACTOR #v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
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
                      slice string)
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
                      slice Core.Fmt.Rt.t_Argument)
                  <:
                  Core.Fmt.t_Arguments)
              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  match cast v_COMPRESSION_FACTOR <: u32 with
  | 1ul -> serialize_little_endian_1_ re
  | 4ul -> serialize_little_endian_4_ re
  | 5ul -> serialize_little_endian_5_ re
  | 10ul -> serialize_little_endian_10_ re
  | 11ul -> serialize_little_endian_11_ re
  | 12ul -> serialize_little_endian_12_ re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: factor "] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                slice string)
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
                slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
        <:
        Rust_primitives.Hax.t_Never)

let deserialize_little_endian (#v_COMPRESSION_FACTOR: usize) (serialized: slice u8)
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
  | 1ul -> deserialize_little_endian_1_ serialized
  | 4ul -> deserialize_little_endian_4_ serialized
  | 5ul -> deserialize_little_endian_5_ serialized
  | 10ul -> deserialize_little_endian_10_ serialized
  | 11ul -> deserialize_little_endian_11_ serialized
  | 12ul -> deserialize_little_endian_12_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: factor "] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                slice string)
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
                slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
        <:
        Rust_primitives.Hax.t_Never)

let serialize_little_endian_1_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _.f_IntoIter)
      serialized
      (fun serialized (i, chunk) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                    (Core.Slice.impl__iter chunk <: Core.Slice.Iter.t_Iter i32)
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
              <:
              _.f_IntoIter)
            serialized
            (fun serialized (j, coefficient) ->
                Rust_primitives.Hax.update_at serialized
                  i
                  ((serialized.[ i ] <: u8) |. ((cast coefficient <: u8) <<! j <: u8) <: Prims.unit)
                <:
                array u8 v_OUT_LEN)
          <:
          array u8 v_OUT_LEN)
  in
  serialized

let deserialize_little_endian_1_ (serialized: slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.impl__len serialized,
          Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 8
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
    Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        _.f_IntoIter)
      re
      (fun re (i, byte) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = sz 8
                  })
              <:
              _.f_IntoIter)
            re
            (fun re j ->
                {
                  re with
                  Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                  =
                  Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    ((sz 8 *! i <: usize) +! j <: usize)
                    (cast ((byte >>! j <: (Core.Ops.Bit.t_impl_780).f_Output) &. 1uy <: u8) <: i32)
                  <:
                  Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                })
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  re

let serialize_little_endian_4_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _.f_IntoIter)
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:u8 = cast chunk.[ sz 0 ] <: u8 in
          let coefficient2:u8 = cast chunk.[ sz 1 ] <: u8 in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              i
              ((coefficient2 <<! 4l <: u8) |. coefficient1 <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_4_ (serialized: slice u8)
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
    Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        _.f_IntoIter)
      re
      (fun re (i, byte) ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                (cast (byte &. 15uy <: (Core.Ops.Bit.t_impl_46).f_Output) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                (cast ((byte >>! 4l <: (Core.Ops.Bit.t_impl_792).f_Output) &. 15uy <: u8) <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_5_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _.f_IntoIter)
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:u8 = cast chunk.[ sz 0 ] <: u8 in
          let coefficient2:u8 = cast chunk.[ sz 1 ] <: u8 in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              i
              ((coefficient2 <<! 4l <: u8) |. coefficient1 <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_5_ (serialized: slice u8)
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
    Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        _.f_IntoIter)
      re
      (fun re (i, byte) ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                (cast (byte &. 15uy <: (Core.Ops.Bit.t_impl_46).f_Output) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                (cast ((byte >>! 4l <: (Core.Ops.Bit.t_impl_792).f_Output) &. 15uy <: u8) <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_10_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    slice i32)
                  (sz 4)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _.f_IntoIter)
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:i32 = chunk.[ sz 0 ] in
          let coefficient2:i32 = chunk.[ sz 1 ] in
          let coefficient3:i32 = chunk.[ sz 2 ] in
          let coefficient4:i32 = chunk.[ sz 3 ] in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              (sz 5 *! i <: usize)
              (cast (coefficient1 &. 255l <: i32) <: u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              (((cast (coefficient2 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
                (cast ((coefficient1 >>! 8l <: i32) &. 3l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (((cast (coefficient3 &. 15l <: i32) <: u8) <<! 4l <: u8) |.
                (cast ((coefficient2 >>! 6l <: i32) &. 15l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              (((cast (coefficient4 &. 3l <: i32) <: u8) <<! 6l <: u8) |.
                (cast ((coefficient3 >>! 4l <: i32) &. 63l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              (cast ((coefficient4 >>! 2l <: i32) &. 255l <: i32) <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_10_ (serialized: slice u8)
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
    Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 5) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _.f_IntoIter)
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
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    slice i32)
                  (sz 4)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _.f_IntoIter)
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:i32 = chunk.[ sz 0 ] in
          let coefficient2:i32 = chunk.[ sz 1 ] in
          let coefficient3:i32 = chunk.[ sz 2 ] in
          let coefficient4:i32 = chunk.[ sz 3 ] in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              (sz 5 *! i <: usize)
              (cast (coefficient1 &. 255l <: i32) <: u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              (((cast (coefficient2 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
                (cast ((coefficient1 >>! 8l <: i32) &. 3l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (((cast (coefficient3 &. 15l <: i32) <: u8) <<! 4l <: u8) |.
                (cast ((coefficient2 >>! 6l <: i32) &. 15l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              (((cast (coefficient4 &. 3l <: i32) <: u8) <<! 6l <: u8) |.
                (cast ((coefficient3 >>! 4l <: i32) &. 63l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              (cast ((coefficient4 >>! 2l <: i32) &. 255l <: i32) <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_11_ (serialized: slice u8)
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
    Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks serialized (sz 5) <: Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        _.f_IntoIter)
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

let serialize_little_endian_12_
      (#v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _.f_IntoIter)
      serialized
      (fun serialized (i, chunks) ->
          let coefficient1:u16 =
            Libcrux.Kem.Kyber.Conversions.to_unsigned_representative (chunks.[ sz 0 ] <: i32)
          in
          let coefficient2:u16 =
            Libcrux.Kem.Kyber.Conversions.to_unsigned_representative (chunks.[ sz 1 ] <: i32)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              (sz 3 *! i <: usize)
              (cast (coefficient1 &. 255us <: u16) <: u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 3 *! i <: usize) +! sz 1 <: usize)
              (cast ((coefficient1 >>! 8l <: u16) |. ((coefficient2 &. 15us <: u16) <<! 4l <: u16)
                    <:
                    u16)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((sz 3 *! i <: usize) +! sz 2 <: usize)
              (cast ((coefficient2 >>! 4l <: u16) &. 255us <: u16) <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_12_ (serialized: slice u8)
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
    Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 3) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _.f_IntoIter)
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