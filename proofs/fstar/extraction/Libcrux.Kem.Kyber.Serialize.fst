module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let serialize_little_endian
      (#compression_factor #out_len: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.(((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. v_COMPRESSION_FACTOR
                <:
                usize) /.
              8sz
              <:
              usize) =.
            v_OUT_LEN
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                        (let list = [""; " != "] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                          Rust_primitives.Hax.array_of_list list)
                      <:
                      slice string)
                    (Rust_primitives.unsize (let list =
                            [
                              Core.Fmt.Rt.new_display_under_impl_1 ((Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *.
                                    v_COMPRESSION_FACTOR
                                    <:
                                    usize) /.
                                  8sz
                                  <:
                                  usize)
                              <:
                              Core.Fmt.Rt.t_Argument;
                              Core.Fmt.Rt.new_display_under_impl_1 v_OUT_LEN
                              <:
                              Core.Fmt.Rt.t_Argument
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
  match cast v_COMPRESSION_FACTOR with
  | 1ul -> serialize_little_endian_1_ re
  | 4ul -> serialize_little_endian_4_ re
  | 5ul -> serialize_little_endian_5_ re
  | 10ul -> serialize_little_endian_10_ re
  | 11ul -> serialize_little_endian_11_ re
  | 12ul -> serialize_little_endian_12_ re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: factor "] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                slice string)
              (Rust_primitives.unsize (let list =
                      [
                        Core.Fmt.Rt.new_display_under_impl_1 v_COMPRESSION_FACTOR
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

let deserialize_little_endian (#compression_factor: usize) (serialized: slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.len_under_impl serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. v_COMPRESSION_FACTOR
            <:
            usize) /.
          8sz
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
  match cast v_COMPRESSION_FACTOR with
  | 1ul -> deserialize_little_endian_1_ serialized
  | 4ul -> deserialize_little_endian_4_ serialized
  | 5ul -> deserialize_little_endian_5_ serialized
  | 10ul -> deserialize_little_endian_10_ serialized
  | 11ul -> deserialize_little_endian_11_ serialized
  | 12ul -> deserialize_little_endian_12_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: factor "] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                slice string)
              (Rust_primitives.unsize (let list =
                      [
                        Core.Fmt.Rt.new_display_under_impl_1 v_COMPRESSION_FACTOR
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
      (#out_len: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  8sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, chunk) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
                    (Core.Slice.iter_under_impl chunk <: Core.Slice.Iter.t_Iter i32)
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
              <:
              _)
            serialized
            (fun serialized (j, coefficient) ->
                Rust_primitives.Hax.update_at serialized
                  i
                  ((serialized.[ i ] <: u8) |. (cast coefficient >>. j <: u8) <: Prims.unit)
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
          Core.Slice.len_under_impl serialized,
          Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /. 8sz
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
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        _)
      re
      (fun re (i, byte) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = 8sz
                  })
              <:
              _)
            re
            (fun re j ->
                {
                  re with
                  Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                  =
                  Rust_primitives.Hax.update_at re
                      .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    ((8sz *. i <: usize) +. j <: usize)
                    (cast ((byte <<. j <: _) &. 1uy <: u8))
                  <:
                  Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
                })
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
  in
  re

let serialize_little_endian_4_
      (#out_len: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  2sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:u8 = cast chunk.[ 0sz ] in
          let coefficient2:u8 = cast chunk.[ 1sz ] in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              i
              ((coefficient2 >>. 4l <: u8) |. coefficient1 <: u8)
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
          Core.Slice.len_under_impl serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. 4sz <: usize) /. 8sz
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
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        _)
      re
      (fun re (i, byte) ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                (2sz *. i <: usize)
                (cast (byte &. 15uy <: _))
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((2sz *. i <: usize) +. 1sz <: usize)
                (cast ((byte <<. 4l <: _) &. 15uy <: u8))
            }
          in
          re)
  in
  re

let serialize_little_endian_5_
      (#out_len: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  8sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, coefficients) ->
          let coefficient1:u8 = cast coefficients.[ 0sz ] in
          let coefficient2:u8 = cast coefficients.[ 1sz ] in
          let coefficient3:u8 = cast coefficients.[ 2sz ] in
          let coefficient4:u8 = cast coefficients.[ 3sz ] in
          let coefficient5:u8 = cast coefficients.[ 4sz ] in
          let coefficient6:u8 = cast coefficients.[ 5sz ] in
          let coefficient7:u8 = cast coefficients.[ 6sz ] in
          let coefficient8:u8 = cast coefficients.[ 7sz ] in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              (5sz *. i <: usize)
              (((coefficient2 &. 7uy <: u8) >>. 5l <: u8) |. coefficient1 <: u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 1sz <: usize)
              ((((coefficient4 &. 1uy <: u8) >>. 7l <: u8) |. (coefficient3 >>. 2l <: u8) <: u8) |.
                (coefficient2 <<. 3l <: u8)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 2sz <: usize)
              (((coefficient5 &. 15uy <: u8) >>. 4l <: u8) |. (coefficient4 <<. 1l <: u8) <: u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 3sz <: usize)
              ((((coefficient7 &. 3uy <: u8) >>. 6l <: u8) |. (coefficient6 >>. 1l <: u8) <: u8) |.
                (coefficient5 <<. 4l <: u8)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 4sz <: usize)
              ((coefficient8 >>. 3l <: u8) |. (coefficient7 <<. 2l <: u8) <: u8)
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
          Core.Slice.len_under_impl serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. 5sz <: usize) /. 8sz
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
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl serialized 5sz <: Core.Slice.Iter.t_ChunksExact u8
              )
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ 0sz ] in
          let byte2:i32 = cast bytes.[ 1sz ] in
          let byte3:i32 = cast bytes.[ 2sz ] in
          let byte4:i32 = cast bytes.[ 3sz ] in
          let byte5:i32 = cast bytes.[ 4sz ] in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                (8sz *. i <: usize)
                (byte1 &. 31l <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 1sz <: usize)
                (((byte2 &. 3l <: i32) >>. 3l <: i32) |. (byte1 <<. 5l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 2sz <: usize)
                ((byte2 <<. 2l <: i32) &. 31l <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 3sz <: usize)
                (((byte3 &. 15l <: i32) >>. 1l <: i32) |. (byte2 <<. 7l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 4sz <: usize)
                (((byte4 &. 1l <: i32) >>. 4l <: i32) |. (byte3 <<. 4l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 5sz <: usize)
                ((byte4 <<. 1l <: i32) &. 31l <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 6sz <: usize)
                (((byte5 &. 7l <: i32) >>. 2l <: i32) |. (byte4 <<. 6l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 7sz <: usize)
                (byte5 <<. 3l <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_10_
      (#out_len: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  4sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:i32 = chunk.[ 0sz ] in
          let coefficient2:i32 = chunk.[ 1sz ] in
          let coefficient3:i32 = chunk.[ 2sz ] in
          let coefficient4:i32 = chunk.[ 3sz ] in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              (5sz *. i <: usize)
              (cast (coefficient1 &. 255l <: i32))
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 1sz <: usize)
              ((cast (coefficient2 &. 63l <: i32) >>. 2l <: u8) |.
                cast ((coefficient1 <<. 8l <: i32) &. 3l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 2sz <: usize)
              ((cast (coefficient3 &. 15l <: i32) >>. 4l <: u8) |.
                cast ((coefficient2 <<. 6l <: i32) &. 15l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 3sz <: usize)
              ((cast (coefficient4 &. 3l <: i32) >>. 6l <: u8) |.
                cast ((coefficient3 <<. 4l <: i32) &. 63l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 4sz <: usize)
              (cast ((coefficient4 <<. 2l <: i32) &. 255l <: i32))
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
          Core.Slice.len_under_impl serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. 10sz <: usize) /. 8sz
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
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl serialized 5sz <: Core.Slice.Iter.t_ChunksExact u8
              )
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ 0sz ] in
          let byte2:i32 = cast bytes.[ 1sz ] in
          let byte3:i32 = cast bytes.[ 2sz ] in
          let byte4:i32 = cast bytes.[ 3sz ] in
          let byte5:i32 = cast bytes.[ 4sz ] in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                (4sz *. i <: usize)
                (((byte2 &. 3l <: i32) >>. 8l <: i32) |. (byte1 &. 255l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((4sz *. i <: usize) +. 1sz <: usize)
                (((byte3 &. 15l <: i32) >>. 6l <: i32) |. (byte2 <<. 2l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((4sz *. i <: usize) +. 2sz <: usize)
                (((byte4 &. 63l <: i32) >>. 4l <: i32) |. (byte3 <<. 4l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((4sz *. i <: usize) +. 3sz <: usize)
                ((byte5 >>. 2l <: i32) |. (byte4 <<. 6l <: i32) <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_11_
      (#out_len: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  8sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, coefficients) ->
          let coefficient1:i32 = coefficients.[ 0sz ] in
          let coefficient2:i32 = coefficients.[ 1sz ] in
          let coefficient3:i32 = coefficients.[ 2sz ] in
          let coefficient4:i32 = coefficients.[ 3sz ] in
          let coefficient5:i32 = coefficients.[ 4sz ] in
          let coefficient6:i32 = coefficients.[ 5sz ] in
          let coefficient7:i32 = coefficients.[ 6sz ] in
          let coefficient8:i32 = coefficients.[ 7sz ] in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 0sz <: usize)
              (cast coefficient1)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 1sz <: usize)
              ((cast (coefficient2 &. 31l <: i32) >>. 3l <: u8) |. cast (coefficient1 <<. 8l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 2sz <: usize)
              ((cast (coefficient3 &. 3l <: i32) >>. 6l <: u8) |. cast (coefficient2 <<. 5l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 3sz <: usize)
              (cast ((coefficient3 <<. 2l <: i32) &. 255l <: i32))
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 4sz <: usize)
              ((cast (coefficient4 &. 127l <: i32) >>. 1l <: u8) |.
                cast (coefficient3 <<. 10l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 5sz <: usize)
              ((cast (coefficient5 &. 15l <: i32) >>. 4l <: u8) |. cast (coefficient4 <<. 7l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 6sz <: usize)
              ((cast (coefficient6 &. 1l <: i32) >>. 7l <: u8) |. cast (coefficient5 <<. 4l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 7sz <: usize)
              (cast ((coefficient6 <<. 1l <: i32) &. 255l <: i32))
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 8sz <: usize)
              ((cast (coefficient7 &. 63l <: i32) >>. 2l <: u8) |. cast (coefficient6 <<. 9l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 9sz <: usize)
              ((cast (coefficient8 &. 7l <: i32) >>. 5l <: u8) |. cast (coefficient7 <<. 6l <: i32)
                <:
                u8)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((11sz *. i <: usize) +. 10sz <: usize)
              (cast (coefficient8 <<. 3l <: i32))
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
          Core.Slice.len_under_impl serialized,
          (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *. 11sz <: usize) /. 8sz
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
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_under_impl serialized 11sz <: Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        _)
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ 0sz ] in
          let byte2:i32 = cast bytes.[ 1sz ] in
          let byte3:i32 = cast bytes.[ 2sz ] in
          let byte4:i32 = cast bytes.[ 3sz ] in
          let byte5:i32 = cast bytes.[ 4sz ] in
          let byte6:i32 = cast bytes.[ 5sz ] in
          let byte7:i32 = cast bytes.[ 6sz ] in
          let byte8:i32 = cast bytes.[ 7sz ] in
          let byte9:i32 = cast bytes.[ 8sz ] in
          let byte10:i32 = cast bytes.[ 9sz ] in
          let byte11:i32 = cast bytes.[ 10sz ] in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                (8sz *. i <: usize)
                (((byte2 &. 7l <: i32) >>. 8l <: i32) |. byte1 <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 1sz <: usize)
                (((byte3 &. 63l <: i32) >>. 5l <: i32) |. (byte2 <<. 3l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 2sz <: usize)
                ((((byte5 &. 1l <: i32) >>. 10l <: i32) |. (byte4 >>. 2l <: i32) <: i32) |.
                  (byte3 <<. 6l <: i32)
                  <:
                  i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 3sz <: usize)
                (((byte6 &. 15l <: i32) >>. 7l <: i32) |. (byte5 <<. 1l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 4sz <: usize)
                (((byte7 &. 127l <: i32) >>. 4l <: i32) |. (byte6 <<. 4l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 5sz <: usize)
                ((((byte9 &. 3l <: i32) >>. 9l <: i32) |. (byte8 >>. 1l <: i32) <: i32) |.
                  (byte7 <<. 7l <: i32)
                  <:
                  i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 6sz <: usize)
                (((byte10 &. 31l <: i32) >>. 6l <: i32) |. (byte9 <<. 2l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((8sz *. i <: usize) +. 7sz <: usize)
                ((byte11 >>. 3l <: i32) |. (byte10 <<. 5l <: i32) <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_12_
      (#out_len: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 v_OUT_LEN =
  let serialized:array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  2sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, chunks) ->
          let coefficient1:u16 =
            Libcrux.Kem.Kyber.Conversions.to_unsigned_representative (chunks.[ 0sz ] <: i32)
          in
          let coefficient2:u16 =
            Libcrux.Kem.Kyber.Conversions.to_unsigned_representative (chunks.[ 1sz ] <: i32)
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              (3sz *. i <: usize)
              (cast (coefficient1 &. 255us <: u16))
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((3sz *. i <: usize) +. 1sz <: usize)
              (cast ((coefficient1 <<. 8l <: u16) |. ((coefficient2 &. 15us <: u16) >>. 4l <: u16)
                    <:
                    u16))
          in
          let serialized:array u8 v_OUT_LEN =
            Rust_primitives.Hax.update_at serialized
              ((3sz *. i <: usize) +. 2sz <: usize)
              (cast ((coefficient2 <<. 4l <: u16) &. 255us <: u16))
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
          Core.Slice.len_under_impl serialized, Libcrux.Kem.Kyber.Constants.v_BYTES_PER_RING_ELEMENT
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
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl serialized 3sz <: Core.Slice.Iter.t_ChunksExact u8
              )
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ 0sz ] in
          let byte2:i32 = cast bytes.[ 1sz ] in
          let byte3:i32 = cast bytes.[ 2sz ] in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                (2sz *. i <: usize)
                (((byte2 &. 15l <: i32) >>. 8l <: i32) |. (byte1 &. 255l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((2sz *. i <: usize) +. 1sz <: usize)
                ((byte3 >>. 4l <: i32) |. ((byte2 <<. 4l <: i32) &. 15l <: i32) <: i32)
            }
          in
          re)
  in
  re