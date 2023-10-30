module Libcrux.Kem.Kyber.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let is_non_zero (value: u8) : u8 =
  let value:u16 = cast value <: u16 in
  let result:u16 =
    ((value |. (Core.Num.impl__u16__wrapping_add (~.value <: u16) 1us <: u16) <: u16) >>! 8l <: u16) &.
    1us
  in
  cast result <: u8

let compare_ciphertexts_in_constant_time (#v_CIPHERTEXT_SIZE: usize) (lhs rhs: t_Slice u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len lhs, Core.Slice.impl__len rhs with
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
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len lhs, v_CIPHERTEXT_SIZE with
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
  let (r: u8):u8 = 0uy in
  let r:u8 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_CIPHERTEXT_SIZE
            })
        <:
        Core.Ops.Range.t_Range usize)
      r
      (fun r i -> r |. ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) <: u8)
  in
  is_non_zero r

let select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8) : t_Array u8 (sz 32) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len lhs, Core.Slice.impl__len rhs with
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
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len lhs, Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE with
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
  let mask:u8 = Core.Num.impl__u8__wrapping_sub (is_non_zero selector <: u8) 1uy in
  let out:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let out:t_Array u8 (sz 32) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
            })
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          Rust_primitives.Hax.update_at out
            i
            ((out.[ i ] <: u8) |.
              (((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
                <:
                u8)
              <:
              u8)
          <:
          t_Array u8 (sz 32))
  in
  out