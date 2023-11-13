module Libcrux.Kem.Kyber.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let is_non_zero (value: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          (~.(value =. 0uy <: bool) || result =. 0uy) &&
          (~.(value <>. 0uy <: bool) || result =. 1uy)) =
  let value:u16 = cast (value <: u8) <: u16 in
  let result:u16 =
    ((value |. (Core.Num.impl__u16__wrapping_add (~.value <: u16) 1us <: u16) <: u16) >>! 8l <: u16) &.
    1us
  in
  cast (result <: u16) <: u8

let compare_ciphertexts_in_constant_time (v_CIPHERTEXT_SIZE: usize) (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          (~.(lhs =. rhs <: bool) || result =. 0uy) && (~.(lhs <>. rhs <: bool) || result =. 1uy)) =
  let _:Prims.unit = () in
  let _:Prims.unit = () in
  let (r: u8):u8 = 0uy in
  let r:u8 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_CIPHERTEXT_SIZE
            })
        <:
        Core.Ops.Range.t_Range usize)
      r
      (fun r i ->
          let r:u8 = r in
          let i:usize = i in
          r |. ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) <: u8)
  in
  is_non_zero r

let select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8)
    : Prims.Pure (t_Array u8 (sz 32))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          (~.(selector =. 0uy <: bool) || result =. lhs) &&
          (~.(selector <>. 0uy <: bool) || result =. rhs)) =
  let _:Prims.unit = () in
  let _:Prims.unit = () in
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
          let out:t_Array u8 (sz 32) = out in
          let i:usize = i in
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