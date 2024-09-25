module Libcrux_ml_kem.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let inz (value: u8) =
  let value:u16 = cast (value <: u8) <: u16 in
  let result:u16 =
    ((value |. (Core.Num.impl__u16__wrapping_add (~.value <: u16) 1us <: u16) <: u16) >>! 8l <: u16) &.
    1us
  in
  cast (result <: u16) <: u8

let is_non_zero (value: u8) = Core.Hint.black_box #u8 (inz value <: u8)

let compare (lhs rhs: t_Slice u8) =
  let (r: u8):u8 = 0uy in
  let r:u8 =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #u8 lhs <: usize)
      (fun r temp_1_ ->
          let r:u8 = r in
          let _:usize = temp_1_ in
          true)
      r
      (fun r i ->
          let r:u8 = r in
          let i:usize = i in
          r |. ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) <: u8)
  in
  is_non_zero r

let compare_ciphertexts_in_constant_time (lhs rhs: t_Slice u8) =
  Core.Hint.black_box #u8 (compare lhs rhs <: u8)

let select_ct (lhs rhs: t_Slice u8) (selector: u8) =
  let mask:u8 = Core.Num.impl__u8__wrapping_sub (is_non_zero selector <: u8) 1uy in
  let out:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let out:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
      (fun out temp_1_ ->
          let out:t_Array u8 (sz 32) = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_Array u8 (sz 32) = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) <: u8)
          <:
          t_Array u8 (sz 32))
  in
  out

let select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8) =
  Core.Hint.black_box #(t_Array u8 (sz 32)) (select_ct lhs rhs selector <: t_Array u8 (sz 32))

let compare_ciphertexts_select_shared_secret_in_constant_time (lhs_c rhs_c lhs_s rhs_s: t_Slice u8) =
  let selector:u8 = compare_ciphertexts_in_constant_time lhs_c rhs_c in
  select_shared_secret_in_constant_time lhs_s rhs_s selector
