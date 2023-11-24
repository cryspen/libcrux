module Libcrux.Kem.Kyber.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let is_non_zero (value: u8) : u8 =
  let value:u16 = cast (value <: u8) <: u16 in
  let result:u16 =
    ((value |. (Core.Num.impl__u16__wrapping_add (~.value <: u16) 1us <: u16) <: u16) >>! 8l <: u16) &.
    1us
  in
  cast (result <: u16) <: u8

inline_for_extraction
let compare_ciphertexts_in_constant_time (v_CIPHERTEXT_SIZE: usize) (lhs rhs: t_Slice u8)
    : FStar.HyperStack.ST.StackInline u8 (fun _ -> True) (fun _ _ _ -> True) =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let (r: u8):u8 = 0uy in
  let r:u8 =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for i in (0)..(CIPHERTEXT_SIZE) {\n            |r| {\n                core::ops::bit::BitOr::bitor(\n                    r,\n                    core::ops::bit::BitXor::bitxor(\n                        core::ops::index::Index::index(lhs, i),\n                        core::ops::index::Index::index(rhs, i),\n                    ),\n                )\n            }\n        })(r)\n    }"

  in
  is_non_zero r

let select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8)
    : FStar.HyperStack.ST.St (t_Array u8 (sz 32)) =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let mask:u8 = Core.Num.impl__u8__wrapping_sub (is_non_zero selector <: u8) 1uy in
  let out:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
      (fun i ->
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
            i
            ((out.[ i ] <: u8) |.
              (((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
                <:
                u8)
              <:
              u8)
          <:
          Prims.unit)
  in
  out
