module Libcrux.Digest
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let sha3_256_ (payload: t_Slice u8) = Libcrux.Hacl.Sha3.sha256 payload

let sha3_512_ (payload: t_Slice u8) = Libcrux.Hacl.Sha3.sha512 payload

let shake128 (v_LEN: usize) (data: t_Slice u8) = Libcrux.Hacl.Sha3.shake128 v_LEN data

let shake256 (v_LEN: usize) (data: t_Slice u8) = Libcrux.Hacl.Sha3.shake256 v_LEN data

let shake128x4_portable (v_LEN: usize) (data0 data1 data2 data3: t_Slice u8) =
  let input_len:usize = Core.Slice.impl__len data0 in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((input_len =. (Core.Slice.impl__len data1 <: usize) <: bool) &&
            (input_len =. (Core.Slice.impl__len data2 <: usize) <: bool) &&
            (input_len =. (Core.Slice.impl__len data3 <: usize) <: bool) &&
            (input_len <=. (cast (Core.Num.impl__u32__MAX <: u32) <: usize) <: bool) &&
            (v_LEN <=. (cast (Core.Num.impl__u32__MAX <: u32) <: usize) <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: input_len == data1.len() && input_len == data2.len() &&\\n            input_len == data3.len() && input_len <= u32::MAX as usize &&\\n    LEN <= u32::MAX as usize"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let digest0:t_Array u8 v_LEN = Libcrux.Hacl.Sha3.shake128 v_LEN data0 in
  let digest1:t_Array u8 v_LEN = Libcrux.Hacl.Sha3.shake128 v_LEN data1 in
  let digest2:t_Array u8 v_LEN = Libcrux.Hacl.Sha3.shake128 v_LEN data2 in
  let digest3:t_Array u8 v_LEN = Libcrux.Hacl.Sha3.shake128 v_LEN data3 in
  digest0, digest1, digest2, digest3
  <:
  (t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN & t_Array u8 v_LEN)

let shake128x4_256_ (v_LEN: usize) (data0 data1 data2 data3: t_Slice u8) =
  shake128x4_portable v_LEN data0 data1 data2 data3

let shake128x4 (v_LEN: usize) (data0 data1 data2 data3: t_Slice u8) =
  if Libcrux_platform.Platform.simd256_support ()
  then shake128x4_256_ v_LEN data0 data1 data2 data3
  else shake128x4_portable v_LEN data0 data1 data2 data3
