module Libcrux_sha3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let t_Algorithm_cast_to_repr (x: t_Algorithm) =
  match x with
  | Algorithm_Sha224  -> discriminant_Algorithm_Sha224
  | Algorithm_Sha256  -> discriminant_Algorithm_Sha256
  | Algorithm_Sha384  -> discriminant_Algorithm_Sha384
  | Algorithm_Sha512  -> discriminant_Algorithm_Sha512

let digest_size (mode: t_Algorithm) =
  match mode with
  | Algorithm_Sha224  -> sz 28
  | Algorithm_Sha256  -> sz 32
  | Algorithm_Sha384  -> sz 48
  | Algorithm_Sha512  -> sz 64

let hash (v_LEN: usize) (algorithm: t_Algorithm) (payload: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core.Num.impl__u32__MAX <: u32) <: usize)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: payload.len() <= u32::MAX as usize"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let out:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
  let out:t_Array u8 v_LEN =
    match algorithm with
    | Algorithm_Sha224  -> Libcrux_sha3.Portable.sha224 out payload
    | Algorithm_Sha256  -> Libcrux_sha3.Portable.sha256 out payload
    | Algorithm_Sha384  -> Libcrux_sha3.Portable.sha384 out payload
    | Algorithm_Sha512  -> Libcrux_sha3.Portable.sha512 out payload
  in
  out

let sha224_ema (digest payload: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core.Num.impl__u32__MAX <: u32) <: usize)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: payload.len() <= u32::MAX as usize"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((Core.Slice.impl__len #u8 digest <: usize) =. sz 28 <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: digest.len() == 28"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let hax_temp_output, digest:(Prims.unit & t_Slice u8) =
    (), Libcrux_sha3.Portable.sha224 digest payload <: (Prims.unit & t_Slice u8)
  in
  digest

let sha224 (data: t_Slice u8) =
  let out:t_Array u8 (sz 28) = Rust_primitives.Hax.repeat 0uy (sz 28) in
  let out:t_Array u8 (sz 28) = sha224_ema out data in
  out

let sha256_ema (digest payload: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core.Num.impl__u32__MAX <: u32) <: usize)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: payload.len() <= u32::MAX as usize"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((Core.Slice.impl__len #u8 digest <: usize) =. sz 32 <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: digest.len() == 32"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let hax_temp_output, digest:(Prims.unit & t_Slice u8) =
    (), Libcrux_sha3.Portable.sha256 digest payload <: (Prims.unit & t_Slice u8)
  in
  digest

let sha256 (data: t_Slice u8) =
  let out:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let out:t_Array u8 (sz 32) = sha256_ema out data in
  out

let sha384_ema (digest payload: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core.Num.impl__u32__MAX <: u32) <: usize)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: payload.len() <= u32::MAX as usize"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((Core.Slice.impl__len #u8 digest <: usize) =. sz 48 <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: digest.len() == 48"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let hax_temp_output, digest:(Prims.unit & t_Slice u8) =
    (), Libcrux_sha3.Portable.sha384 digest payload <: (Prims.unit & t_Slice u8)
  in
  digest

let sha384 (data: t_Slice u8) =
  let out:t_Array u8 (sz 48) = Rust_primitives.Hax.repeat 0uy (sz 48) in
  let out:t_Array u8 (sz 48) = sha384_ema out data in
  out

let sha512_ema (digest payload: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((Core.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core.Num.impl__u32__MAX <: u32) <: usize)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: payload.len() <= u32::MAX as usize"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((Core.Slice.impl__len #u8 digest <: usize) =. sz 64 <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: digest.len() == 64"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let hax_temp_output, digest:(Prims.unit & t_Slice u8) =
    (), Libcrux_sha3.Portable.sha512 digest payload <: (Prims.unit & t_Slice u8)
  in
  digest

let sha512 (data: t_Slice u8) =
  let out:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
  let out:t_Array u8 (sz 64) = sha512_ema out data in
  out

let shake128 (v_BYTES: usize) (data: t_Slice u8) =
  let out:t_Array u8 v_BYTES = Rust_primitives.Hax.repeat 0uy v_BYTES in
  let out:t_Array u8 v_BYTES = Libcrux_sha3.Portable.shake128 v_BYTES out data in
  out

let shake256 (v_BYTES: usize) (data: t_Slice u8) =
  let out:t_Array u8 v_BYTES = Rust_primitives.Hax.repeat 0uy v_BYTES in
  let out:t_Array u8 v_BYTES = Libcrux_sha3.Portable.shake256 v_BYTES out data in
  out
