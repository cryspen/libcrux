module Libcrux_secrets.Int
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let v_U8 (v: u8) : u8 = Libcrux_secrets.Int.Public_integers.secret #u8 v

let v_U16 (v: u16) : u16 = Libcrux_secrets.Int.Public_integers.secret #u16 v

let v_U32 (v: u32) : u32 = Libcrux_secrets.Int.Public_integers.secret #u32 v

let v_U64 (v: u64) : u64 = Libcrux_secrets.Int.Public_integers.secret #u64 v

let v_U128 (v: u128) : u128 = Libcrux_secrets.Int.Public_integers.secret #u128 v

let v_I8 (v: i8) : i8 = Libcrux_secrets.Int.Public_integers.secret #i8 v

let v_I16 (v: i16) : i16 = Libcrux_secrets.Int.Public_integers.secret #i16 v

let v_I32 (v: i32) : i32 = Libcrux_secrets.Int.Public_integers.secret #i32 v

let v_I64 (v: i64) : i64 = Libcrux_secrets.Int.Public_integers.secret #i64 v

let v_I128 (v: i128) : i128 = Libcrux_secrets.Int.Public_integers.secret #i128 v

class t_CastOps (v_Self: Type0) = {
  f_as_u8_pre:v_Self -> Type0;
  f_as_u8_post:v_Self -> u8 -> Type0;
  f_as_u8:x0: v_Self -> Prims.Pure u8 (f_as_u8_pre x0) (fun result -> f_as_u8_post x0 result);
  f_as_i8_pre:v_Self -> Type0;
  f_as_i8_post:v_Self -> i8 -> Type0;
  f_as_i8:x0: v_Self -> Prims.Pure i8 (f_as_i8_pre x0) (fun result -> f_as_i8_post x0 result);
  f_as_u16_pre:v_Self -> Type0;
  f_as_u16_post:v_Self -> u16 -> Type0;
  f_as_u16:x0: v_Self -> Prims.Pure u16 (f_as_u16_pre x0) (fun result -> f_as_u16_post x0 result);
  f_as_i16_pre:v_Self -> Type0;
  f_as_i16_post:v_Self -> i16 -> Type0;
  f_as_i16:x0: v_Self -> Prims.Pure i16 (f_as_i16_pre x0) (fun result -> f_as_i16_post x0 result);
  f_as_u32_pre:v_Self -> Type0;
  f_as_u32_post:v_Self -> u32 -> Type0;
  f_as_u32:x0: v_Self -> Prims.Pure u32 (f_as_u32_pre x0) (fun result -> f_as_u32_post x0 result);
  f_as_i32_pre:v_Self -> Type0;
  f_as_i32_post:v_Self -> i32 -> Type0;
  f_as_i32:x0: v_Self -> Prims.Pure i32 (f_as_i32_pre x0) (fun result -> f_as_i32_post x0 result);
  f_as_u64_pre:v_Self -> Type0;
  f_as_u64_post:v_Self -> u64 -> Type0;
  f_as_u64:x0: v_Self -> Prims.Pure u64 (f_as_u64_pre x0) (fun result -> f_as_u64_post x0 result);
  f_as_i64_pre:v_Self -> Type0;
  f_as_i64_post:v_Self -> i64 -> Type0;
  f_as_i64:x0: v_Self -> Prims.Pure i64 (f_as_i64_pre x0) (fun result -> f_as_i64_post x0 result);
  f_as_u128_pre:v_Self -> Type0;
  f_as_u128_post:v_Self -> u128 -> Type0;
  f_as_u128:x0: v_Self
    -> Prims.Pure u128 (f_as_u128_pre x0) (fun result -> f_as_u128_post x0 result);
  f_as_i128_pre:v_Self -> Type0;
  f_as_i128_post:v_Self -> i128 -> Type0;
  f_as_i128:x0: v_Self
    -> Prims.Pure i128 (f_as_i128_pre x0) (fun result -> f_as_i128_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_CastOps u8 =
  {
    f_as_u8_pre = (fun (self: u8) -> true);
    f_as_u8_post = (fun (self: u8) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8));
    f_as_i8_pre = (fun (self: u8) -> true);
    f_as_i8_post = (fun (self: u8) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8
              )
            <:
            i8));
    f_as_u16_pre = (fun (self: u8) -> true);
    f_as_u16_post = (fun (self: u8) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8
              )
            <:
            u16));
    f_as_i16_pre = (fun (self: u8) -> true);
    f_as_i16_post = (fun (self: u8) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8
              )
            <:
            i16));
    f_as_u32_pre = (fun (self: u8) -> true);
    f_as_u32_post = (fun (self: u8) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8
              )
            <:
            u32));
    f_as_i32_pre = (fun (self: u8) -> true);
    f_as_i32_post = (fun (self: u8) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8
              )
            <:
            i32));
    f_as_u64_pre = (fun (self: u8) -> true);
    f_as_u64_post = (fun (self: u8) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8
              )
            <:
            u64));
    f_as_i64_pre = (fun (self: u8) -> true);
    f_as_i64_post = (fun (self: u8) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8
              )
            <:
            i64));
    f_as_u128_pre = (fun (self: u8) -> true);
    f_as_u128_post = (fun (self: u8) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: u8) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8
              )
            <:
            u128));
    f_as_i128_pre = (fun (self: u8) -> true);
    f_as_i128_post = (fun (self: u8) (out: i128) -> true);
    f_as_i128
    =
    fun (self: u8) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #u8 #FStar.Tactics.Typeclasses.solve self <: u8)
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_u16: t_CastOps u16 =
  {
    f_as_u8_pre = (fun (self: u16) -> true);
    f_as_u8_post = (fun (self: u16) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self
                <:
                u16)
            <:
            u8));
    f_as_i8_pre = (fun (self: u16) -> true);
    f_as_i8_post = (fun (self: u16) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self
                <:
                u16)
            <:
            i8));
    f_as_u16_pre = (fun (self: u16) -> true);
    f_as_u16_post = (fun (self: u16) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self <: u16));
    f_as_i16_pre = (fun (self: u16) -> true);
    f_as_i16_post = (fun (self: u16) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self
                <:
                u16)
            <:
            i16));
    f_as_u32_pre = (fun (self: u16) -> true);
    f_as_u32_post = (fun (self: u16) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self
                <:
                u16)
            <:
            u32));
    f_as_i32_pre = (fun (self: u16) -> true);
    f_as_i32_post = (fun (self: u16) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self
                <:
                u16)
            <:
            i32));
    f_as_u64_pre = (fun (self: u16) -> true);
    f_as_u64_post = (fun (self: u16) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self
                <:
                u16)
            <:
            u64));
    f_as_i64_pre = (fun (self: u16) -> true);
    f_as_i64_post = (fun (self: u16) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self
                <:
                u16)
            <:
            i64));
    f_as_u128_pre = (fun (self: u16) -> true);
    f_as_u128_post = (fun (self: u16) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: u16) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self
                <:
                u16)
            <:
            u128));
    f_as_i128_pre = (fun (self: u16) -> true);
    f_as_i128_post = (fun (self: u16) (out: i128) -> true);
    f_as_i128
    =
    fun (self: u16) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #u16 #FStar.Tactics.Typeclasses.solve self <: u16
            )
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_u32: t_CastOps u32 =
  {
    f_as_u8_pre = (fun (self: u32) -> true);
    f_as_u8_post = (fun (self: u32) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self
                <:
                u32)
            <:
            u8));
    f_as_i8_pre = (fun (self: u32) -> true);
    f_as_i8_post = (fun (self: u32) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self
                <:
                u32)
            <:
            i8));
    f_as_u16_pre = (fun (self: u32) -> true);
    f_as_u16_post = (fun (self: u32) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self
                <:
                u32)
            <:
            u16));
    f_as_i16_pre = (fun (self: u32) -> true);
    f_as_i16_post = (fun (self: u32) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self
                <:
                u32)
            <:
            i16));
    f_as_u32_pre = (fun (self: u32) -> true);
    f_as_u32_post = (fun (self: u32) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self <: u32));
    f_as_i32_pre = (fun (self: u32) -> true);
    f_as_i32_post = (fun (self: u32) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self
                <:
                u32)
            <:
            i32));
    f_as_u64_pre = (fun (self: u32) -> true);
    f_as_u64_post = (fun (self: u32) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self
                <:
                u32)
            <:
            u64));
    f_as_i64_pre = (fun (self: u32) -> true);
    f_as_i64_post = (fun (self: u32) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self
                <:
                u32)
            <:
            i64));
    f_as_u128_pre = (fun (self: u32) -> true);
    f_as_u128_post = (fun (self: u32) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: u32) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self
                <:
                u32)
            <:
            u128));
    f_as_i128_pre = (fun (self: u32) -> true);
    f_as_i128_post = (fun (self: u32) (out: i128) -> true);
    f_as_i128
    =
    fun (self: u32) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #u32 #FStar.Tactics.Typeclasses.solve self <: u32
            )
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_u64: t_CastOps u64 =
  {
    f_as_u8_pre = (fun (self: u64) -> true);
    f_as_u8_post = (fun (self: u64) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self
                <:
                u64)
            <:
            u8));
    f_as_i8_pre = (fun (self: u64) -> true);
    f_as_i8_post = (fun (self: u64) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self
                <:
                u64)
            <:
            i8));
    f_as_u16_pre = (fun (self: u64) -> true);
    f_as_u16_post = (fun (self: u64) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self
                <:
                u64)
            <:
            u16));
    f_as_i16_pre = (fun (self: u64) -> true);
    f_as_i16_post = (fun (self: u64) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self
                <:
                u64)
            <:
            i16));
    f_as_u32_pre = (fun (self: u64) -> true);
    f_as_u32_post = (fun (self: u64) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self
                <:
                u64)
            <:
            u32));
    f_as_i32_pre = (fun (self: u64) -> true);
    f_as_i32_post = (fun (self: u64) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self
                <:
                u64)
            <:
            i32));
    f_as_u64_pre = (fun (self: u64) -> true);
    f_as_u64_post = (fun (self: u64) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self <: u64));
    f_as_i64_pre = (fun (self: u64) -> true);
    f_as_i64_post = (fun (self: u64) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self
                <:
                u64)
            <:
            i64));
    f_as_u128_pre = (fun (self: u64) -> true);
    f_as_u128_post = (fun (self: u64) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: u64) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self
                <:
                u64)
            <:
            u128));
    f_as_i128_pre = (fun (self: u64) -> true);
    f_as_i128_post = (fun (self: u64) (out: i128) -> true);
    f_as_i128
    =
    fun (self: u64) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #u64 #FStar.Tactics.Typeclasses.solve self <: u64
            )
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_u128: t_CastOps u128 =
  {
    f_as_u8_pre = (fun (self: u128) -> true);
    f_as_u8_post = (fun (self: u128) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
                <:
                u128)
            <:
            u8));
    f_as_i8_pre = (fun (self: u128) -> true);
    f_as_i8_post = (fun (self: u128) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
                <:
                u128)
            <:
            i8));
    f_as_u16_pre = (fun (self: u128) -> true);
    f_as_u16_post = (fun (self: u128) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
                <:
                u128)
            <:
            u16));
    f_as_i16_pre = (fun (self: u128) -> true);
    f_as_i16_post = (fun (self: u128) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
                <:
                u128)
            <:
            i16));
    f_as_u32_pre = (fun (self: u128) -> true);
    f_as_u32_post = (fun (self: u128) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
                <:
                u128)
            <:
            u32));
    f_as_i32_pre = (fun (self: u128) -> true);
    f_as_i32_post = (fun (self: u128) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
                <:
                u128)
            <:
            i32));
    f_as_u64_pre = (fun (self: u128) -> true);
    f_as_u64_post = (fun (self: u128) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
                <:
                u128)
            <:
            u64));
    f_as_i64_pre = (fun (self: u128) -> true);
    f_as_i64_post = (fun (self: u128) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
                <:
                u128)
            <:
            i64));
    f_as_u128_pre = (fun (self: u128) -> true);
    f_as_u128_post = (fun (self: u128) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: u128) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self <: u128));
    f_as_i128_pre = (fun (self: u128) -> true);
    f_as_i128_post = (fun (self: u128) (out: i128) -> true);
    f_as_i128
    =
    fun (self: u128) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #u128 #FStar.Tactics.Typeclasses.solve self
              <:
              u128)
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_i8: t_CastOps i8 =
  {
    f_as_u8_pre = (fun (self: i8) -> true);
    f_as_u8_post = (fun (self: i8) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8
              )
            <:
            u8));
    f_as_i8_pre = (fun (self: i8) -> true);
    f_as_i8_post = (fun (self: i8) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8));
    f_as_u16_pre = (fun (self: i8) -> true);
    f_as_u16_post = (fun (self: i8) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8
              )
            <:
            u16));
    f_as_i16_pre = (fun (self: i8) -> true);
    f_as_i16_post = (fun (self: i8) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8
              )
            <:
            i16));
    f_as_u32_pre = (fun (self: i8) -> true);
    f_as_u32_post = (fun (self: i8) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8
              )
            <:
            u32));
    f_as_i32_pre = (fun (self: i8) -> true);
    f_as_i32_post = (fun (self: i8) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8
              )
            <:
            i32));
    f_as_u64_pre = (fun (self: i8) -> true);
    f_as_u64_post = (fun (self: i8) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8
              )
            <:
            u64));
    f_as_i64_pre = (fun (self: i8) -> true);
    f_as_i64_post = (fun (self: i8) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8
              )
            <:
            i64));
    f_as_u128_pre = (fun (self: i8) -> true);
    f_as_u128_post = (fun (self: i8) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: i8) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8
              )
            <:
            u128));
    f_as_i128_pre = (fun (self: i8) -> true);
    f_as_i128_post = (fun (self: i8) (out: i128) -> true);
    f_as_i128
    =
    fun (self: i8) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #i8 #FStar.Tactics.Typeclasses.solve self <: i8)
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_i16: t_CastOps i16 =
  {
    f_as_u8_pre = (fun (self: i16) -> true);
    f_as_u8_post = (fun (self: i16) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self
                <:
                i16)
            <:
            u8));
    f_as_i8_pre = (fun (self: i16) -> true);
    f_as_i8_post = (fun (self: i16) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self
                <:
                i16)
            <:
            i8));
    f_as_u16_pre = (fun (self: i16) -> true);
    f_as_u16_post = (fun (self: i16) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self
                <:
                i16)
            <:
            u16));
    f_as_i16_pre = (fun (self: i16) -> true);
    f_as_i16_post = (fun (self: i16) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self <: i16));
    f_as_u32_pre = (fun (self: i16) -> true);
    f_as_u32_post = (fun (self: i16) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self
                <:
                i16)
            <:
            u32));
    f_as_i32_pre = (fun (self: i16) -> true);
    f_as_i32_post = (fun (self: i16) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self
                <:
                i16)
            <:
            i32));
    f_as_u64_pre = (fun (self: i16) -> true);
    f_as_u64_post = (fun (self: i16) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self
                <:
                i16)
            <:
            u64));
    f_as_i64_pre = (fun (self: i16) -> true);
    f_as_i64_post = (fun (self: i16) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self
                <:
                i16)
            <:
            i64));
    f_as_u128_pre = (fun (self: i16) -> true);
    f_as_u128_post = (fun (self: i16) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: i16) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self
                <:
                i16)
            <:
            u128));
    f_as_i128_pre = (fun (self: i16) -> true);
    f_as_i128_post = (fun (self: i16) (out: i128) -> true);
    f_as_i128
    =
    fun (self: i16) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #i16 #FStar.Tactics.Typeclasses.solve self <: i16
            )
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_i32: t_CastOps i32 =
  {
    f_as_u8_pre = (fun (self: i32) -> true);
    f_as_u8_post = (fun (self: i32) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self
                <:
                i32)
            <:
            u8));
    f_as_i8_pre = (fun (self: i32) -> true);
    f_as_i8_post = (fun (self: i32) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self
                <:
                i32)
            <:
            i8));
    f_as_u16_pre = (fun (self: i32) -> true);
    f_as_u16_post = (fun (self: i32) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self
                <:
                i32)
            <:
            u16));
    f_as_i16_pre = (fun (self: i32) -> true);
    f_as_i16_post = (fun (self: i32) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self
                <:
                i32)
            <:
            i16));
    f_as_u32_pre = (fun (self: i32) -> true);
    f_as_u32_post = (fun (self: i32) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self
                <:
                i32)
            <:
            u32));
    f_as_i32_pre = (fun (self: i32) -> true);
    f_as_i32_post = (fun (self: i32) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self <: i32));
    f_as_u64_pre = (fun (self: i32) -> true);
    f_as_u64_post = (fun (self: i32) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self
                <:
                i32)
            <:
            u64));
    f_as_i64_pre = (fun (self: i32) -> true);
    f_as_i64_post = (fun (self: i32) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self
                <:
                i32)
            <:
            i64));
    f_as_u128_pre = (fun (self: i32) -> true);
    f_as_u128_post = (fun (self: i32) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: i32) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self
                <:
                i32)
            <:
            u128));
    f_as_i128_pre = (fun (self: i32) -> true);
    f_as_i128_post = (fun (self: i32) (out: i128) -> true);
    f_as_i128
    =
    fun (self: i32) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #i32 #FStar.Tactics.Typeclasses.solve self <: i32
            )
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_i64: t_CastOps i64 =
  {
    f_as_u8_pre = (fun (self: i64) -> true);
    f_as_u8_post = (fun (self: i64) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self
                <:
                i64)
            <:
            u8));
    f_as_i8_pre = (fun (self: i64) -> true);
    f_as_i8_post = (fun (self: i64) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self
                <:
                i64)
            <:
            i8));
    f_as_u16_pre = (fun (self: i64) -> true);
    f_as_u16_post = (fun (self: i64) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self
                <:
                i64)
            <:
            u16));
    f_as_i16_pre = (fun (self: i64) -> true);
    f_as_i16_post = (fun (self: i64) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self
                <:
                i64)
            <:
            i16));
    f_as_u32_pre = (fun (self: i64) -> true);
    f_as_u32_post = (fun (self: i64) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self
                <:
                i64)
            <:
            u32));
    f_as_i32_pre = (fun (self: i64) -> true);
    f_as_i32_post = (fun (self: i64) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self
                <:
                i64)
            <:
            i32));
    f_as_u64_pre = (fun (self: i64) -> true);
    f_as_u64_post = (fun (self: i64) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self
                <:
                i64)
            <:
            u64));
    f_as_i64_pre = (fun (self: i64) -> true);
    f_as_i64_post = (fun (self: i64) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self <: i64));
    f_as_u128_pre = (fun (self: i64) -> true);
    f_as_u128_post = (fun (self: i64) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: i64) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self
                <:
                i64)
            <:
            u128));
    f_as_i128_pre = (fun (self: i64) -> true);
    f_as_i128_post = (fun (self: i64) (out: i128) -> true);
    f_as_i128
    =
    fun (self: i64) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (cast (Libcrux_secrets.Traits.f_declassify #i64 #FStar.Tactics.Typeclasses.solve self <: i64
            )
          <:
          i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_CastOps_for_i128: t_CastOps i128 =
  {
    f_as_u8_pre = (fun (self: i128) -> true);
    f_as_u8_post = (fun (self: i128) (out: u8) -> true);
    f_as_u8
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            u8));
    f_as_i8_pre = (fun (self: i128) -> true);
    f_as_i8_post = (fun (self: i128) (out: i8) -> true);
    f_as_i8
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #i8
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            i8));
    f_as_u16_pre = (fun (self: i128) -> true);
    f_as_u16_post = (fun (self: i128) (out: u16) -> true);
    f_as_u16
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #u16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            u16));
    f_as_i16_pre = (fun (self: i128) -> true);
    f_as_i16_post = (fun (self: i128) (out: i16) -> true);
    f_as_i16
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #i16
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            i16));
    f_as_u32_pre = (fun (self: i128) -> true);
    f_as_u32_post = (fun (self: i128) (out: u32) -> true);
    f_as_u32
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #u32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            u32));
    f_as_i32_pre = (fun (self: i128) -> true);
    f_as_i32_post = (fun (self: i128) (out: i32) -> true);
    f_as_i32
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #i32
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            i32));
    f_as_u64_pre = (fun (self: i128) -> true);
    f_as_u64_post = (fun (self: i128) (out: u64) -> true);
    f_as_u64
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #u64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            u64));
    f_as_i64_pre = (fun (self: i128) -> true);
    f_as_i64_post = (fun (self: i128) (out: i64) -> true);
    f_as_i64
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #i64
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            i64));
    f_as_u128_pre = (fun (self: i128) -> true);
    f_as_u128_post = (fun (self: i128) (out: u128) -> true);
    f_as_u128
    =
    (fun (self: i128) ->
        Libcrux_secrets.Traits.f_classify #u128
          #FStar.Tactics.Typeclasses.solve
          (cast (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self
                <:
                i128)
            <:
            u128));
    f_as_i128_pre = (fun (self: i128) -> true);
    f_as_i128_post = (fun (self: i128) (out: i128) -> true);
    f_as_i128
    =
    fun (self: i128) ->
      Libcrux_secrets.Traits.f_classify #i128
        #FStar.Tactics.Typeclasses.solve
        (Libcrux_secrets.Traits.f_declassify #i128 #FStar.Tactics.Typeclasses.solve self <: i128)
  }
