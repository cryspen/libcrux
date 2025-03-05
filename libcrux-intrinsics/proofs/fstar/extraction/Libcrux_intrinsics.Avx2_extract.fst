module Libcrux_intrinsics.Avx2_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let mm256_storeu_si256_u8
      (output: t_Slice u8)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : t_Slice u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 output, mk_usize 32 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm256_storeu_si256_i16
      (output: t_Slice i16)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (t_Slice i16)
      Prims.l_True
      (ensures
        fun output_future ->
          let output_future:t_Slice i16 = output_future in
          (Core.Slice.impl__len #i16 output_future <: usize) =.
          (Core.Slice.impl__len #i16 output <: usize)) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #i16 output, mk_usize 16 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm256_storeu_si256_i32
      (output: t_Slice i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : t_Slice i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #i32 output, mk_usize 8 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm_storeu_si128
      (output: t_Slice i16)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : t_Slice i16 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #i16 output <: usize) >=. mk_usize 8 <: bool)
      in
      ()
  in
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm_storeu_si128_i32
      (output: t_Slice i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : t_Slice i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #i32 output, mk_usize 4 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm_storeu_bytes_si128
      (output: t_Slice u8)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : t_Slice u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 output, mk_usize 16 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let _:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm_loadu_si128 (input: t_Slice u8) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 input, mk_usize 16 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_loadu_si256_u8 (input: t_Slice u8) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 input, mk_usize 32 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_loadu_si256_i16 (input: t_Slice i16) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #i16 input, mk_usize 16 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_loadu_si256_i32 (input: t_Slice i32) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #i32 input, mk_usize 8 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_setzero_si256 (_: Prims.unit) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set_m128i (hi lo: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_set_epi8
      (byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          u8)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set_epi8
      (byte31 byte30 byte29 byte28 byte27 byte26 byte25 byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          i8)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set1_epi16 (constant: i16) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set_epi16
      (input15 input14 input13 input12 input11 input10 input9 input8 input7 input6 input5 input4 input3 input2 input1 input0:
          i16)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_set1_epi16 (constant: i16) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set1_epi32 (constant: i32) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_set_epi32 (input3 input2 input1 input0: i32)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set_epi32 (input7 input6 input5 input4 input3 input2 input1 input0: i32)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_add_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_sub_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_add_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_madd_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_add_epi32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_sub_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_add_epi64 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_abs_epi32 (a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_sub_epi32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mullo_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_mullo_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_cmpgt_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_cmpgt_epi32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_cmpeq_epi32 (a b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_sign_epi32 (a b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_castsi256_ps (a: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_movemask_ps (a: u8) : i32 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_mulhi_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mullo_epi32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mulhi_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mul_epu32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mul_epi32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_and_si256 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_or_si256 (a b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_testz_si256 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) : i32 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_xor_si256 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srai_epi16 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires v_SHIFT_BY >=. mk_i32 0 && v_SHIFT_BY <. mk_i32 16)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_SHIFT_BY >=. mk_i32 0 <: bool) && (v_SHIFT_BY <. mk_i32 16 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srai_epi32 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_SHIFT_BY >=. mk_i32 0 <: bool) && (v_SHIFT_BY <. mk_i32 32 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srli_epi16 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_SHIFT_BY >=. mk_i32 0 <: bool) && (v_SHIFT_BY <. mk_i32 16 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srli_epi32 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_SHIFT_BY >=. mk_i32 0 <: bool) && (v_SHIFT_BY <. mk_i32 32 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_srli_epi64 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_SHIFT_BY >=. mk_i32 0 <: bool) && (v_SHIFT_BY <. mk_i32 64 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srli_epi64 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Minicore.Arch.X86.e_mm256_srli_epi64 v_SHIFT_BY vector

let mm256_slli_epi16 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Minicore.Arch.X86.e_mm256_slli_epi16 v_SHIFT_BY vector

let mm256_slli_epi32 (v_SHIFT_BY: i32) (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_SHIFT_BY >=. mk_i32 0 <: bool) && (v_SHIFT_BY <. mk_i32 32 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_shuffle_epi8 (vector control: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_shuffle_epi8 (vector control: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_shuffle_epi32
      (v_CONTROL: i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_CONTROL >=. mk_i32 0 <: bool) && (v_CONTROL <. mk_i32 256 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_permute4x64_epi64
      (v_CONTROL: i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_CONTROL >=. mk_i32 0 <: bool) && (v_CONTROL <. mk_i32 256 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_unpackhi_epi64 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_unpacklo_epi32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_unpackhi_epi32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_castsi256_si128 (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Minicore.Arch.X86.e_mm256_castsi256_si128 vector

let mm256_castsi128_si256 (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_cvtepi16_epi32 (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_packs_epi16 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_packs_epi32 (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_extracti128_si256
      (v_CONTROL: i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_CONTROL =. mk_i32 0 <: bool) || (v_CONTROL =. mk_i32 1 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_inserti128_si256
      (v_CONTROL: i32)
      (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (vector_i128: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_CONTROL =. mk_i32 0 <: bool) || (v_CONTROL =. mk_i32 1 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_blend_epi16 (v_CONTROL: i32) (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_CONTROL >=. mk_i32 0 <: bool) && (v_CONTROL <. mk_i32 256 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_blend_epi32 (v_CONTROL: i32) (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_CONTROL >=. mk_i32 0 <: bool) && (v_CONTROL <. mk_i32 256 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let vec256_blendv_epi32 (a b mask: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_movemask_epi8 (vector: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)) : i32 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_permutevar8x32_epi32 (vector control: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srlv_epi32 (vector counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srlv_epi64 (vector counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_sllv_epi32 (vector counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_sllv_epi32 (vector counts: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_slli_epi64 (v_LEFT: i32) (x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_bsrli_epi128 (v_SHIFT_BY: i32) (x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_SHIFT_BY >. mk_i32 0 <: bool) && (v_SHIFT_BY <. mk_i32 16 <: bool))
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_andnot_si256 (a b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set1_epi64x (a: i64) : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set_epi64x (input3 input2 input1 input0: i64)
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_unpacklo_epi64 (a b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_permute2x128_si256 (v_IMM8: i32) (a b: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)
