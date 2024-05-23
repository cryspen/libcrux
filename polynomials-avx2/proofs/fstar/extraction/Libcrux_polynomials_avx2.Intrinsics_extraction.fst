module Libcrux_polynomials_avx2.Intrinsics_extraction
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_Vec128 = u8

unfold
let t_Vec256 = u8

let mm256_add_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_add_epi32 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_and_si256 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_blend_epi16 (v_CONTROL: i32) (lhs rhs: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_CONTROL >=. 0l <: bool) && (v_CONTROL <. 256l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: CONTROL >= 0 && CONTROL < 256"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_castsi128_si256 (vector: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_castsi256_si128 (vector: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_cmpgt_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_cvtepi16_epi32 (vector: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_extracti128_si256 (v_CONTROL: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_CONTROL =. 0l <: bool) || (v_CONTROL =. 1l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: CONTROL == 0 || CONTROL == 1"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_inserti128_si256 (v_CONTROL: i32) (vector vector_i128: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_CONTROL =. 0l <: bool) || (v_CONTROL =. 1l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: CONTROL == 0 || CONTROL == 1"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_loadu_si256 (input: t_Slice i16) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #i16 input, sz 16 <: (usize & usize) with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind =
              Core.Panicking.AssertKind_Eq <: Core.Panicking.t_AssertKind
            in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed #usize
                  #usize
                  kind
                  left_val
                  right_val
                  (Core.Option.Option_None <: Core.Option.t_Option Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_madd_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mul_epu32 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mulhi_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mullo_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_mullo_epi32 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_packs_epi32 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_permute4x64_epi64 (v_CONTROL: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_CONTROL >=. 0l <: bool) && (v_CONTROL <. 256l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: CONTROL >= 0 && CONTROL < 256"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_permutevar8x32_epi32 (vector control: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set1_epi16 (constant: i16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set1_epi32 (constant: i32) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set_epi16
      (input15 input14 input13 input12 input11 input10 input9 input8 input7 input6 input5 input4 input3 input2 input1 input0:
          i16)
    : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set_epi32 (input7 input6 input5 input4 input3 input2 input1 input0: i32) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_set_epi8
      (byte31 byte30 byte29 byte28 byte27 byte26 byte25 byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          i8)
    : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_setzero_si256 (_: Prims.unit) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_shuffle_epi32 (v_CONTROL: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_CONTROL >=. 0l <: bool) && (v_CONTROL <. 256l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: CONTROL >= 0 && CONTROL < 256"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_shuffle_epi8 (vector control: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_slli_epi16 (v_SHIFT_BY: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_SHIFT_BY >=. 0l <: bool) && (v_SHIFT_BY <. 16l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: SHIFT_BY >= 0 && SHIFT_BY < 16"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_slli_epi32 (v_SHIFT_BY: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_SHIFT_BY >=. 0l <: bool) && (v_SHIFT_BY <. 32l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: SHIFT_BY >= 0 && SHIFT_BY < 32"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_sllv_epi32 (vector counts: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srai_epi16 (v_SHIFT_BY: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_SHIFT_BY >=. 0l <: bool) && (v_SHIFT_BY <. 16l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: SHIFT_BY >= 0 && SHIFT_BY < 16"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srai_epi32 (v_SHIFT_BY: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_SHIFT_BY >=. 0l <: bool) && (v_SHIFT_BY <. 32l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: SHIFT_BY >= 0 && SHIFT_BY < 32"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srli_epi16 (v_SHIFT_BY: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_SHIFT_BY >=. 0l <: bool) && (v_SHIFT_BY <. 16l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: SHIFT_BY >= 0 && SHIFT_BY < 16"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srli_epi32 (v_SHIFT_BY: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_SHIFT_BY >=. 0l <: bool) && (v_SHIFT_BY <. 32l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: SHIFT_BY >= 0 && SHIFT_BY < 32"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_srli_epi64 (v_SHIFT_BY: i32) (vector: u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_SHIFT_BY >=. 0l <: bool) && (v_SHIFT_BY <. 64l <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: SHIFT_BY >= 0 && SHIFT_BY < 64"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_storeu_si256 (output: t_Slice i16) (vector: u8) : t_Slice i16 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #i16 output, sz 16 <: (usize & usize) with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind =
              Core.Panicking.AssertKind_Eq <: Core.Panicking.t_AssertKind
            in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed #usize
                  #usize
                  kind
                  left_val
                  right_val
                  (Core.Option.Option_None <: Core.Option.t_Option Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let hax_temp_output:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm256_sub_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_unpackhi_epi32 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_unpackhi_epi64 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_unpacklo_epi32 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm256_xor_si256 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_add_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_loadu_si128 (input: t_Slice u8) : u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 input, sz 16 <: (usize & usize) with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind =
              Core.Panicking.AssertKind_Eq <: Core.Panicking.t_AssertKind
            in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed #usize
                  #usize
                  kind
                  left_val
                  right_val
                  (Core.Option.Option_None <: Core.Option.t_Option Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_movemask_epi8 (vector: u8) : i32 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_mulhi_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_mullo_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_packs_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_set1_epi16 (constant: i16) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_set_epi8
      (byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          u8)
    : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_shuffle_epi8 (vector control: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)

let mm_storeu_bytes_si128 (output: t_Slice u8) (vector: u8) : t_Slice u8 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 output, sz 16 <: (usize & usize) with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind =
              Core.Panicking.AssertKind_Eq <: Core.Panicking.t_AssertKind
            in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed #usize
                  #usize
                  kind
                  left_val
                  right_val
                  (Core.Option.Option_None <: Core.Option.t_Option Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let hax_temp_output:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm_storeu_si128 (output: t_Slice i16) (vector: u8) : t_Slice i16 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #i16 output, sz 8 <: (usize & usize) with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind =
              Core.Panicking.AssertKind_Eq <: Core.Panicking.t_AssertKind
            in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed #usize
                  #usize
                  kind
                  left_val
                  right_val
                  (Core.Option.Option_None <: Core.Option.t_Option Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let hax_temp_output:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
        <:
        Rust_primitives.Hax.t_Never)
  in
  output

let mm_sub_epi16 (lhs rhs: u8) : u8 =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
      <:
      Rust_primitives.Hax.t_Never)
