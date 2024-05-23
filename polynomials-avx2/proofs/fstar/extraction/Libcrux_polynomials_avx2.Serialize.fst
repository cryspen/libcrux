module Libcrux_polynomials_avx2.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let deserialize_1_ (bytes: t_Slice u8) : u8 =
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (cast (bytes.[ sz 1 ] <: u8)
        <:
        i16) (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16)
  in
  let shift_lsb_to_msb:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 8l <: i16)
      (1s <<! 9l <: i16) (1s <<! 10l <: i16) (1s <<! 11l <: i16) (1s <<! 12l <: i16)
      (1s <<! 13l <: i16) (1s <<! 14l <: i16) (1s <<! 15l <: i16) (1s <<! 8l <: i16)
      (1s <<! 9l <: i16) (1s <<! 10l <: i16) (1s <<! 11l <: i16) (1s <<! 12l <: i16)
      (1s <<! 13l <: i16) (1s <<! 14l <: i16) (1s <<! 15l <: i16)
  in
  let coefficients_in_msb:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 coefficients shift_lsb_to_msb
  in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi16 15l coefficients_in_msb

let deserialize_10_ (bytes: t_Slice u8) : u8 =
  let shift_lsbs_to_msbs:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 0l <: i16)
      (1s <<! 2l <: i16) (1s <<! 4l <: i16) (1s <<! 6l <: i16) (1s <<! 0l <: i16) (1s <<! 2l <: i16)
      (1s <<! 4l <: i16) (1s <<! 6l <: i16) (1s <<! 0l <: i16) (1s <<! 2l <: i16) (1s <<! 4l <: i16)
      (1s <<! 6l <: i16) (1s <<! 0l <: i16) (1s <<! 2l <: i16) (1s <<! 4l <: i16) (1s <<! 6l <: i16)
  in
  let lower_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_loadu_si128 (Core.Result.impl__unwrap #(t_Slice
            u8)
          #Core.Convert.t_Infallible
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Slice u8)
              (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result (t_Slice u8) Core.Convert.t_Infallible)
        <:
        t_Slice u8)
  in
  let lower_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_shuffle_epi8 lower_coefficients
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_set_epi8 9uy 8uy 8uy 7uy 7uy 6uy 6uy 5uy
          4uy 3uy 3uy 2uy 2uy 1uy 1uy 0uy
        <:
        u8)
  in
  let upper_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_loadu_si128 (Core.Result.impl__unwrap #(t_Slice
            u8)
          #Core.Convert.t_Infallible
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Slice u8)
              (bytes.[ { Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 20 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result (t_Slice u8) Core.Convert.t_Infallible)
        <:
        t_Slice u8)
  in
  let upper_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_shuffle_epi8 upper_coefficients
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_set_epi8 15uy 14uy 14uy 13uy 13uy 12uy 12uy
          11uy 10uy 9uy 9uy 8uy 8uy 7uy 7uy 6uy
        <:
        u8)
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi128_si256 lower_coefficients
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_inserti128_si256 1l
      coefficients
      upper_coefficients
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 coefficients shift_lsbs_to_msbs
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi16 6l coefficients
  in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_and_si256 coefficients
    (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 ((1s <<! 10l <: i16) -! 1s
          <:
          i16)
      <:
      u8)

let deserialize_12_ (bytes: t_Slice u8) : u8 =
  let shift_lsbs_to_msbs:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 0l <: i16)
      (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16)
      (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16)
      (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16)
  in
  let lower_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_loadu_si128 (Core.Result.impl__unwrap #(t_Slice
            u8)
          #Core.Convert.t_Infallible
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Slice u8)
              (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result (t_Slice u8) Core.Convert.t_Infallible)
        <:
        t_Slice u8)
  in
  let lower_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_shuffle_epi8 lower_coefficients
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_set_epi8 11uy 10uy 10uy 9uy 8uy 7uy 7uy 6uy
          5uy 4uy 4uy 3uy 2uy 1uy 1uy 0uy
        <:
        u8)
  in
  let upper_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_loadu_si128 (Core.Result.impl__unwrap #(t_Slice
            u8)
          #Core.Convert.t_Infallible
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Slice u8)
              (bytes.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 24 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result (t_Slice u8) Core.Convert.t_Infallible)
        <:
        t_Slice u8)
  in
  let upper_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_shuffle_epi8 upper_coefficients
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_set_epi8 15uy 14uy 14uy 13uy 12uy 11uy 11uy
          10uy 9uy 8uy 8uy 7uy 6uy 5uy 5uy 4uy
        <:
        u8)
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi128_si256 lower_coefficients
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_inserti128_si256 1l
      coefficients
      upper_coefficients
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 coefficients shift_lsbs_to_msbs
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi16 4l coefficients
  in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_and_si256 coefficients
    (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 ((1s <<! 12l <: i16) -! 1s
          <:
          i16)
      <:
      u8)

let deserialize_4_ (bytes: t_Slice u8) : u8 =
  let shift_lsbs_to_msbs:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 0l <: i16)
      (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16)
      (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16)
      (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16)
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (cast (bytes.[ sz 7 ] <: u8)
        <:
        i16) (cast (bytes.[ sz 7 ] <: u8) <: i16) (cast (bytes.[ sz 6 ] <: u8) <: i16)
      (cast (bytes.[ sz 6 ] <: u8) <: i16) (cast (bytes.[ sz 5 ] <: u8) <: i16)
      (cast (bytes.[ sz 5 ] <: u8) <: i16) (cast (bytes.[ sz 4 ] <: u8) <: i16)
      (cast (bytes.[ sz 4 ] <: u8) <: i16) (cast (bytes.[ sz 3 ] <: u8) <: i16)
      (cast (bytes.[ sz 3 ] <: u8) <: i16) (cast (bytes.[ sz 2 ] <: u8) <: i16)
      (cast (bytes.[ sz 2 ] <: u8) <: i16) (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16)
  in
  let coefficients_in_msb:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 coefficients shift_lsbs_to_msbs
  in
  let coefficients_in_lsb:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi16 4l coefficients_in_msb
  in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_and_si256 coefficients_in_lsb
    (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 ((1s <<! 4l <: i16) -! 1s
          <:
          i16)
      <:
      u8)

let deserialize_5_ (bytes: t_Slice u8) : u8 =
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_set_epi8 (bytes.[ sz 9 ] <: u8)
      (bytes.[ sz 8 ] <: u8) (bytes.[ sz 8 ] <: u8) (bytes.[ sz 7 ] <: u8) (bytes.[ sz 7 ] <: u8)
      (bytes.[ sz 6 ] <: u8) (bytes.[ sz 6 ] <: u8) (bytes.[ sz 5 ] <: u8) (bytes.[ sz 4 ] <: u8)
      (bytes.[ sz 3 ] <: u8) (bytes.[ sz 3 ] <: u8) (bytes.[ sz 2 ] <: u8) (bytes.[ sz 2 ] <: u8)
      (bytes.[ sz 1 ] <: u8) (bytes.[ sz 1 ] <: u8) (bytes.[ sz 0 ] <: u8)
  in
  let coefficients_loaded:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi128_si256 coefficients
  in
  let coefficients_loaded:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_inserti128_si256 1l
      coefficients_loaded
      coefficients
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_shuffle_epi8 coefficients_loaded
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi8 15y 14y 15y 14y 13y 12y 13y 12y
          11y 10y 11y 10y 9y 8y 9y 8y 7y 6y 7y 6y 5y 4y 5y 4y 3y 2y 3y 2y 1y 0y 1y 0y
        <:
        u8)
  in
  let coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 coefficients
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 0l <: i16)
          (1s <<! 5l <: i16) (1s <<! 2l <: i16) (1s <<! 7l <: i16) (1s <<! 4l <: i16)
          (1s <<! 9l <: i16) (1s <<! 6l <: i16) (1s <<! 11l <: i16) (1s <<! 0l <: i16)
          (1s <<! 5l <: i16) (1s <<! 2l <: i16) (1s <<! 7l <: i16) (1s <<! 4l <: i16)
          (1s <<! 9l <: i16) (1s <<! 6l <: i16) (1s <<! 11l <: i16)
        <:
        u8)
  in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi16 11l coefficients

let serialize_1_ (vector: u8) : t_Array u8 (sz 2) =
  let lsb_to_msb:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_slli_epi16 15l vector in
  let low_msbs:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi256_si128 lsb_to_msb
  in
  let high_msbs:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_extracti128_si256 1l lsb_to_msb
  in
  let msbs:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm_packs_epi16 low_msbs high_msbs in
  let bits_packed:i32 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm_movemask_epi8 msbs in
  let serialized:t_Array u8 (sz 2) = Rust_primitives.Hax.repeat 0uy (sz 2) in
  let serialized:t_Array u8 (sz 2) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 0)
      (cast (bits_packed <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 2) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 1)
      (cast (bits_packed >>! 8l <: i32) <: u8)
  in
  serialized

let serialize_10_ (vector: u8) : t_Array u8 (sz 20) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let adjacent_2_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_madd_epi16 vector
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 10l <: i16) 1s
          (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16)
          1s (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16) 1s
        <:
        u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi32 0l 12l 0l 12l 0l 12l 0l 12l
        <:
        u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi64 12l adjacent_4_combined
  in
  let adjacent_8_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_shuffle_epi8 adjacent_4_combined
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) 12y 11y 10y 9y 8y 4y 3y 2y 1y 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 12y 11y 10y 9y
          8y 4y 3y 2y 1y 0y
        <:
        u8)
  in
  let lower_8_:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi256_si128 adjacent_8_combined
  in
  let upper_8_:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_extracti128_si256 1l adjacent_8_combined
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_8_
        <:
        t_Slice u8)
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 10; Core.Ops.Range.f_end = sz 26 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = sz 10;
                Core.Ops.Range.f_end = sz 26
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_8_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 (sz 20))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (sz 20))
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 20 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 20)) Core.Array.t_TryFromSliceError)

let serialize_12_ (vector: u8) : t_Array u8 (sz 24) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let adjacent_2_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_madd_epi16 vector
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 12l <: i16) 1s
          (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16)
          1s (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16) 1s
        <:
        u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi32 0l 8l 0l 8l 0l 8l 0l 8l <: u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi64 8l adjacent_4_combined
  in
  let adjacent_8_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_shuffle_epi8 adjacent_4_combined
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) 13y 12y
          11y 10y 9y 8y 5y 4y 3y 2y 1y 0y (-1y) (-1y) (-1y) (-1y) 13y 12y 11y 10y 9y 8y 5y 4y 3y 2y
          1y 0y
        <:
        u8)
  in
  let lower_8_:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi256_si128 adjacent_8_combined
  in
  let upper_8_:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_extracti128_si256 1l adjacent_8_combined
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_8_
        <:
        t_Slice u8)
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 12; Core.Ops.Range.f_end = sz 28 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = sz 12;
                Core.Ops.Range.f_end = sz 28
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_8_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 (sz 24))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (sz 24))
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 24 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 24)) Core.Array.t_TryFromSliceError)

let serialize_4_ (vector: u8) : t_Array u8 (sz 8) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let adjacent_2_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_madd_epi16 vector
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 4l <: i16) 1s
          (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
          (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
        <:
        u8)
  in
  let adjacent_8_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 12y 8y 4y 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 12y 8y 4y 0y
        <:
        u8)
  in
  let combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_permutevar8x32_epi32 adjacent_8_combined
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi32 0l 0l 0l 0l 0l 0l 4l 0l <: u8)
  in
  let combined:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi256_si128 combined in
  let serialized:t_Array u8 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full serialized
      (Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_bytes_si128 (serialized.[ Core.Ops.Range.RangeFull
              <:
              Core.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
          combined
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 (sz 8))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (sz 8))
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 8)) Core.Array.t_TryFromSliceError)

let serialize_5_ (vector: u8) : t_Array u8 (sz 10) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let adjacent_2_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_madd_epi16 vector
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi16 (1s <<! 5l <: i16) 1s
          (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s
          (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s
        <:
        u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi32 0l 22l 0l 22l 0l 22l 0l 22l
        <:
        u8)
  in
  let adjacent_4_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi64 22l adjacent_4_combined
  in
  let adjacent_8_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_shuffle_epi32 8l adjacent_4_combined
  in
  let adjacent_8_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sllv_epi32 adjacent_8_combined
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set_epi32 0l 12l 0l 12l 0l 12l 0l 12l
        <:
        u8)
  in
  let adjacent_8_combined:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi64 12l adjacent_8_combined
  in
  let lower_8_:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi256_si128 adjacent_8_combined
  in
  let upper_8_:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_extracti128_si256 1l adjacent_8_combined
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_8_
        <:
        t_Slice u8)
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 21 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = sz 5;
                Core.Ops.Range.f_end = sz 21
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_8_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 (sz 10))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (sz 10))
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 10 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 10)) Core.Array.t_TryFromSliceError)

let deserialize_11_ (bytes: t_Slice u8) : u8 =
  let output:Libcrux_polynomials_avx2.Portable.t_PortableVector =
    Libcrux_polynomials_avx2.Portable.deserialize_11_ bytes
  in
  (Libcrux_polynomials_avx2.from_i16_array (Rust_primitives.unsize (Libcrux_polynomials_avx2.Portable.to_i16_array
              output
            <:
            t_Array i16 (sz 16))
        <:
        t_Slice i16))
    .Libcrux_polynomials_avx2.f_elements

let serialize_11_ (vector: u8) : t_Array u8 (sz 22) =
  let input:Libcrux_polynomials_avx2.Portable.t_PortableVector =
    Libcrux_polynomials_avx2.Portable.from_i16_array (Libcrux_polynomials_avx2.to_i16_array ({
              Libcrux_polynomials_avx2.f_elements = vector
            }
            <:
            Libcrux_polynomials_avx2.t_SIMD256Vector)
        <:
        t_Array i16 (sz 16))
  in
  Libcrux_polynomials_avx2.Portable.serialize_11_ input
