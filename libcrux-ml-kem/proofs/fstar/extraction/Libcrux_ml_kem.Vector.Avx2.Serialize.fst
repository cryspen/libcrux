module Libcrux_ml_kem.Vector.Avx2.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable in
  ()

let deserialize_1_ (bytes: t_Slice u8) =
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16)
  in
  let shift_lsb_to_msb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 8l <: i16) (1s <<! 9l <: i16)
      (1s <<! 10l <: i16) (1s <<! 11l <: i16) (1s <<! 12l <: i16) (1s <<! 13l <: i16)
      (1s <<! 14l <: i16) (-32768s) (1s <<! 8l <: i16) (1s <<! 9l <: i16) (1s <<! 10l <: i16)
      (1s <<! 11l <: i16) (1s <<! 12l <: i16) (1s <<! 13l <: i16) (1s <<! 14l <: i16) (-32768s)
  in
  let coefficients_in_msb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients shift_lsb_to_msb
  in
  Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 15l coefficients_in_msb

let deserialize_10_ (bytes: t_Slice u8) =
  let shift_lsbs_to_msbs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 0l <: i16) (1s <<! 2l <: i16)
      (1s <<! 4l <: i16) (1s <<! 6l <: i16) (1s <<! 0l <: i16) (1s <<! 2l <: i16) (1s <<! 4l <: i16)
      (1s <<! 6l <: i16) (1s <<! 0l <: i16) (1s <<! 2l <: i16) (1s <<! 4l <: i16) (1s <<! 6l <: i16)
      (1s <<! 0l <: i16) (1s <<! 2l <: i16) (1s <<! 4l <: i16) (1s <<! 6l <: i16)
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (bytes.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 lower_coefficients
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 9uy 8uy 8uy 7uy 7uy 6uy 6uy 5uy 4uy 3uy 3uy 2uy
          2uy 1uy 1uy 0uy
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (bytes.[ {
            Core.Ops.Range.f_start = sz 4;
            Core.Ops.Range.f_end = sz 20
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 upper_coefficients
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 15uy 14uy 14uy 13uy 13uy 12uy 12uy 11uy 10uy 9uy
          9uy 8uy 8uy 7uy 7uy 6uy
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi128_si256 lower_coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_inserti128_si256 1l coefficients upper_coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients shift_lsbs_to_msbs
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 6l coefficients
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((1s <<! 10l <: i16) -! 1s <: i16)
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let deserialize_12_ (bytes: t_Slice u8) =
  let shift_lsbs_to_msbs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 0l <: i16) (1s <<! 4l <: i16)
      (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16)
      (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16)
      (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16)
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (bytes.[ {
            Core.Ops.Range.f_start = sz 0;
            Core.Ops.Range.f_end = sz 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 lower_coefficients
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 11uy 10uy 10uy 9uy 8uy 7uy 7uy 6uy 5uy 4uy 4uy
          3uy 2uy 1uy 1uy 0uy
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (bytes.[ {
            Core.Ops.Range.f_start = sz 8;
            Core.Ops.Range.f_end = sz 24
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 upper_coefficients
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 15uy 14uy 14uy 13uy 12uy 11uy 11uy 10uy 9uy 8uy
          8uy 7uy 6uy 5uy 5uy 4uy
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi128_si256 lower_coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_inserti128_si256 1l coefficients upper_coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients shift_lsbs_to_msbs
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 4l coefficients
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((1s <<! 12l <: i16) -! 1s <: i16)
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let deserialize_4_ (bytes: t_Slice u8) =
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (cast (bytes.[ sz 7 ] <: u8) <: i16)
      (cast (bytes.[ sz 7 ] <: u8) <: i16) (cast (bytes.[ sz 6 ] <: u8) <: i16)
      (cast (bytes.[ sz 6 ] <: u8) <: i16) (cast (bytes.[ sz 5 ] <: u8) <: i16)
      (cast (bytes.[ sz 5 ] <: u8) <: i16) (cast (bytes.[ sz 4 ] <: u8) <: i16)
      (cast (bytes.[ sz 4 ] <: u8) <: i16) (cast (bytes.[ sz 3 ] <: u8) <: i16)
      (cast (bytes.[ sz 3 ] <: u8) <: i16) (cast (bytes.[ sz 2 ] <: u8) <: i16)
      (cast (bytes.[ sz 2 ] <: u8) <: i16) (cast (bytes.[ sz 1 ] <: u8) <: i16)
      (cast (bytes.[ sz 1 ] <: u8) <: i16) (cast (bytes.[ sz 0 ] <: u8) <: i16)
      (cast (bytes.[ sz 0 ] <: u8) <: i16)
  in
  let shift_lsbs_to_msbs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 0l <: i16) (1s <<! 4l <: i16)
      (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16)
      (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16)
      (1s <<! 0l <: i16) (1s <<! 4l <: i16) (1s <<! 0l <: i16) (1s <<! 4l <: i16)
  in
  let coefficients_in_msb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients shift_lsbs_to_msbs
  in
  let coefficients_in_lsb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 4l coefficients_in_msb
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients_in_lsb
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((1s <<! 4l <: i16) -! 1s <: i16)
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let deserialize_5_ (bytes: t_Slice u8) =
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_set_epi8 (bytes.[ sz 9 ] <: u8) (bytes.[ sz 8 ] <: u8)
      (bytes.[ sz 8 ] <: u8) (bytes.[ sz 7 ] <: u8) (bytes.[ sz 7 ] <: u8) (bytes.[ sz 6 ] <: u8)
      (bytes.[ sz 6 ] <: u8) (bytes.[ sz 5 ] <: u8) (bytes.[ sz 4 ] <: u8) (bytes.[ sz 3 ] <: u8)
      (bytes.[ sz 3 ] <: u8) (bytes.[ sz 2 ] <: u8) (bytes.[ sz 2 ] <: u8) (bytes.[ sz 1 ] <: u8)
      (bytes.[ sz 1 ] <: u8) (bytes.[ sz 0 ] <: u8)
  in
  let coefficients_loaded:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi128_si256 coefficients
  in
  let coefficients_loaded:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_inserti128_si256 1l coefficients_loaded coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 coefficients_loaded
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 15y 14y 15y 14y 13y 12y 13y 12y 11y 10y 11y
          10y 9y 8y 9y 8y 7y 6y 7y 6y 5y 4y 5y 4y 3y 2y 3y 2y 1y 0y 1y 0y
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 0l <: i16) (1s <<! 5l <: i16)
          (1s <<! 2l <: i16) (1s <<! 7l <: i16) (1s <<! 4l <: i16) (1s <<! 9l <: i16)
          (1s <<! 6l <: i16) (1s <<! 11l <: i16) (1s <<! 0l <: i16) (1s <<! 5l <: i16)
          (1s <<! 2l <: i16) (1s <<! 7l <: i16) (1s <<! 4l <: i16) (1s <<! 9l <: i16)
          (1s <<! 6l <: i16) (1s <<! 11l <: i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 11l coefficients

open FStar.Tactics.V2
open Tactics.Utils

// let _ = get_bit_cast

let rw_get_bit_cast #t #u
  (x: int_t t) (nth: usize)
  : Lemma (requires v nth < bits u /\ v nth < bits u)
          (ensures eq2 #bit (get_bit (cast_mod #t #u x) nth) (if v nth < bits t then get_bit x nth else 0))
          [SMTPat (get_bit (cast_mod #t #u x) nth)]
  = ()

let rw_get_bit_shr #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t)
          (ensures eq2 #bit (get_bit (x >>! y) i )
                (if v i < bits t - v y
                    then get_bit x (mk_int (v i + v y))
                    else if signed t
                         then get_bit x (mk_int (bits t - 1))
                         else 0))
  = ()

// val bit_vec_to_int_t_lemma
//     #t (d: num_bits t) (bv: bit_vec d)
//     i
//   : Lemma (eq2 #bit (get_bit (bit_vec_to_int_t d bv) (sz i)) (bv i))

// val bit_vec_to_int_t_lemma2
//     #t (d: num_bits t) (bv: bit_vec d)
//     i
//   : Lemma (eq2 (get_bit (bit_vec_to_int_t d bv) (sz i)) (bv i))


#push-options "--compat_pre_core 0"
#push-options "--z3rlimit 90"
let serialize_1_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let lsb_to_msb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi16 15 vector
  in
  let low_msbs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 lsb_to_msb
  in
  let high_msbs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1 lsb_to_msb
  in
  let msbs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_packs_epi16 low_msbs high_msbs
  in
  let bits_packed:i32 = Libcrux_intrinsics.Avx2_extract.mm_movemask_epi8 msbs in
  let x = cast (bits_packed <: i32) <: u8 in
  let y = cast (bits_packed >>! 8l <: i32) <: u8 in
  let l = [x; y] in
  assert_norm (List.length l == 2);
  let arr: t_Array u8 (sz 2) = Seq.seq_of_list l in 
  let ll = bit_vec_of_int_t_array arr 8 in
  assume (forall (i: nat {i < 256}). vector i == (if i % 16 = 0 then vector i else 0));
  // HERE: the bound should be 16, not 8
  let _ = (forall (i: nat {i < 16}). ll i == vector (i * 16)) in
  assert (forall (i: nat {i < 16}). get_bit y (sz 7) == vector (i * 16)) by (
  // assert (forall (i: nat {i < 16}). ll i == vector (i * 16)) by (
    Tactics.Utils.prove_forall_nat_pointwise (fun _ ->
      norm [iota; primops; delta_only [`%cast; `%cast_tc_integers]];
      l_to_r [`rw_get_bit_cast];
      let light_norm () = norm [ iota; primops; zeta_full
           ; delta_only [`%bit_vec_of_int_t_array;`%bits;`%Lib.IntTypes.bits]
           ; delta_namespace ["FStar"]
      ] in
      light_norm ();
      Tactics.Seq.norm_index ();
      l_to_r[`rw_get_bit_cast; `bit_vec_to_int_t_lemma; `get_bit_shr];
      Tactics.MachineInts.(transform norm_machine_int_term);
      light_norm ();
      norm [primops; iota; zeta_full; delta_only [
        `%Libcrux_intrinsics.Avx2_extract.mm_movemask_epi8;
        `%BitVec.Intrinsics.mm_movemask_epi8;
      ]];
      l_to_r [`rw_get_bit_cast; `bit_vec_to_int_t_lemma; `get_bit_shr];
      let _ = rewrite_lhs () in
      flip ();
      trefl ();
      l_to_r [`rw_get_bit_shr];
      Tactics.MachineInts.(transform norm_machine_int_term);
      l_to_r [`rw_get_bit_cast; `bit_vec_to_int_t_lemma; `get_bit_shr];
      light_norm ();
      norm [primops; iota; zeta_full; delta_namespace ["Libcrux_intrinsics.Avx2_extract";"BitVec.Intrinsics"; "FStar"]];
      dump' "Goal:";
      smt_sync ();
      dump' "Success";
      smt ()
    )
  );
  Seq.seq_of_list l

let serialize_10_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 vector
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16) 1s
          (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16)
          1s (1s <<! 10l <: i16) 1s (1s <<! 10l <: i16) 1s
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 12l 0l 12l 0l 12l 0l 12l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 12l adjacent_4_combined
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 12y 11y
          10y 9y 8y 4y 3y 2y 1y 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) 12y 11y 10y 9y 8y 4y 3y 2y 1y
          0y
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let lower_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_8_combined
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
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
  let upper_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l adjacent_8_combined
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 10; Core.Ops.Range.f_end = sz 26 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
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
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 20 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 20)) Core.Array.t_TryFromSliceError)

let serialize_12_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 vector
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16) 1s
          (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16)
          1s (1s <<! 12l <: i16) 1s (1s <<! 12l <: i16) 1s
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 8l 0l 8l 0l 8l 0l 8l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 8l adjacent_4_combined
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) 13y 12y 11y 10y 9y 8y
          5y 4y 3y 2y 1y 0y (-1y) (-1y) (-1y) (-1y) 13y 12y 11y 10y 9y 8y 5y 4y 3y 2y 1y 0y
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let lower_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_8_combined
  in
  let upper_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l adjacent_8_combined
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
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
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
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
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 24 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 24)) Core.Array.t_TryFromSliceError)

let serialize_5_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 vector
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s
          (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s
          (1s <<! 5l <: i16) 1s (1s <<! 5l <: i16) 1s
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 22l 0l 22l 0l 22l 0l 22l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 22l adjacent_4_combined
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 8l adjacent_4_combined
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_8_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 12l 0l 0l 0l 12l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 12l adjacent_8_combined
  in
  let lower_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_8_combined
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
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
  let upper_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l adjacent_8_combined
  in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 21 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
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
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 10 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 10)) Core.Array.t_TryFromSliceError)

let serialize_4_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 vector
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
          (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
          (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) 12y 8y 4y 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) 12y 8y 4y 0y
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_8_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 0l 0l 0l 4l 0l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let combined:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 combined
  in
  let serialized:t_Array u8 (sz 16) =
    Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 serialized combined
  in
  Core.Result.impl__unwrap #(t_Array u8 (sz 8))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (sz 8))
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (sz 8)) Core.Array.t_TryFromSliceError)

let deserialize_11_ (bytes: t_Slice u8) =
  let output:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_deserialize_11_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      bytes
  in
  let array:t_Array i16 (sz 16) =
    Libcrux_ml_kem.Vector.Traits.f_to_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      output
  in
  Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_i16 (array <: t_Slice i16)

let serialize_11_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let array:t_Array i16 (sz 16) = Rust_primitives.Hax.repeat 0s (sz 16) in
  let array:t_Array i16 (sz 16) =
    Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_i16 array vector
  in
  let input:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_from_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      (array <: t_Slice i16)
  in
  Libcrux_ml_kem.Vector.Traits.f_serialize_11_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #FStar.Tactics.Typeclasses.solve
    input
