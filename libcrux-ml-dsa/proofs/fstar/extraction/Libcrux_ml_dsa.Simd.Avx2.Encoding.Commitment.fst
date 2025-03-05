module Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Bitvec in
  ()

let pointwise (x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)) =
  Minicore.Abstractions.Bitvec.impl_7__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> x.[ mk_u64 0 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 1 -> x.[ mk_u64 1 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 2 -> x.[ mk_u64 2 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 3 -> x.[ mk_u64 3 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 4 -> x.[ mk_u64 4 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 5 -> x.[ mk_u64 5 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 6 -> x.[ mk_u64 6 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 7 -> x.[ mk_u64 7 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 8 -> x.[ mk_u64 8 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 9 -> x.[ mk_u64 9 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 10 -> x.[ mk_u64 10 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 11 -> x.[ mk_u64 11 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 12 -> x.[ mk_u64 12 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 13 -> x.[ mk_u64 13 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 14 -> x.[ mk_u64 14 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 15 -> x.[ mk_u64 15 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 16 -> x.[ mk_u64 16 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 17 -> x.[ mk_u64 17 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 18 -> x.[ mk_u64 18 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 19 -> x.[ mk_u64 19 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 20 -> x.[ mk_u64 20 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 21 -> x.[ mk_u64 21 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 22 -> x.[ mk_u64 22 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 23 -> x.[ mk_u64 23 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 24 -> x.[ mk_u64 24 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 25 -> x.[ mk_u64 25 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 26 -> x.[ mk_u64 26 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 27 -> x.[ mk_u64 27 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 28 -> x.[ mk_u64 28 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 29 -> x.[ mk_u64 29 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 30 -> x.[ mk_u64 30 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 31 -> x.[ mk_u64 31 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 32 -> x.[ mk_u64 32 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 33 -> x.[ mk_u64 33 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 34 -> x.[ mk_u64 34 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 35 -> x.[ mk_u64 35 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 36 -> x.[ mk_u64 36 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 37 -> x.[ mk_u64 37 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 38 -> x.[ mk_u64 38 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 39 -> x.[ mk_u64 39 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 40 -> x.[ mk_u64 40 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 41 -> x.[ mk_u64 41 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 42 -> x.[ mk_u64 42 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 43 -> x.[ mk_u64 43 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 44 -> x.[ mk_u64 44 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 45 -> x.[ mk_u64 45 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 46 -> x.[ mk_u64 46 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 47 -> x.[ mk_u64 47 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 48 -> x.[ mk_u64 48 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 49 -> x.[ mk_u64 49 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 50 -> x.[ mk_u64 50 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 51 -> x.[ mk_u64 51 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 52 -> x.[ mk_u64 52 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 53 -> x.[ mk_u64 53 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 54 -> x.[ mk_u64 54 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 55 -> x.[ mk_u64 55 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 56 -> x.[ mk_u64 56 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 57 -> x.[ mk_u64 57 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 58 -> x.[ mk_u64 58 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 59 -> x.[ mk_u64 59 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 60 -> x.[ mk_u64 60 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 61 -> x.[ mk_u64 61 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 62 -> x.[ mk_u64 62 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 63 -> x.[ mk_u64 63 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 64 -> x.[ mk_u64 64 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 65 -> x.[ mk_u64 65 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 66 -> x.[ mk_u64 66 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 67 -> x.[ mk_u64 67 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 68 -> x.[ mk_u64 68 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 69 -> x.[ mk_u64 69 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 70 -> x.[ mk_u64 70 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 71 -> x.[ mk_u64 71 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 72 -> x.[ mk_u64 72 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 73 -> x.[ mk_u64 73 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 74 -> x.[ mk_u64 74 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 75 -> x.[ mk_u64 75 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 76 -> x.[ mk_u64 76 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 77 -> x.[ mk_u64 77 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 78 -> x.[ mk_u64 78 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 79 -> x.[ mk_u64 79 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 80 -> x.[ mk_u64 80 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 81 -> x.[ mk_u64 81 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 82 -> x.[ mk_u64 82 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 83 -> x.[ mk_u64 83 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 84 -> x.[ mk_u64 84 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 85 -> x.[ mk_u64 85 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 86 -> x.[ mk_u64 86 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 87 -> x.[ mk_u64 87 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 88 -> x.[ mk_u64 88 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 89 -> x.[ mk_u64 89 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 90 -> x.[ mk_u64 90 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 91 -> x.[ mk_u64 91 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 92 -> x.[ mk_u64 92 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 93 -> x.[ mk_u64 93 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 94 -> x.[ mk_u64 94 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 95 -> x.[ mk_u64 95 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 96 -> x.[ mk_u64 96 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 97 -> x.[ mk_u64 97 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 98 -> x.[ mk_u64 98 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 99 -> x.[ mk_u64 99 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 100 -> x.[ mk_u64 100 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 101 -> x.[ mk_u64 101 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 102 -> x.[ mk_u64 102 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 103 -> x.[ mk_u64 103 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 104 -> x.[ mk_u64 104 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 105 -> x.[ mk_u64 105 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 106 -> x.[ mk_u64 106 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 107 -> x.[ mk_u64 107 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 108 -> x.[ mk_u64 108 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 109 -> x.[ mk_u64 109 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 110 -> x.[ mk_u64 110 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 111 -> x.[ mk_u64 111 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 112 -> x.[ mk_u64 112 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 113 -> x.[ mk_u64 113 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 114 -> x.[ mk_u64 114 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 115 -> x.[ mk_u64 115 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 116 -> x.[ mk_u64 116 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 117 -> x.[ mk_u64 117 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 118 -> x.[ mk_u64 118 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 119 -> x.[ mk_u64 119 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 120 -> x.[ mk_u64 120 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 121 -> x.[ mk_u64 121 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 122 -> x.[ mk_u64 122 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 123 -> x.[ mk_u64 123 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 124 -> x.[ mk_u64 124 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 125 -> x.[ mk_u64 125 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 126 -> x.[ mk_u64 126 ] <: Minicore.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 127 -> x.[ mk_u64 127 ] <: Minicore.Abstractions.Bit.t_Bit
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          Minicore.Abstractions.Bit.t_Bit)

let rw (x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)): Lemma (x == pointwise x) = admit ()

[@@FStar.Tactics.V2.(postprocess_with (fun () -> 
        let done = alloc false in
        ctrl_rewrite TopDown (fun _ -> if read done then (false, Skip) else (true, Continue))
                             (fun _ -> (fun () -> apply_lemma_rw (`rw); write done true)
                                       `or_else` trefl);
        norm [primops; iota; delta_namespace ["Core"; "Libcrux_ml_dsa"; "Libcrux_intrinsics"; "Minicore"; "FStar.FunctionalExtensionality"; "Rust_primitives"]; zeta_full];
        compute ();
        norm [primops; iota; delta; zeta_full];
        trefl ()
        ))]

let serialize_4_aux (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  let adjacent_2_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Minicore.Arch.X86.Extra.mm256_sllv_epi32_u32 simd_unit
      (mk_u32 0)
      (mk_u32 28)
      (mk_u32 0)
      (mk_u32 28)
      (mk_u32 0)
      (mk_u32 28)
      (mk_u32 0)
      (mk_u32 28)
  in
  let x:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) = adjacent_2_combined in
  let adjacent_2_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (mk_i32 28) adjacent_2_combined
  in
  let adjacent_4_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Minicore.Arch.X86.Extra.mm256_permutevar8x32_epi32_u32 adjacent_2_combined
      (mk_u32 0)
      (mk_u32 0)
      (mk_u32 0)
      (mk_u32 0)
      (mk_u32 6)
      (mk_u32 2)
      (mk_u32 4)
      (mk_u32 0)
  in
  let adjacent_4_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_4_combined
  in
  Minicore.Arch.X86.Extra.mm_shuffle_epi8_u8 adjacent_4_combined (mk_u8 240) (mk_u8 240) (mk_u8 240)
    (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240)
    (mk_u8 240) (mk_u8 12) (mk_u8 4) (mk_u8 8) (mk_u8 0)

let serialize_4_ (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
  serialize_4_aux simd_unit

let serialize (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) (out: t_Slice u8) =
  let serialized:t_Array u8 (mk_usize 19) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 19) in
  let out, serialized:(t_Slice u8 & t_Array u8 (mk_usize 19)) =
    match cast (Core.Slice.impl__len #u8 out <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 4 ->
      let adjacent_2_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
              (mk_i32 28)
              (mk_i32 0)
              (mk_i32 28)
              (mk_i32 0)
              (mk_i32 28)
              (mk_i32 0)
              (mk_i32 28)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let adjacent_2_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (mk_i32 28) adjacent_2_combined
      in
      let adjacent_4_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_2_combined
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
              (mk_i32 0)
              (mk_i32 0)
              (mk_i32 0)
              (mk_i32 6)
              (mk_i32 2)
              (mk_i32 4)
              (mk_i32 0)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let adjacent_4_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
        Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_4_combined
      in
      let adjacent_4_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
        Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 adjacent_4_combined
          (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 (mk_u8 240) (mk_u8 240) (mk_u8 240)
              (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240)
              (mk_u8 240) (mk_u8 240) (mk_u8 12) (mk_u8 4) (mk_u8 8) (mk_u8 0)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      in
      let serialized:t_Array u8 (mk_usize 19) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
          ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
            <:
            Core.Ops.Range.t_Range usize)
          (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                    Core.Ops.Range.f_start = mk_usize 0;
                    Core.Ops.Range.f_end = mk_usize 16
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              adjacent_4_combined
            <:
            t_Slice u8)
      in
      let out:t_Slice u8 =
        Core.Slice.impl__copy_from_slice #u8
          out
          (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 4 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      in
      out, serialized <: (t_Slice u8 & t_Array u8 (mk_usize 19))
    | Rust_primitives.Integers.MkInt 6 ->
      let adjacent_2_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 simd_unit
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
              (mk_i32 26)
              (mk_i32 0)
              (mk_i32 26)
              (mk_i32 0)
              (mk_i32 26)
              (mk_i32 0)
              (mk_i32 26)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let adjacent_2_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (mk_i32 26) adjacent_2_combined
      in
      let adjacent_3_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
              (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
              (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 9) (mk_i8 8) (mk_i8 1) (mk_i8 0)
              (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
              (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
              (mk_i8 9) (mk_i8 8) (mk_i8 1) (mk_i8 0)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let adjacent_3_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 adjacent_3_combined
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 1) (mk_i16 1) (mk_i16 1)
              (mk_i16 1) (mk_i16 1) (mk_i16 1) (mk_i16 1) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1)
              (mk_i16 1) (mk_i16 1) (mk_i16 1) (mk_i16 1) (mk_i16 1) (mk_i16 1)
              (mk_i16 1 <<! mk_i32 4 <: i16)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let adjacent_3_combined:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
        Libcrux_intrinsics.Avx2_extract.mm256_srlv_epi32 adjacent_3_combined
          (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
              (mk_i32 0)
              (mk_i32 0)
              (mk_i32 4)
              (mk_i32 0)
              (mk_i32 0)
              (mk_i32 0)
              (mk_i32 4)
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      in
      let lower_3_:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
        Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_3_combined
      in
      let serialized:t_Array u8 (mk_usize 19) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
          ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
            <:
            Core.Ops.Range.t_Range usize)
          (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                    Core.Ops.Range.f_start = mk_usize 0;
                    Core.Ops.Range.f_end = mk_usize 16
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              lower_3_
            <:
            t_Slice u8)
      in
      let upper_3_:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
        Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) adjacent_3_combined
      in
      let serialized:t_Array u8 (mk_usize 19) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
          ({ Core.Ops.Range.f_start = mk_usize 3; Core.Ops.Range.f_end = mk_usize 19 }
            <:
            Core.Ops.Range.t_Range usize)
          (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                    Core.Ops.Range.f_start = mk_usize 3;
                    Core.Ops.Range.f_end = mk_usize 19
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              upper_3_
            <:
            t_Slice u8)
      in
      let out:t_Slice u8 =
        Core.Slice.impl__copy_from_slice #u8
          out
          (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 6 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      in
      out, serialized <: (t_Slice u8 & t_Array u8 (mk_usize 19))
    | _ -> out, serialized <: (t_Slice u8 & t_Array u8 (mk_usize 19))
  in
  out
