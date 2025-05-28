module Libcrux_ml_dsa.Simd.Avx2.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

open Spec.Intrinsics

let change_interval (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let interval_end:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1 <<!
        (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! mk_usize 1 <: usize)
        <:
        i32)
  in
  Libcrux_intrinsics.Avx2.mm256_sub_epi32 interval_end simd_unit

let mm256_add_epi64_lemma_smtpat lhs rhs (i: u64 {v i < 256})
  : Lemma
    (requires 
      forall (j:nat{j < v i % 64}). Core_models.Abstractions.Bit.Bit_Zero? lhs.(mk_int ((v i / 64) * 64 + j))
                         \/ Core_models.Abstractions.Bit.Bit_Zero? rhs.(mk_int ((v i / 64) * 64 + j))
    )
    (ensures  
      (Core_models.Abstractions.Bit.Bit_Zero? lhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == rhs.(i)) /\
      (Core_models.Abstractions.Bit.Bit_Zero? rhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == lhs.(i))
    )
    [SMTPat (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i)]
    = mm256_add_epi64_lemma lhs rhs i

#push-options "--fuel 0 --ifuel 0 --split_queries always --z3rlimit 500"
// #push-options "--fuel 0 --ifuel 0 --z3rlimit 5000 --z3smtopt '(set-option :smt.arith.nl false)'"
let serialize
  (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) {
    forall i. v i % 32 >= 13 ==> simd_unit.(i) == Core_models.Abstractions.Bit.Bit_Zero
  })
  (out: t_Slice u8)=
  let serialized:t_Array u8 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16) in
  // let simd_unit:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = change_interval simd_unit in
  // assert (Core_models.Abstractions.Bit.Bit_Zero? simd_unit.(mk_int 109));
  // admit ()
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 19) adjacent_2_combined
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 4)
          (mk_i32 2)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  // assert (adjacent_4_combined.(mk_int (103 + 6)) == simd_unit.(mk_int (205 + 19)));
  // assert (adjacent_4_combined.(mk_int (32 * 3 + 13)) == adjacent_2_combined.(mk_int (32 * 6 + 13)));
  // assert (adjacent_4_combined.(mk_int (32 + 26)) == adjacent_2_combined.(mk_int (64 + 26)));
  // assert (adjacent_4_combined.(mk_int (32 + 31)) == adjacent_2_combined.(mk_int (64 + 31)));
  // assert (adjacent_4_combined.(mk_int 64) == adjacent_2_combined.(mk_int 128));
  // assert (adjacent_4_combined.(mk_int 96) == adjacent_2_combined.(mk_int 192));
  // let i = 5 in
  // assert (adjacent_4_combined.(mk_int (32 + 26 + i)) == adjacent_2_combined.(mk_int (64 + 26 + i)));
  // admit ()
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 6) adjacent_4_combined
  in
  // assert(Core_models.Abstractions.Bit.Bit_Zero? adjacent_4_combined.(mk_int 53));
  let second_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_bsrli_epi128 (mk_i32 8) adjacent_4_combined
  in
  // assert (adjacent_4_combined.(mk_int 64) == simd_unit.(mk_int 128));
  // assert (second_4_combined.(mk_int 0) == simd_unit.(mk_int 128));
  // assert (second_4_combined.(mk_int 0) == Core_models.Abstractions.Bit.Bit_Zero);
  // assert (simd_unit.(mk_int 128) == second_4_combined.(mk_int 0));
  // admit ()
  let least_12_bits_shifted_up:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_slli_epi64 (mk_i32 52) second_4_combined
  in
  // assert (adjacent_4_combined.(mk_int 76) == simd_unit.(mk_int (140)));
  // assert (Core_models.Abstractions.Bit.Bit_Zero? least_12_bits_shifted_up.(mk_int 76));
  // admit ()
  // assert_spinoff (forall (i: _ {v i >= 0 /\ v i < 116}). Core_models.Abstractions.Bit.Bit_Zero? least_12_bits_shifted_up.(i) \/
  //                                                 Core_models.Abstractions.Bit.Bit_Zero? adjacent_4_combined.(i));
  // assert_spinoff (forall (i: _ {v i >= 122 /\ v i < 128}). Core_models.Abstractions.Bit.Bit_Zero? least_12_bits_shifted_up.(i) \/
  //                                                 Core_models.Abstractions.Bit.Bit_Zero? adjacent_4_combined.(i));
  // assert_spinoff (forall (i: _ {v i >= 128 /\ v i < 244}). Core_models.Abstractions.Bit.Bit_Zero? least_12_bits_shifted_up.(i) \/
  //                                                 Core_models.Abstractions.Bit.Bit_Zero? adjacent_4_combined.(i));
  // assert_spinoff (forall (i: _ {v i >= 250 /\ v i < 256}). Core_models.Abstractions.Bit.Bit_Zero? least_12_bits_shifted_up.(i) \/
  //                                                 Core_models.Abstractions.Bit.Bit_Zero? adjacent_4_combined.(i));
  let bits_sequential:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi64 adjacent_4_combined least_12_bits_shifted_up
  in
  // assert (forall i.
  //   Core_models.Abstractions.Bit.Bit_Zero? adjacent_4_combined.(i) \/
  //   Core_models.Abstractions.Bit.Bit_Zero? least_12_bits_shifted_up.(i)
  // );
  // assert (bits_sequential.(mk_int 53) == simd_unit.(mk_int (129)));
  // // assert (
  // //   (least_12_bits_shifted_up).(mk_int (53)) == simd_unit.(mk_int (129))
  // // );
  // admit ()
  // assert (bits_sequential.(mk_int 76) == simd_unit.(mk_int (140)));
  let bits_sequential0 = bits_sequential in
  let shifts  =(Libcrux_intrinsics.Avx2.mm256_set_epi64x (mk_i64 0) (mk_i64 0) (mk_i64 12) (mk_i64 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) in
  let bits_sequential:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi64 bits_sequential shifts
  in
        
  // assert (Core_models.Abstractions.Bit.Bit_Zero? bits_sequential.(mk_int 64));
  // assert (bits_sequential0.(mk_int 76) == bits_sequential.(mk_int 64));
  // assert (bits_sequential.(mk_int 64) == simd_unit.(mk_int (140)));
  // admit ()
  let bits_sequential:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 bits_sequential
  in
  let prop (i: nat{i < 8})
    = forall (j: nat {j < 13}). (bits_sequential).(mk_int (i * 13 + j)) == simd_unit.(mk_int (i * 32 + j))
  in
  assert (
   forall (i: nat {i < 8}).
    forall (j: nat {j < 13}).
      (bits_sequential).(mk_int (i * 13 + j)) == simd_unit.(mk_int (i * 32 + j))
  );
  bits_sequential
#pop-options

let lemma_spec (i:nat{i < 8}) = 
  (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) {
    forall i. v i % 32 >= 13 ==> simd_unit.(i) == Core_models.Abstractions.Bit.Bit_Zero
  }) -> out:_ -> Lemma (
    forall (j: nat {j < 13}).
      (serialize simd_unit out).(mk_int (i * 13 + j)) == simd_unit.(mk_int (i * 32 + j))
  )

let l0: lemma_spec 0 = fun _ _ -> ()
let l1: lemma_spec 1 = fun _ _ -> ()
let l2: lemma_spec 2 = fun _ _ -> ()
let l3: lemma_spec 3 = fun _ _ -> ()
#push-options "--fuel 0 --ifuel 0 --z3rlimit 5000 --z3smtopt '(set-option :smt.arith.nl false)'"
// let l4: lemma_spec 4 = fun _ _ -> ()
let l5: lemma_spec 5 = fun _ _ -> admit ()
let l6: lemma_spec 6 = fun _ _ -> admit ()
let l7: lemma_spec 7 = fun _ _ -> admit ()

let lemma i: lemma_spec i = fun a b ->
  match i with | 0 -> l0 a b
               | 1 -> l1 a b
               | 2 -> l2 a b
               | 3 -> l3 a b
               | 4 -> l4 a b
               | 5 -> l5 a b
               | 6 -> l6 a b
               | 7 -> l7 a b

#push-options "--fuel 0 --ifuel 0 --z3rlimit 5000 --z3smtopt '(set-option :smt.arith.nl false)'"
let serialize'
  (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) {
    forall i. v i % 32 >= 13 ==> simd_unit.(i) == Core_models.Abstractions.Bit.Bit_Zero
  }): Lemma () =
    let out = serialize simd_unit out in
    assert (forall (i: nat {i < 8}) (j: nat {j < 13}).
      out.(mk_int (i * 13 + j)) == simd_unit.(mk_int (i * 32 + j))
    )
  
  // assert (bits_sequential.(mk_int 52) == adjacent_4_combined0.(mk_int (52 + 6)));
  // assert (bits_sequential.(mk_int 52) == adjacent_2_combined.(mk_int 90));
  // assert (bits_sequential.(mk_int 52) == simd_unit.(mk_int (90 + 19)));
  // assert (bits_sequential.(mk_int 52) == simd_unit.(mk_int 128));
  // admit ()
  // assert (bits_sequential.(mk_int 52) == simd_unit.(mk_int 128));
  // assert (bits_sequential.(mk_int (64)) == simd_unit.(mk_int (128)));
  
  // assert (bits_sequential.(mk_int (96)) == simd_unit.(mk_int (192 + 6)));
  // assert (bits_sequential.(mk_int (96 + 6)) == simd_unit.(mk_int (192 + 6 + 6)));
  // assert (bits_sequential.(mk_int (103)) == adjacent_4_combined0.(mk_int (103 + 6)));
  // assert (bits_sequential.(mk_int (103)) == simd_unit.(mk_int (224)));
  // assert (bits_sequential.(mk_int (103)) == simd_unit.(mk_int (205 + 0)));
  // assert (bits_sequential.(mk_int (96)) == adjacent_4_combined0.(mk_int (96 + 6)));
  
  // let i0 = 5 in
  // FROM 0 TO 51 INCLUDED!


  // assert (forall (i: nat {i < 6}) (j: nat {j < 13}).
  //   bits_sequential.(mk_int (i * 13 + j)) == simd_unit.(mk_int (i * 32 + j))
  // );
  // assert (forall (i: _{v i < 104}). bits_sequential.(i) == simd_unit.(mk_int ((v i / 13) * 32 + v i % 13)));
  // admit ()
  
  // assert (let i = mk_u64 51 in bits_sequential.(i) == simd_unit.(mk_int (32 + 12)));
  
  // assert (let i = mk_u64 52 in bits_sequential.(i) == simd_unit.(mk_int ((v i / 13) * 32 + v i % 13)));
  // assert (let i = mk_u64 60 in bits_sequential.(i) == simd_unit.(mk_int ((v i / 13) * 32 + v i % 13)));
  // assert (let i = mk_u64 (i0 + 1) in bits_sequential.(i) == simd_unit.(mk_int ((v i / 13) * 32 + v i % 13)));
  // assert (let i = mk_u64 (i0 + 2) in bits_sequential.(i) == simd_unit.(mk_int ((v i / 13) * 32 + v i % 13)));
  // let serialized:t_Array u8 (mk_usize 16) =
  //   Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 serialized bits_sequential
  // in
  // let out:t_Slice u8 =
  //   Core.Slice.impl__copy_from_slice #u8
  //     out
  //     (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 13 }
  //         <:
  //         Core.Ops.Range.t_Range usize ]
  //       <:
  //       t_Slice u8)
  // in
  // out

let deserialize__v_COEFFICIENT_MASK: i32 = (mk_i32 1 <<! mk_i32 13 <: i32) -! mk_i32 1

let deserialize
      (serialized: t_Slice u8)
      (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 serialized, mk_usize 13 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let serialized_extended:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16)
  in
  let serialized_extended:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized_extended
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 13 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized_extended.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 13
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          serialized
        <:
        t_Slice u8)
  in
  let serialized:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm_loadu_si128 (serialized_extended <: t_Slice u8)
  in
  let serialized:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set_m128i serialized serialized
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11)
          (mk_i8 (-1)) (mk_i8 11) (mk_i8 10) (mk_i8 9) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 9) (mk_i8 8)
          (mk_i8 (-1)) (mk_i8 8) (mk_i8 7) (mk_i8 6) (mk_i8 (-1)) (mk_i8 6) (mk_i8 5) (mk_i8 4)
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 4) (mk_i8 3) (mk_i8 (-1)) (mk_i8 3) (mk_i8 2) (mk_i8 1)
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 1) (mk_i8 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 3)
          (mk_i32 6)
          (mk_i32 1)
          (mk_i32 4)
          (mk_i32 7)
          (mk_i32 2)
          (mk_i32 5)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize__v_COEFFICIENT_MASK
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = change_interval coefficients in
  out
