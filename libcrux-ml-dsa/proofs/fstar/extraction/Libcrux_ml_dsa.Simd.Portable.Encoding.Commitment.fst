module Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

#set-options "--fuel 0 --ifuel 1 --z3rlimit 300 --z3version 4.13.3 --ext context_pruning"

let encode_4_ (coefficients: t_Slice i32) =
  let coefficient0:u8 = cast (coefficients.[ mk_usize 0 ] <: i32) <: u8 in
  let coefficient1:u8 = cast (coefficients.[ mk_usize 1 ] <: i32) <: u8 in
  (coefficient1 <<! mk_i32 4 <: u8) |. coefficient0

let encode_6_ (coefficients: t_Slice i32) =
  let coefficient0:u8 = cast (coefficients.[ mk_usize 0 ] <: i32) <: u8 in
  let coefficient1:u8 = cast (coefficients.[ mk_usize 1 ] <: i32) <: u8 in
  let coefficient2:u8 = cast (coefficients.[ mk_usize 2 ] <: i32) <: u8 in
  let coefficient3:u8 = cast (coefficients.[ mk_usize 3 ] <: i32) <: u8 in
  (coefficient1 <<! mk_i32 6 <: u8) |. coefficient0,
  (coefficient2 <<! mk_i32 4 <: u8) |. (coefficient1 >>! mk_i32 2 <: u8),
  (coefficient3 <<! mk_i32 2 <: u8) |. (coefficient2 >>! mk_i32 4 <: u8)
  <:
  (u8 & u8 & u8)

let serialize_4_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 2)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
      (fun serialized i ->
          let serialized:t_Slice u8 = serialized in
          let i:usize = i in
          Seq.length serialized == 4 /\
          (let inp =
              bit_vec_of_int_t_array #I32
                #(mk_usize 8)
                simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                4
            in
            let out = bit_vec_of_int_t_array #U8 #(mk_usize 4) serialized 8 in
            forall (n: nat{n < v i * 8}). out n == inp n))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              i
              (encode_4_ coefficients <: u8)
          in
          let _:Prims.unit =
            let inp =
              bit_vec_of_int_t_array #I32
                #(mk_usize 8)
                simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                4
            in
            let out = bit_vec_of_int_t_array #U8 #(mk_usize 4) serialized 8 in
            introduce forall (n: nat{n < 8}) . inp (v i * 8 + n) == out (v i * 8 + n)
            with (calc ( == ) {
                inp (v i * 8 + n);
                ( == ) { () }
                get_bit (Seq.index simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                      ((v i * 8 + n) / 4))
                  (sz ((v i * 8 + n) % 4));
                ( == ) { Math.Lemmas.division_addition_lemma n 4 (v i * 2) }
                get_bit (Seq.index simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                      (v i * 2 + n / 4))
                  (sz (n % 4));
                ( == ) { () }
                get_bit (Seq.index coefficients (n / 4)) (sz (n % 4));
                ( == ) { () }
                bit_vec_of_int_t_array #I32 #(mk_usize 2) coefficients 4 n;
                ( == ) { () }
                out (v i * 8 + n);
              })
          in
          serialized)
  in
  let _:Prims.unit = () <: Prims.unit in
  serialized

let serialize_6_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 4)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
      (fun serialized i ->
          let serialized:t_Slice u8 = serialized in
          let i:usize = i in
          Seq.length serialized == 6 /\
          (let inp =
              bit_vec_of_int_t_array #I32
                #(mk_usize 8)
                simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                6
            in
            let out = bit_vec_of_int_t_array #U8 #(mk_usize 6) serialized 8 in
            (forall (n: nat{n < v i * 24}). out n == inp n)))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let r0, r1, r2:(u8 & u8 & u8) = encode_6_ coefficients in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (mk_usize 3 *! i <: usize)
              r0
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 3 *! i <: usize) +! mk_usize 1 <: usize)
              r1
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 3 *! i <: usize) +! mk_usize 2 <: usize)
              r2
          in
          let _:Prims.unit =
            let inp =
              bit_vec_of_int_t_array #I32
                #(mk_usize 8)
                simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                6
            in
            let out = bit_vec_of_int_t_array #U8 #(mk_usize 6) serialized 8 in
            introduce forall (n: nat{n < 24}) . inp (v i * 24 + n) == out (v i * 24 + n)
            with (calc ( == ) {
                inp (v i * 24 + n);
                ( == ) { () }
                get_bit (Seq.index simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                      ((v i * 24 + n) / 6))
                  (sz ((v i * 24 + n) % 6));
                ( == ) { Math.Lemmas.division_addition_lemma n 6 (v i * 4) }
                get_bit (Seq.index simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                      (v i * 4 + n / 6))
                  (sz (n % 6));
                ( == ) { () }
                get_bit (Seq.index coefficients (n / 6)) (sz (n % 6));
                ( == ) { () }
                bit_vec_of_int_t_array #I32 #(mk_usize 4) coefficients 6 n;
                ( == ) { () }
                out (v i * 24 + n);
              })
          in
          serialized)
  in
  let _:Prims.unit = () <: Prims.unit in
  serialized

let serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    match cast (Core.Slice.impl__len #u8 serialized <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 4 -> serialize_4_ simd_unit serialized
    | Rust_primitives.Integers.MkInt 6 -> serialize_6_ simd_unit serialized
    | _ -> serialized
  in
  serialized
