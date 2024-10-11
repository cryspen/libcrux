module Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Shuffle_table
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_SHUFFLE_TABLE: t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
  (Rust_primitives.mk_usize 16) =
  let list =
    [
      (let list =
          [
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 0; Rust_primitives.mk_u8 1; Rust_primitives.mk_u8 2;
            Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 4; Rust_primitives.mk_u8 5; Rust_primitives.mk_u8 6;
            Rust_primitives.mk_u8 7; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 0; Rust_primitives.mk_u8 1; Rust_primitives.mk_u8 2;
            Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 4; Rust_primitives.mk_u8 5;
            Rust_primitives.mk_u8 6; Rust_primitives.mk_u8 7; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 8; Rust_primitives.mk_u8 9; Rust_primitives.mk_u8 10;
            Rust_primitives.mk_u8 11; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 0; Rust_primitives.mk_u8 1; Rust_primitives.mk_u8 2;
            Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 8; Rust_primitives.mk_u8 9;
            Rust_primitives.mk_u8 10; Rust_primitives.mk_u8 11; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 4; Rust_primitives.mk_u8 5; Rust_primitives.mk_u8 6;
            Rust_primitives.mk_u8 7; Rust_primitives.mk_u8 8; Rust_primitives.mk_u8 9;
            Rust_primitives.mk_u8 10; Rust_primitives.mk_u8 11; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 0; Rust_primitives.mk_u8 1; Rust_primitives.mk_u8 2;
            Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 4; Rust_primitives.mk_u8 5;
            Rust_primitives.mk_u8 6; Rust_primitives.mk_u8 7; Rust_primitives.mk_u8 8;
            Rust_primitives.mk_u8 9; Rust_primitives.mk_u8 10; Rust_primitives.mk_u8 11;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 12; Rust_primitives.mk_u8 13; Rust_primitives.mk_u8 14;
            Rust_primitives.mk_u8 15; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 0; Rust_primitives.mk_u8 1; Rust_primitives.mk_u8 2;
            Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 12; Rust_primitives.mk_u8 13;
            Rust_primitives.mk_u8 14; Rust_primitives.mk_u8 15; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 4; Rust_primitives.mk_u8 5; Rust_primitives.mk_u8 6;
            Rust_primitives.mk_u8 7; Rust_primitives.mk_u8 12; Rust_primitives.mk_u8 13;
            Rust_primitives.mk_u8 14; Rust_primitives.mk_u8 15; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 0; Rust_primitives.mk_u8 1; Rust_primitives.mk_u8 2;
            Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 4; Rust_primitives.mk_u8 5;
            Rust_primitives.mk_u8 6; Rust_primitives.mk_u8 7; Rust_primitives.mk_u8 12;
            Rust_primitives.mk_u8 13; Rust_primitives.mk_u8 14; Rust_primitives.mk_u8 15;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 8; Rust_primitives.mk_u8 9; Rust_primitives.mk_u8 10;
            Rust_primitives.mk_u8 11; Rust_primitives.mk_u8 12; Rust_primitives.mk_u8 13;
            Rust_primitives.mk_u8 14; Rust_primitives.mk_u8 15; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 0; Rust_primitives.mk_u8 1; Rust_primitives.mk_u8 2;
            Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 8; Rust_primitives.mk_u8 9;
            Rust_primitives.mk_u8 10; Rust_primitives.mk_u8 11; Rust_primitives.mk_u8 12;
            Rust_primitives.mk_u8 13; Rust_primitives.mk_u8 14; Rust_primitives.mk_u8 15;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            Rust_primitives.mk_u8 4; Rust_primitives.mk_u8 5; Rust_primitives.mk_u8 6;
            Rust_primitives.mk_u8 7; Rust_primitives.mk_u8 8; Rust_primitives.mk_u8 9;
            Rust_primitives.mk_u8 10; Rust_primitives.mk_u8 11; Rust_primitives.mk_u8 12;
            Rust_primitives.mk_u8 13; Rust_primitives.mk_u8 14; Rust_primitives.mk_u8 15;
            Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255; Rust_primitives.mk_u8 255;
            Rust_primitives.mk_u8 255
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      let list =
        [
          Rust_primitives.mk_u8 0; Rust_primitives.mk_u8 1; Rust_primitives.mk_u8 2;
          Rust_primitives.mk_u8 3; Rust_primitives.mk_u8 4; Rust_primitives.mk_u8 5;
          Rust_primitives.mk_u8 6; Rust_primitives.mk_u8 7; Rust_primitives.mk_u8 8;
          Rust_primitives.mk_u8 9; Rust_primitives.mk_u8 10; Rust_primitives.mk_u8 11;
          Rust_primitives.mk_u8 12; Rust_primitives.mk_u8 13; Rust_primitives.mk_u8 14;
          Rust_primitives.mk_u8 15
        ]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
      Rust_primitives.Hax.array_of_list 16 list
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
  Rust_primitives.Hax.array_of_list 16 list

val is_bit_set (number: usize) (bit_position: u8)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val generate_shuffle_table: Prims.unit
  -> Prims.Pure (t_Array (t_Array u8 (Rust_primitives.mk_usize 16)) (Rust_primitives.mk_usize 16))
      Prims.l_True
      (fun _ -> Prims.l_True)
