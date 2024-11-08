module Libcrux_ml_kem.Vector.Rej_sample_table
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_REJECTION_SAMPLE_SHUFFLE_TABLE: t_Array (t_Array u8 (sz 16)) (sz 256) =
  let list =
    [
      (let list =
          [
            255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 255uy; 255uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 14uy; 15uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 2uy; 3uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            0uy; 1uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 2uy; 3uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [
            4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy; 255uy;
            255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [0uy; 1uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      (let list =
          [2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy; 255uy; 255uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list);
      let list =
        [0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
      Rust_primitives.Hax.array_of_list 16 list
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 256);
  Rust_primitives.Hax.array_of_list 256 list
