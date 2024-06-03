module Libcrux_polynomials_avx2.Sampling
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

let rejection_sample (input: t_Slice u8) (output: t_Slice i16) : (t_Slice i16 & usize) =
  let field_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 Libcrux_traits.v_FIELD_MODULUS
  in
  let potential_coefficients:u8 = Libcrux_polynomials_avx2.Serialize.deserialize_12_ input in
  let compare_with_field_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_cmpgt_epi16 field_modulus
      potential_coefficients
  in
  let good:t_Array u8 (sz 2) =
    Libcrux_polynomials_avx2.Serialize.serialize_1_ compare_with_field_modulus
  in
  let lower_shuffles:t_Array u8 (sz 16) =
    v_REJECTION_SAMPLE_SHUFFLE_TABLE.[ cast (good.[ sz 0 ] <: u8) <: usize ]
  in
  let lower_shuffles:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_loadu_si128 (Rust_primitives.unsize lower_shuffles

        <:
        t_Slice u8)
  in
  let lower_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_castsi256_si128 potential_coefficients
  in
  let lower_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_shuffle_epi8 lower_coefficients lower_shuffles
  in
  let output:t_Slice i16 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range output
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_si128 (output.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = sz 8
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          lower_coefficients
        <:
        t_Slice i16)
  in
  let sampled_count:usize =
    cast (Core.Num.impl__u8__count_ones (good.[ sz 0 ] <: u8) <: u32) <: usize
  in
  let upper_shuffles:t_Array u8 (sz 16) =
    v_REJECTION_SAMPLE_SHUFFLE_TABLE.[ cast (good.[ sz 1 ] <: u8) <: usize ]
  in
  let upper_shuffles:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_loadu_si128 (Rust_primitives.unsize upper_shuffles

        <:
        t_Slice u8)
  in
  let upper_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_extracti128_si256 1l potential_coefficients
  in
  let upper_coefficients:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_shuffle_epi8 upper_coefficients upper_shuffles
  in
  let output:t_Slice i16 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range output
      ({
          Core.Ops.Range.f_start = sampled_count;
          Core.Ops.Range.f_end = sampled_count +! sz 8 <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_storeu_si128 (output.[ {
                Core.Ops.Range.f_start = sampled_count;
                Core.Ops.Range.f_end = sampled_count +! sz 8 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          upper_coefficients
        <:
        t_Slice i16)
  in
  let hax_temp_output:usize =
    sampled_count +! (cast (Core.Num.impl__u8__count_ones (good.[ sz 1 ] <: u8) <: u32) <: usize)
  in
  output, hax_temp_output <: (t_Slice i16 & usize)
