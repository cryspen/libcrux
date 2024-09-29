module BitVec.Intrinsics.TestShuffle

open Rust_primitives
open FStar.Mul
open BitVec.Utils
open BitVec.Intrinsics

assume val stuck: #a:Type -> #b:Type -> a -> b

let index64 l (i: nat {i < List.Tot.length l}) =
  match l with
  | [x0;x1;x2;x3] -> 
    (match i with
    | 0 -> x0   | 1 -> x1   | 2 -> x2   | 3 -> x3)
  | [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;x17;x18;x19;x20;x21;x22;x23;x24;x25;x26;x27;x28;x29;x30;x31;x32;x33;x34;x35;x36;x37;x38;x39;x40;x41;x42;x43;x44;x45;x46;x47;x48;x49;x50;x51;x52;x53;x54;x55;x56;x57;x58;x59;x60;x61;x62;x63] -> 
    (match i with
    | 0 -> x0   | 1 -> x1   | 2 -> x2   | 3 -> x3   | 4 -> x4   | 5 -> x5   | 6 -> x6   | 7 -> x7   | 8 -> x8   | 9 -> x9   | 10 -> x10 | 11 -> x11 | 12 -> x12 | 13 -> x13 | 14 -> x14 | 15 -> x15 
    | 16 -> x16 | 17 -> x17 | 18 -> x18 | 19 -> x19 | 20 -> x20 | 21 -> x21 | 22 -> x22 | 23 -> x23 | 24 -> x24 | 25 -> x25 | 26 -> x26 | 27 -> x27 | 28 -> x28 | 29 -> x29 | 30 -> x30 | 31 -> x31 
    | 32 -> x32 | 33 -> x33 | 34 -> x34 | 35 -> x35 | 36 -> x36 | 37 -> x37 | 38 -> x38 | 39 -> x39 | 40 -> x40 | 41 -> x41 | 42 -> x42 | 43 -> x43 | 44 -> x44 | 45 -> x45 | 46 -> x46 | 47 -> x47 
    | 48 -> x48 | 49 -> x49 | 50 -> x50 | 51 -> x51 | 52 -> x52 | 53 -> x53 | 54 -> x54 | 55 -> x55 | 56 -> x56 | 57 -> x57 | 58 -> x58 | 59 -> x59 | 60 -> x60 | 61 -> x61 | 62 -> x62 | 63 -> x63)
  | _ -> stuck "index"

assume val nth: list bit -> nat -> bit

let bv_of_list_list (n: pos) (l: list (l: list bit {List.Tot.length l == n})): bit_vec (List.Tot.length l * n)
  = mk_bv (fun i -> nth (index64 l (i / n)) (i % n))

let z: l: list bit {List.Tot.length l == 4} = [0;0;0;0]

type result #t0 #t1 #t2 #t3 #t4 = {
     vector: t0;
     adjacent_2_combined: t1;
     adjacent_8_combined: t2;
     combined': t3;
     combined: t4;
  }

// /// We view `x` as a sequence of pairs of 16 bits, of the shape
// /// `(0b0…0a₁…aₙ, 0b0…0b₁…bₙ)`: only the last `n` bits are non-zero.
// /// We output a sequence of 32 bits `0b0…0b₁…bₙa₁…aₙ`.
// let mm256_madd_epi16_specialized' (x: bit_vec 256) (n: nat {n < 16}): bit_vec 256 =
//   mk_bv (fun i -> let j = i % 32 in
//                // `x i` is the `j`th bit in the `i/32`th pair of 16 bits `(0b0…0a₁…aₙ, 0b0…0b₁…bₙ)`
//                // we want to construct the `j`th bit of `0b0…0b₁…bₙa₁…aₙ`
//                let is_zero = 
//                  // `|b₁…bₙa₁…aₙ| = n * 2`: if we're above that, we want to produce the bit `0`
//                  j >= n * 2
//                in
//                if is_zero
//                then 0
//                else if j < n
//                     then x i        // we want to produce the bit `aⱼ`
//                     else 
//                       // the bit from `b` is in the second item of the pair `(0b0…0a₁…aₙ, 0b0…0b₁…bₙ)`
//                       x (i - n + 16)
//          )

// let mm256_permutevar8x32_epi32_i32 (a: bit_vec 256) (b: list _ {List.Tot.length b == 8}): bit_vec 256 =
//   mk_bv (fun i ->
//      let j = i / 32 in
//      let index = (List.Tot.index b (7 - j) % 8) * 32 in
//      a (index + i % 32))

let serialize_4_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mm256_madd_epi16_specialized' vector 4
    // Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 vector
    //   (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
    //       (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
    //       (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
    //     <:
    //     Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) 12y 8y 4y 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) 12y 8y 4y 0y
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let combined':Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mm256_permutevar8x32_epi32_i32 adjacent_8_combined (mk_list_8 0 0 0 0 0 0 4 0)
    // Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_8_combined
    //   (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 0l 0l 0l 0l 0l 0l 4l 0l
    //     <:
    //     Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let combined:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 combined'
  in
  {vector; adjacent_2_combined; adjacent_8_combined; combined'; combined}

let map256 (f: (i: nat {i < 256}) -> bit) = [f 0;f 1;f 2;f 3;f 4;f 5;f 6;f 7;f 8;f 9;f 10;f 11;f 12;f 13;f 14;f 15;f 16;f 17;f 18;f 19;f 20;f 21;f 22;f 23;f 24;f 25;f 26;f 27;f 28;f 29;f 30;f 31;f 32;f 33;f 34;f 35;f 36;f 37;f 38;f 39;f 40;f 41;f 42;f 43;f 44;f 45;f 46;f 47;f 48;f 49;f 50;f 51;f 52;f 53;f 54;f 55;f 56;f 57;f 58;f 59;f 60;f 61;f 62;f 63;f 64;f 65;f 66;f 67;f 68;f 69;f 70;f 71;f 72;f 73;f 74;f 75;f 76;f 77;f 78;f 79;f 80;f 81;f 82;f 83;f 84;f 85;f 86;f 87;f 88;f 89;f 90;f 91;f 92;f 93;f 94;f 95;f 96;f 97;f 98;f 99;f 100;f 101;f 102;f 103;f 104;f 105;f 106;f 107;f 108;f 109;f 110;f 111;f 112;f 113;f 114;f 115;f 116;f 117;f 118;f 119;f 120;f 121;f 122;f 123;f 124;f 125;f 126;f 127;f 128;f 129;f 130;f 131;f 132;f 133;f 134;f 135;f 136;f 137;f 138;f 139;f 140;f 141;f 142;f 143;f 144;f 145;f 146;f 147;f 148;f 149;f 150;f 151;f 152;f 153;f 154;f 155;f 156;f 157;f 158;f 159;f 160;f 161;f 162;f 163;f 164;f 165;f 166;f 167;f 168;f 169;f 170;f 171;f 172;f 173;f 174;f 175;f 176;f 177;f 178;f 179;f 180;f 181;f 182;f 183;f 184;f 185;f 186;f 187;f 188;f 189;f 190;f 191;f 192;f 193;f 194;f 195;f 196;f 197;f 198;f 199;f 200;f 201;f 202;f 203;f 204;f 205;f 206;f 207;f 208;f 209;f 210;f 211;f 212;f 213;f 214;f 215;f 216;f 217;f 218;f 219;f 220;f 221;f 222;f 223;f 224;f 225;f 226;f 227;f 228;f 229;f 230;f 231;f 232;f 233;f 234;f 235;f 236;f 237;f 238;f 239;f 240;f 241;f 242;f 243;f 244;f 245;f 246;f 247;f 248;f 249;f 250;f 251;f 252;f 253;f 254;f 255]
let map128 (f: (i: nat {i < 128}) -> bit) = [f 0;f 1;f 2;f 3;f 4;f 5;f 6;f 7;f 8;f 9;f 10;f 11;f 12;f 13;f 14;f 15;f 16;f 17;f 18;f 19;f 20;f 21;f 22;f 23;f 24;f 25;f 26;f 27;f 28;f 29;f 30;f 31;f 32;f 33;f 34;f 35;f 36;f 37;f 38;f 39;f 40;f 41;f 42;f 43;f 44;f 45;f 46;f 47;f 48;f 49;f 50;f 51;f 52;f 53;f 54;f 55;f 56;f 57;f 58;f 59;f 60;f 61;f 62;f 63;f 64;f 65;f 66;f 67;f 68;f 69;f 70;f 71;f 72;f 73;f 74;f 75;f 76;f 77;f 78;f 79;f 80;f 81;f 82;f 83;f 84;f 85;f 86;f 87;f 88;f 89;f 90;f 91;f 92;f 93;f 94;f 95;f 96;f 97;f 98;f 99;f 100;f 101;f 102;f 103;f 104;f 105;f 106;f 107;f 108;f 109;f 110;f 111;f 112;f 113;f 114;f 115;f 116;f 117;f 118;f 119;f 120;f 121;f 122;f 123;f 124;f 125;f 126;f 127]

let test (a b c d e f g h i j k l m n o p: (l: list bit {List.Tot.length l == 4})) = 
  let input = bv_of_list_list 4 [
    a;z;z;z; b;z;z;z; c;z;z;z; d;z;z;z;
    e;z;z;z; f;z;z;z; g;z;z;z; h;z;z;z;
    i;z;z;z; j;z;z;z; k;z;z;z; l;z;z;z;
    m;z;z;z; n;z;z;z; o;z;z;z; p;z;z;z;
    
    // z;z;z;a; z;z;z;b; z;z;z;c; z;z;z;d;
    // z;z;z;e; z;z;z;f; z;z;z;g; z;z;z;h;
    // z;z;z;i; z;z;z;j; z;z;z;k; z;z;z;l;
    // z;z;z;m; z;z;z;n; z;z;z;o; z;z;z;p;
  ] in
  serialize_4_ input


// let xx a b c d e f g h i j k l m n o p =
//   Pervasives.norm [iota; primops; zeta_full; delta] (
//     Pervasives.norm [iota; primops; zeta; delta] (
//       let {vector; adjacent_2_combined; adjacent_8_combined; combined'; combined} = test a b c d e f g h i j k l m n o p in
//       let vector = map256 (fun (idx: nat{idx < 256}) -> vector idx) in
//       let adjacent_2_combined = map256 (fun (idx: nat{idx < 256}) -> adjacent_2_combined idx) in
//       let adjacent_8_combined = map256 (fun (idx: nat{idx < 256}) -> adjacent_8_combined idx) in
//       let combined' = map256 (fun (idx: nat{idx < 256}) -> combined' idx) in
//       let combined = map128 (fun (idx: nat{idx < 128}) -> combined idx) in
//       // map128 (fun (idx: nat {idx < 128}) -> test a b c d e f g h i j k l m n o p idx)
//       {vector; adjacent_2_combined; adjacent_8_combined; combined'; combined}
//       // (vector, adjacent_2_combined)
//     )
//   )



open FStar.Tactics.V2
open Tactics.Utils


open Libcrux_intrinsics.Avx2_extract {t_Vec256, t_Vec128}
// open BitVec.Intrinsics {
  
// }

#push-options "--compat_pre_core 0"
let serialize_4__ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    BitVec.Intrinsics.mm256_madd_epi16 vector
      (BitVec.Intrinsics.mm256_set_epi16 (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
          (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
          (1s <<! 4l <: i16) 1s (1s <<! 4l <: i16) 1s
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    BitVec.Intrinsics.mm256_shuffle_epi8 adjacent_2_combined
      (BitVec.Intrinsics.mm256_set_epi8 (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) (-1y) 12y 8y 4y 0y (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y) (-1y)
          (-1y) (-1y) (-1y) (-1y) 12y 8y 4y 0y
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    // BitVec.Intrinsics.mm256_permutevar8x32_epi32_i32 adjacent_8_combined (mk_list_8 0 0 0 0 0 0 4 0)
    BitVec.Intrinsics.mm256_permutevar8x32_epi32 adjacent_8_combined
      (BitVec.Intrinsics.mm256_set_epi32 0l 0l 0l 0l 0l 0l 4l 0l
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let combined:t_Vec128 =
    BitVec.Intrinsics.mm256_castsi256_si128 combined
  in
  assume (BitVec.Intrinsics.forall_bool #256 (fun i -> i % 16 < 4 || vector i = 0));
  assert (forall (i: nat {i < 64}).
    // let local_i = i / 4 in
    combined i == vector ((i / 4) * 16 + i % 4)
  ) by (
    // unfold wrappers
    norm [primops; iota; zeta; delta_namespace [
      `%BitVec.Intrinsics.mm256_shuffle_epi8;
      `%BitVec.Intrinsics.mm256_permutevar8x32_epi32;
      `%BitVec.Intrinsics.mm256_madd_epi16;
      `%BitVec.Intrinsics.mm256_castsi256_si128;
      "BitVec.Utils";
    ]];
    Tactics.Utils.prove_forall_nat_pointwise (Tactics.Utils.print_time "SMT query succeeded in " (fun _ ->
      let reduce t =
        norm [primops; iota; zeta_full; delta_namespace [
          "FStar.FunctionalExtensionality";
          t;
          `%BitVec.Utils.mk_bv;
          `%( + ); `%op_Subtraction; `%( / ); `%( * ); `%( % )
        ]];
        norm [primops; iota; zeta_full; delta_namespace [
          "FStar.List.Tot"; `%( + ); `%op_Subtraction; `%( / ); `%( * ); `%( % )
        ]]
      in
      reduce (`%BitVec.Intrinsics.mm256_permutevar8x32_epi32_i32);
      reduce (`%BitVec.Intrinsics.mm256_shuffle_epi8_i8);
      reduce (`%BitVec.Intrinsics.mm256_madd_epi16_specialized);
      grewrite (quote (forall_bool #256 (fun i -> i % 16 < 4 || op_Equality #int (vector i) 0))) (`true);
      flip (); smt ();
      reduce (`%BitVec.Intrinsics.mm256_madd_epi16_specialized');
      // focus (fun _ -> dump' "Goal!!");
      trivial ()
    ))
  );
  combined
