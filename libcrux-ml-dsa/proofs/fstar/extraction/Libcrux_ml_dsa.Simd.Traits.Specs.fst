module Libcrux_ml_dsa.Simd.Traits.Specs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let v_PRIME: u32 = mk_u32 8380417

let v_MONT_R: u32 = mk_u32 8380417

let v_FIELD_MAX: u32 = mk_u32 8380416

let v_FIELD_MID: u32 = mk_u32 4190208

let v_NTT_BASE_BOUND: u32 = v_FIELD_MID

let v_COEFFICIENTS_IN_SIMD_UNIT: usize = mk_usize 8

let int_is_i32 (i: Hax_lib.Int.t_Int) : bool =
  i <= (Rust_primitives.Hax.Int.from_machine Core.Num.impl_i32__MAX <: Hax_lib.Int.t_Int) &&
  i >= (Rust_primitives.Hax.Int.from_machine Core.Num.impl_i32__MIN <: Hax_lib.Int.t_Int)

[@@ "opaque_to_smt"]

let add_pre (lhs rhs: t_Array i32 (mk_usize 8)) : Hax_lib.Prop.t_Prop =
  forall (i: usize).
    b2t (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool) ==>
    b2t
    (int_is_i32 ((Rust_primitives.Hax.Int.from_machine (lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (rhs.[ i ] <: i32) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int)
      <:
      bool)

let bounded_add_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
                (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b))
               [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b); 
                SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
                SMTPat (Spec.Utils.is_i32b_array_opaque b2 b)] = 
        reveal_opaque (`%add_pre) (add_pre)

[@@ "opaque_to_smt"]

let add_post (lhs rhs future_lhs: t_Array i32 (mk_usize 8)) : Hax_lib.Prop.t_Prop =
  forall (i: usize).
    b2t (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool) ==>
    b2t
    ((Rust_primitives.Hax.Int.from_machine (future_lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) =
      ((Rust_primitives.Hax.Int.from_machine (lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) +
        (Rust_primitives.Hax.Int.from_machine (rhs.[ i ] <: i32) <: Hax_lib.Int.t_Int)
        <:
        Hax_lib.Int.t_Int)
      <:
      bool)

let bounded_add_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                    b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future))
            (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future))
            [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future); 
            SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
            SMTPat (Spec.Utils.is_i32b_array_opaque b2 b);
            SMTPat (Spec.Utils.is_i32b_array_opaque b3 a_future)] = 
        reveal_opaque (`%add_post) (add_post)

[@@ "opaque_to_smt"]

let sub_pre (lhs rhs: t_Array i32 (mk_usize 8)) : Hax_lib.Prop.t_Prop =
  forall (i: usize).
    b2t (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool) ==>
    b2t
    (int_is_i32 ((Rust_primitives.Hax.Int.from_machine (lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine (rhs.[ i ] <: i32) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int)
      <:
      bool)

let bounded_sub_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
              (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre a b))
              [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre a b); 
               SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
               SMTPat (Spec.Utils.is_i32b_array_opaque b2 b)] = 
        reveal_opaque (`%sub_pre) (sub_pre)

[@@ "opaque_to_smt"]

let sub_post (lhs rhs future_lhs: t_Array i32 (mk_usize 8)) : Hax_lib.Prop.t_Prop =
  forall (i: usize).
    b2t (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool) ==>
    b2t
    ((Rust_primitives.Hax.Int.from_machine (future_lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) =
      ((Rust_primitives.Hax.Int.from_machine (lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) -
        (Rust_primitives.Hax.Int.from_machine (rhs.[ i ] <: i32) <: Hax_lib.Int.t_Int)
        <:
        Hax_lib.Int.t_Int)
      <:
      bool)

let bounded_sub_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                        b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.sub_post a b a_future))
                (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future))
                [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.sub_post a b a_future); 
                SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
                SMTPat (Spec.Utils.is_i32b_array_opaque b2 b);
                SMTPat (Spec.Utils.is_i32b_array_opaque b3 a_future)] = 
                reveal_opaque (`%sub_post) (sub_post)

let zeta (i: usize)
    : Prims.Pure i32
      (requires i <. mk_usize 256)
      (ensures
        fun result ->
          let result:i32 = result in
          result >=. mk_i32 0 && result <=. (cast (v_FIELD_MAX <: u32) <: i32)) =
  match i <: usize with
  | Rust_primitives.Integers.MkInt 0 -> mk_i32 0
  | Rust_primitives.Integers.MkInt 1 -> mk_i32 4808194
  | Rust_primitives.Integers.MkInt 2 -> mk_i32 3765607
  | Rust_primitives.Integers.MkInt 3 -> mk_i32 3761513
  | Rust_primitives.Integers.MkInt 4 -> mk_i32 5178923
  | Rust_primitives.Integers.MkInt 5 -> mk_i32 5496691
  | Rust_primitives.Integers.MkInt 6 -> mk_i32 5234739
  | Rust_primitives.Integers.MkInt 7 -> mk_i32 5178987
  | Rust_primitives.Integers.MkInt 8 -> mk_i32 7778734
  | Rust_primitives.Integers.MkInt 9 -> mk_i32 3542485
  | Rust_primitives.Integers.MkInt 10 -> mk_i32 2682288
  | Rust_primitives.Integers.MkInt 11 -> mk_i32 2129892
  | Rust_primitives.Integers.MkInt 12 -> mk_i32 3764867
  | Rust_primitives.Integers.MkInt 13 -> mk_i32 7375178
  | Rust_primitives.Integers.MkInt 14 -> mk_i32 557458
  | Rust_primitives.Integers.MkInt 15 -> mk_i32 7159240
  | Rust_primitives.Integers.MkInt 16 -> mk_i32 5010068
  | Rust_primitives.Integers.MkInt 17 -> mk_i32 4317364
  | Rust_primitives.Integers.MkInt 18 -> mk_i32 2663378
  | Rust_primitives.Integers.MkInt 19 -> mk_i32 6705802
  | Rust_primitives.Integers.MkInt 20 -> mk_i32 4855975
  | Rust_primitives.Integers.MkInt 21 -> mk_i32 7946292
  | Rust_primitives.Integers.MkInt 22 -> mk_i32 676590
  | Rust_primitives.Integers.MkInt 23 -> mk_i32 7044481
  | Rust_primitives.Integers.MkInt 24 -> mk_i32 5152541
  | Rust_primitives.Integers.MkInt 25 -> mk_i32 1714295
  | Rust_primitives.Integers.MkInt 26 -> mk_i32 2453983
  | Rust_primitives.Integers.MkInt 27 -> mk_i32 1460718
  | Rust_primitives.Integers.MkInt 28 -> mk_i32 7737789
  | Rust_primitives.Integers.MkInt 29 -> mk_i32 4795319
  | Rust_primitives.Integers.MkInt 30 -> mk_i32 2815639
  | Rust_primitives.Integers.MkInt 31 -> mk_i32 2283733
  | Rust_primitives.Integers.MkInt 32 -> mk_i32 3602218
  | Rust_primitives.Integers.MkInt 33 -> mk_i32 3182878
  | Rust_primitives.Integers.MkInt 34 -> mk_i32 2740543
  | Rust_primitives.Integers.MkInt 35 -> mk_i32 4793971
  | Rust_primitives.Integers.MkInt 36 -> mk_i32 5269599
  | Rust_primitives.Integers.MkInt 37 -> mk_i32 2101410
  | Rust_primitives.Integers.MkInt 38 -> mk_i32 3704823
  | Rust_primitives.Integers.MkInt 39 -> mk_i32 1159875
  | Rust_primitives.Integers.MkInt 40 -> mk_i32 394148
  | Rust_primitives.Integers.MkInt 41 -> mk_i32 928749
  | Rust_primitives.Integers.MkInt 42 -> mk_i32 1095468
  | Rust_primitives.Integers.MkInt 43 -> mk_i32 4874037
  | Rust_primitives.Integers.MkInt 44 -> mk_i32 2071829
  | Rust_primitives.Integers.MkInt 45 -> mk_i32 4361428
  | Rust_primitives.Integers.MkInt 46 -> mk_i32 3241972
  | Rust_primitives.Integers.MkInt 47 -> mk_i32 2156050
  | Rust_primitives.Integers.MkInt 48 -> mk_i32 3415069
  | Rust_primitives.Integers.MkInt 49 -> mk_i32 1759347
  | Rust_primitives.Integers.MkInt 50 -> mk_i32 7562881
  | Rust_primitives.Integers.MkInt 51 -> mk_i32 4805951
  | Rust_primitives.Integers.MkInt 52 -> mk_i32 3756790
  | Rust_primitives.Integers.MkInt 53 -> mk_i32 6444618
  | Rust_primitives.Integers.MkInt 54 -> mk_i32 6663429
  | Rust_primitives.Integers.MkInt 55 -> mk_i32 4430364
  | Rust_primitives.Integers.MkInt 56 -> mk_i32 5483103
  | Rust_primitives.Integers.MkInt 57 -> mk_i32 3192354
  | Rust_primitives.Integers.MkInt 58 -> mk_i32 556856
  | Rust_primitives.Integers.MkInt 59 -> mk_i32 3870317
  | Rust_primitives.Integers.MkInt 60 -> mk_i32 2917338
  | Rust_primitives.Integers.MkInt 61 -> mk_i32 1853806
  | Rust_primitives.Integers.MkInt 62 -> mk_i32 3345963
  | Rust_primitives.Integers.MkInt 63 -> mk_i32 1858416
  | Rust_primitives.Integers.MkInt 64 -> mk_i32 3073009
  | Rust_primitives.Integers.MkInt 65 -> mk_i32 1277625
  | Rust_primitives.Integers.MkInt 66 -> mk_i32 5744944
  | Rust_primitives.Integers.MkInt 67 -> mk_i32 3852015
  | Rust_primitives.Integers.MkInt 68 -> mk_i32 4183372
  | Rust_primitives.Integers.MkInt 69 -> mk_i32 5157610
  | Rust_primitives.Integers.MkInt 70 -> mk_i32 5258977
  | Rust_primitives.Integers.MkInt 71 -> mk_i32 8106357
  | Rust_primitives.Integers.MkInt 72 -> mk_i32 2508980
  | Rust_primitives.Integers.MkInt 73 -> mk_i32 2028118
  | Rust_primitives.Integers.MkInt 74 -> mk_i32 1937570
  | Rust_primitives.Integers.MkInt 75 -> mk_i32 4564692
  | Rust_primitives.Integers.MkInt 76 -> mk_i32 2811291
  | Rust_primitives.Integers.MkInt 77 -> mk_i32 5396636
  | Rust_primitives.Integers.MkInt 78 -> mk_i32 7270901
  | Rust_primitives.Integers.MkInt 79 -> mk_i32 4158088
  | Rust_primitives.Integers.MkInt 80 -> mk_i32 1528066
  | Rust_primitives.Integers.MkInt 81 -> mk_i32 482649
  | Rust_primitives.Integers.MkInt 82 -> mk_i32 1148858
  | Rust_primitives.Integers.MkInt 83 -> mk_i32 5418153
  | Rust_primitives.Integers.MkInt 84 -> mk_i32 7814814
  | Rust_primitives.Integers.MkInt 85 -> mk_i32 169688
  | Rust_primitives.Integers.MkInt 86 -> mk_i32 2462444
  | Rust_primitives.Integers.MkInt 87 -> mk_i32 5046034
  | Rust_primitives.Integers.MkInt 88 -> mk_i32 4213992
  | Rust_primitives.Integers.MkInt 89 -> mk_i32 4892034
  | Rust_primitives.Integers.MkInt 90 -> mk_i32 1987814
  | Rust_primitives.Integers.MkInt 91 -> mk_i32 5183169
  | Rust_primitives.Integers.MkInt 92 -> mk_i32 1736313
  | Rust_primitives.Integers.MkInt 93 -> mk_i32 235407
  | Rust_primitives.Integers.MkInt 94 -> mk_i32 5130263
  | Rust_primitives.Integers.MkInt 95 -> mk_i32 3258457
  | Rust_primitives.Integers.MkInt 96 -> mk_i32 5801164
  | Rust_primitives.Integers.MkInt 97 -> mk_i32 1787943
  | Rust_primitives.Integers.MkInt 98 -> mk_i32 5989328
  | Rust_primitives.Integers.MkInt 99 -> mk_i32 6125690
  | Rust_primitives.Integers.MkInt 100 -> mk_i32 3482206
  | Rust_primitives.Integers.MkInt 101 -> mk_i32 4197502
  | Rust_primitives.Integers.MkInt 102 -> mk_i32 7080401
  | Rust_primitives.Integers.MkInt 103 -> mk_i32 6018354
  | Rust_primitives.Integers.MkInt 104 -> mk_i32 7062739
  | Rust_primitives.Integers.MkInt 105 -> mk_i32 2461387
  | Rust_primitives.Integers.MkInt 106 -> mk_i32 3035980
  | Rust_primitives.Integers.MkInt 107 -> mk_i32 621164
  | Rust_primitives.Integers.MkInt 108 -> mk_i32 3901472
  | Rust_primitives.Integers.MkInt 109 -> mk_i32 7153756
  | Rust_primitives.Integers.MkInt 110 -> mk_i32 2925816
  | Rust_primitives.Integers.MkInt 111 -> mk_i32 3374250
  | Rust_primitives.Integers.MkInt 112 -> mk_i32 1356448
  | Rust_primitives.Integers.MkInt 113 -> mk_i32 5604662
  | Rust_primitives.Integers.MkInt 114 -> mk_i32 2683270
  | Rust_primitives.Integers.MkInt 115 -> mk_i32 5601629
  | Rust_primitives.Integers.MkInt 116 -> mk_i32 4912752
  | Rust_primitives.Integers.MkInt 117 -> mk_i32 2312838
  | Rust_primitives.Integers.MkInt 118 -> mk_i32 7727142
  | Rust_primitives.Integers.MkInt 119 -> mk_i32 7921254
  | Rust_primitives.Integers.MkInt 120 -> mk_i32 348812
  | Rust_primitives.Integers.MkInt 121 -> mk_i32 8052569
  | Rust_primitives.Integers.MkInt 122 -> mk_i32 1011223
  | Rust_primitives.Integers.MkInt 123 -> mk_i32 6026202
  | Rust_primitives.Integers.MkInt 124 -> mk_i32 4561790
  | Rust_primitives.Integers.MkInt 125 -> mk_i32 6458164
  | Rust_primitives.Integers.MkInt 126 -> mk_i32 6143691
  | Rust_primitives.Integers.MkInt 127 -> mk_i32 1744507
  | Rust_primitives.Integers.MkInt 128 -> mk_i32 1753
  | Rust_primitives.Integers.MkInt 129 -> mk_i32 6444997
  | Rust_primitives.Integers.MkInt 130 -> mk_i32 5720892
  | Rust_primitives.Integers.MkInt 131 -> mk_i32 6924527
  | Rust_primitives.Integers.MkInt 132 -> mk_i32 2660408
  | Rust_primitives.Integers.MkInt 133 -> mk_i32 6600190
  | Rust_primitives.Integers.MkInt 134 -> mk_i32 8321269
  | Rust_primitives.Integers.MkInt 135 -> mk_i32 2772600
  | Rust_primitives.Integers.MkInt 136 -> mk_i32 1182243
  | Rust_primitives.Integers.MkInt 137 -> mk_i32 87208
  | Rust_primitives.Integers.MkInt 138 -> mk_i32 636927
  | Rust_primitives.Integers.MkInt 139 -> mk_i32 4415111
  | Rust_primitives.Integers.MkInt 140 -> mk_i32 4423672
  | Rust_primitives.Integers.MkInt 141 -> mk_i32 6084020
  | Rust_primitives.Integers.MkInt 142 -> mk_i32 5095502
  | Rust_primitives.Integers.MkInt 143 -> mk_i32 4663471
  | Rust_primitives.Integers.MkInt 144 -> mk_i32 8352605
  | Rust_primitives.Integers.MkInt 145 -> mk_i32 822541
  | Rust_primitives.Integers.MkInt 146 -> mk_i32 1009365
  | Rust_primitives.Integers.MkInt 147 -> mk_i32 5926272
  | Rust_primitives.Integers.MkInt 148 -> mk_i32 6400920
  | Rust_primitives.Integers.MkInt 149 -> mk_i32 1596822
  | Rust_primitives.Integers.MkInt 150 -> mk_i32 4423473
  | Rust_primitives.Integers.MkInt 151 -> mk_i32 4620952
  | Rust_primitives.Integers.MkInt 152 -> mk_i32 6695264
  | Rust_primitives.Integers.MkInt 153 -> mk_i32 4969849
  | Rust_primitives.Integers.MkInt 154 -> mk_i32 2678278
  | Rust_primitives.Integers.MkInt 155 -> mk_i32 4611469
  | Rust_primitives.Integers.MkInt 156 -> mk_i32 4829411
  | Rust_primitives.Integers.MkInt 157 -> mk_i32 635956
  | Rust_primitives.Integers.MkInt 158 -> mk_i32 8129971
  | Rust_primitives.Integers.MkInt 159 -> mk_i32 5925040
  | Rust_primitives.Integers.MkInt 160 -> mk_i32 4234153
  | Rust_primitives.Integers.MkInt 161 -> mk_i32 6607829
  | Rust_primitives.Integers.MkInt 162 -> mk_i32 2192938
  | Rust_primitives.Integers.MkInt 163 -> mk_i32 6653329
  | Rust_primitives.Integers.MkInt 164 -> mk_i32 2387513
  | Rust_primitives.Integers.MkInt 165 -> mk_i32 4768667
  | Rust_primitives.Integers.MkInt 166 -> mk_i32 8111961
  | Rust_primitives.Integers.MkInt 167 -> mk_i32 5199961
  | Rust_primitives.Integers.MkInt 168 -> mk_i32 3747250
  | Rust_primitives.Integers.MkInt 169 -> mk_i32 2296099
  | Rust_primitives.Integers.MkInt 170 -> mk_i32 1239911
  | Rust_primitives.Integers.MkInt 171 -> mk_i32 4541938
  | Rust_primitives.Integers.MkInt 172 -> mk_i32 3195676
  | Rust_primitives.Integers.MkInt 173 -> mk_i32 2642980
  | Rust_primitives.Integers.MkInt 174 -> mk_i32 1254190
  | Rust_primitives.Integers.MkInt 175 -> mk_i32 8368000
  | Rust_primitives.Integers.MkInt 176 -> mk_i32 2998219
  | Rust_primitives.Integers.MkInt 177 -> mk_i32 141835
  | Rust_primitives.Integers.MkInt 178 -> mk_i32 8291116
  | Rust_primitives.Integers.MkInt 179 -> mk_i32 2513018
  | Rust_primitives.Integers.MkInt 180 -> mk_i32 7025525
  | Rust_primitives.Integers.MkInt 181 -> mk_i32 613238
  | Rust_primitives.Integers.MkInt 182 -> mk_i32 7070156
  | Rust_primitives.Integers.MkInt 183 -> mk_i32 6161950
  | Rust_primitives.Integers.MkInt 184 -> mk_i32 7921677
  | Rust_primitives.Integers.MkInt 185 -> mk_i32 6458423
  | Rust_primitives.Integers.MkInt 186 -> mk_i32 4040196
  | Rust_primitives.Integers.MkInt 187 -> mk_i32 4908348
  | Rust_primitives.Integers.MkInt 188 -> mk_i32 2039144
  | Rust_primitives.Integers.MkInt 189 -> mk_i32 6500539
  | Rust_primitives.Integers.MkInt 190 -> mk_i32 7561656
  | Rust_primitives.Integers.MkInt 191 -> mk_i32 6201452
  | Rust_primitives.Integers.MkInt 192 -> mk_i32 6757063
  | Rust_primitives.Integers.MkInt 193 -> mk_i32 2105286
  | Rust_primitives.Integers.MkInt 194 -> mk_i32 6006015
  | Rust_primitives.Integers.MkInt 195 -> mk_i32 6346610
  | Rust_primitives.Integers.MkInt 196 -> mk_i32 586241
  | Rust_primitives.Integers.MkInt 197 -> mk_i32 7200804
  | Rust_primitives.Integers.MkInt 198 -> mk_i32 527981
  | Rust_primitives.Integers.MkInt 199 -> mk_i32 5637006
  | Rust_primitives.Integers.MkInt 200 -> mk_i32 6903432
  | Rust_primitives.Integers.MkInt 201 -> mk_i32 1994046
  | Rust_primitives.Integers.MkInt 202 -> mk_i32 2491325
  | Rust_primitives.Integers.MkInt 203 -> mk_i32 6987258
  | Rust_primitives.Integers.MkInt 204 -> mk_i32 507927
  | Rust_primitives.Integers.MkInt 205 -> mk_i32 7192532
  | Rust_primitives.Integers.MkInt 206 -> mk_i32 7655613
  | Rust_primitives.Integers.MkInt 207 -> mk_i32 6545891
  | Rust_primitives.Integers.MkInt 208 -> mk_i32 5346675
  | Rust_primitives.Integers.MkInt 209 -> mk_i32 8041997
  | Rust_primitives.Integers.MkInt 210 -> mk_i32 2647994
  | Rust_primitives.Integers.MkInt 211 -> mk_i32 3009748
  | Rust_primitives.Integers.MkInt 212 -> mk_i32 5767564
  | Rust_primitives.Integers.MkInt 213 -> mk_i32 4148469
  | Rust_primitives.Integers.MkInt 214 -> mk_i32 749577
  | Rust_primitives.Integers.MkInt 215 -> mk_i32 4357667
  | Rust_primitives.Integers.MkInt 216 -> mk_i32 3980599
  | Rust_primitives.Integers.MkInt 217 -> mk_i32 2569011
  | Rust_primitives.Integers.MkInt 218 -> mk_i32 6764887
  | Rust_primitives.Integers.MkInt 219 -> mk_i32 1723229
  | Rust_primitives.Integers.MkInt 220 -> mk_i32 1665318
  | Rust_primitives.Integers.MkInt 221 -> mk_i32 2028038
  | Rust_primitives.Integers.MkInt 222 -> mk_i32 1163598
  | Rust_primitives.Integers.MkInt 223 -> mk_i32 5011144
  | Rust_primitives.Integers.MkInt 224 -> mk_i32 3994671
  | Rust_primitives.Integers.MkInt 225 -> mk_i32 8368538
  | Rust_primitives.Integers.MkInt 226 -> mk_i32 7009900
  | Rust_primitives.Integers.MkInt 227 -> mk_i32 3020393
  | Rust_primitives.Integers.MkInt 228 -> mk_i32 3363542
  | Rust_primitives.Integers.MkInt 229 -> mk_i32 214880
  | Rust_primitives.Integers.MkInt 230 -> mk_i32 545376
  | Rust_primitives.Integers.MkInt 231 -> mk_i32 7609976
  | Rust_primitives.Integers.MkInt 232 -> mk_i32 3105558
  | Rust_primitives.Integers.MkInt 233 -> mk_i32 7277073
  | Rust_primitives.Integers.MkInt 234 -> mk_i32 508145
  | Rust_primitives.Integers.MkInt 235 -> mk_i32 7826699
  | Rust_primitives.Integers.MkInt 236 -> mk_i32 860144
  | Rust_primitives.Integers.MkInt 237 -> mk_i32 3430436
  | Rust_primitives.Integers.MkInt 238 -> mk_i32 140244
  | Rust_primitives.Integers.MkInt 239 -> mk_i32 6866265
  | Rust_primitives.Integers.MkInt 240 -> mk_i32 6195333
  | Rust_primitives.Integers.MkInt 241 -> mk_i32 3123762
  | Rust_primitives.Integers.MkInt 242 -> mk_i32 2358373
  | Rust_primitives.Integers.MkInt 243 -> mk_i32 6187330
  | Rust_primitives.Integers.MkInt 244 -> mk_i32 5365997
  | Rust_primitives.Integers.MkInt 245 -> mk_i32 6663603
  | Rust_primitives.Integers.MkInt 246 -> mk_i32 2926054
  | Rust_primitives.Integers.MkInt 247 -> mk_i32 7987710
  | Rust_primitives.Integers.MkInt 248 -> mk_i32 8077412
  | Rust_primitives.Integers.MkInt 249 -> mk_i32 3531229
  | Rust_primitives.Integers.MkInt 250 -> mk_i32 4405932
  | Rust_primitives.Integers.MkInt 251 -> mk_i32 4606686
  | Rust_primitives.Integers.MkInt 252 -> mk_i32 1900052
  | Rust_primitives.Integers.MkInt 253 -> mk_i32 7598542
  | Rust_primitives.Integers.MkInt 254 -> mk_i32 1054478
  | Rust_primitives.Integers.MkInt 255 -> mk_i32 7648983
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let zeta_r (i: usize)
    : Prims.Pure i32
      (requires i <. mk_usize 256)
      (ensures
        fun result ->
          let result:i32 = result in
          Spec.Utils.is_i32b (v v_FIELD_MID) result /\
          v result % (v v_PRIME) == (v (zeta i) * pow2 32) % (v v_PRIME)) =
  match i <: usize with
  | Rust_primitives.Integers.MkInt 0 -> mk_i32 0
  | Rust_primitives.Integers.MkInt 1 -> mk_i32 25847
  | Rust_primitives.Integers.MkInt 2 -> mk_i32 (-2608894)
  | Rust_primitives.Integers.MkInt 3 -> mk_i32 (-518909)
  | Rust_primitives.Integers.MkInt 4 -> mk_i32 237124
  | Rust_primitives.Integers.MkInt 5 -> mk_i32 (-777960)
  | Rust_primitives.Integers.MkInt 6 -> mk_i32 (-876248)
  | Rust_primitives.Integers.MkInt 7 -> mk_i32 466468
  | Rust_primitives.Integers.MkInt 8 -> mk_i32 1826347
  | Rust_primitives.Integers.MkInt 9 -> mk_i32 2353451
  | Rust_primitives.Integers.MkInt 10 -> mk_i32 (-359251)
  | Rust_primitives.Integers.MkInt 11 -> mk_i32 (-2091905)
  | Rust_primitives.Integers.MkInt 12 -> mk_i32 3119733
  | Rust_primitives.Integers.MkInt 13 -> mk_i32 (-2884855)
  | Rust_primitives.Integers.MkInt 14 -> mk_i32 3111497
  | Rust_primitives.Integers.MkInt 15 -> mk_i32 2680103
  | Rust_primitives.Integers.MkInt 16 -> mk_i32 2725464
  | Rust_primitives.Integers.MkInt 17 -> mk_i32 1024112
  | Rust_primitives.Integers.MkInt 18 -> mk_i32 (-1079900)
  | Rust_primitives.Integers.MkInt 19 -> mk_i32 3585928
  | Rust_primitives.Integers.MkInt 20 -> mk_i32 (-549488)
  | Rust_primitives.Integers.MkInt 21 -> mk_i32 (-1119584)
  | Rust_primitives.Integers.MkInt 22 -> mk_i32 2619752
  | Rust_primitives.Integers.MkInt 23 -> mk_i32 (-2108549)
  | Rust_primitives.Integers.MkInt 24 -> mk_i32 (-2118186)
  | Rust_primitives.Integers.MkInt 25 -> mk_i32 (-3859737)
  | Rust_primitives.Integers.MkInt 26 -> mk_i32 (-1399561)
  | Rust_primitives.Integers.MkInt 27 -> mk_i32 (-3277672)
  | Rust_primitives.Integers.MkInt 28 -> mk_i32 1757237
  | Rust_primitives.Integers.MkInt 29 -> mk_i32 (-19422)
  | Rust_primitives.Integers.MkInt 30 -> mk_i32 4010497
  | Rust_primitives.Integers.MkInt 31 -> mk_i32 280005
  | Rust_primitives.Integers.MkInt 32 -> mk_i32 2706023
  | Rust_primitives.Integers.MkInt 33 -> mk_i32 95776
  | Rust_primitives.Integers.MkInt 34 -> mk_i32 3077325
  | Rust_primitives.Integers.MkInt 35 -> mk_i32 3530437
  | Rust_primitives.Integers.MkInt 36 -> mk_i32 (-1661693)
  | Rust_primitives.Integers.MkInt 37 -> mk_i32 (-3592148)
  | Rust_primitives.Integers.MkInt 38 -> mk_i32 (-2537516)
  | Rust_primitives.Integers.MkInt 39 -> mk_i32 3915439
  | Rust_primitives.Integers.MkInt 40 -> mk_i32 (-3861115)
  | Rust_primitives.Integers.MkInt 41 -> mk_i32 (-3043716)
  | Rust_primitives.Integers.MkInt 42 -> mk_i32 3574422
  | Rust_primitives.Integers.MkInt 43 -> mk_i32 (-2867647)
  | Rust_primitives.Integers.MkInt 44 -> mk_i32 3539968
  | Rust_primitives.Integers.MkInt 45 -> mk_i32 (-300467)
  | Rust_primitives.Integers.MkInt 46 -> mk_i32 2348700
  | Rust_primitives.Integers.MkInt 47 -> mk_i32 (-539299)
  | Rust_primitives.Integers.MkInt 48 -> mk_i32 (-1699267)
  | Rust_primitives.Integers.MkInt 49 -> mk_i32 (-1643818)
  | Rust_primitives.Integers.MkInt 50 -> mk_i32 3505694
  | Rust_primitives.Integers.MkInt 51 -> mk_i32 (-3821735)
  | Rust_primitives.Integers.MkInt 52 -> mk_i32 3507263
  | Rust_primitives.Integers.MkInt 53 -> mk_i32 (-2140649)
  | Rust_primitives.Integers.MkInt 54 -> mk_i32 (-1600420)
  | Rust_primitives.Integers.MkInt 55 -> mk_i32 3699596
  | Rust_primitives.Integers.MkInt 56 -> mk_i32 811944
  | Rust_primitives.Integers.MkInt 57 -> mk_i32 531354
  | Rust_primitives.Integers.MkInt 58 -> mk_i32 954230
  | Rust_primitives.Integers.MkInt 59 -> mk_i32 3881043
  | Rust_primitives.Integers.MkInt 60 -> mk_i32 3900724
  | Rust_primitives.Integers.MkInt 61 -> mk_i32 (-2556880)
  | Rust_primitives.Integers.MkInt 62 -> mk_i32 2071892
  | Rust_primitives.Integers.MkInt 63 -> mk_i32 (-2797779)
  | Rust_primitives.Integers.MkInt 64 -> mk_i32 (-3930395)
  | Rust_primitives.Integers.MkInt 65 -> mk_i32 (-1528703)
  | Rust_primitives.Integers.MkInt 66 -> mk_i32 (-3677745)
  | Rust_primitives.Integers.MkInt 67 -> mk_i32 (-3041255)
  | Rust_primitives.Integers.MkInt 68 -> mk_i32 (-1452451)
  | Rust_primitives.Integers.MkInt 69 -> mk_i32 3475950
  | Rust_primitives.Integers.MkInt 70 -> mk_i32 2176455
  | Rust_primitives.Integers.MkInt 71 -> mk_i32 (-1585221)
  | Rust_primitives.Integers.MkInt 72 -> mk_i32 (-1257611)
  | Rust_primitives.Integers.MkInt 73 -> mk_i32 1939314
  | Rust_primitives.Integers.MkInt 74 -> mk_i32 (-4083598)
  | Rust_primitives.Integers.MkInt 75 -> mk_i32 (-1000202)
  | Rust_primitives.Integers.MkInt 76 -> mk_i32 (-3190144)
  | Rust_primitives.Integers.MkInt 77 -> mk_i32 (-3157330)
  | Rust_primitives.Integers.MkInt 78 -> mk_i32 (-3632928)
  | Rust_primitives.Integers.MkInt 79 -> mk_i32 126922
  | Rust_primitives.Integers.MkInt 80 -> mk_i32 3412210
  | Rust_primitives.Integers.MkInt 81 -> mk_i32 (-983419)
  | Rust_primitives.Integers.MkInt 82 -> mk_i32 2147896
  | Rust_primitives.Integers.MkInt 83 -> mk_i32 2715295
  | Rust_primitives.Integers.MkInt 84 -> mk_i32 (-2967645)
  | Rust_primitives.Integers.MkInt 85 -> mk_i32 (-3693493)
  | Rust_primitives.Integers.MkInt 86 -> mk_i32 (-411027)
  | Rust_primitives.Integers.MkInt 87 -> mk_i32 (-2477047)
  | Rust_primitives.Integers.MkInt 88 -> mk_i32 (-671102)
  | Rust_primitives.Integers.MkInt 89 -> mk_i32 (-1228525)
  | Rust_primitives.Integers.MkInt 90 -> mk_i32 (-22981)
  | Rust_primitives.Integers.MkInt 91 -> mk_i32 (-1308169)
  | Rust_primitives.Integers.MkInt 92 -> mk_i32 (-381987)
  | Rust_primitives.Integers.MkInt 93 -> mk_i32 1349076
  | Rust_primitives.Integers.MkInt 94 -> mk_i32 1852771
  | Rust_primitives.Integers.MkInt 95 -> mk_i32 (-1430430)
  | Rust_primitives.Integers.MkInt 96 -> mk_i32 (-3343383)
  | Rust_primitives.Integers.MkInt 97 -> mk_i32 264944
  | Rust_primitives.Integers.MkInt 98 -> mk_i32 508951
  | Rust_primitives.Integers.MkInt 99 -> mk_i32 3097992
  | Rust_primitives.Integers.MkInt 100 -> mk_i32 44288
  | Rust_primitives.Integers.MkInt 101 -> mk_i32 (-1100098)
  | Rust_primitives.Integers.MkInt 102 -> mk_i32 904516
  | Rust_primitives.Integers.MkInt 103 -> mk_i32 3958618
  | Rust_primitives.Integers.MkInt 104 -> mk_i32 (-3724342)
  | Rust_primitives.Integers.MkInt 105 -> mk_i32 (-8578)
  | Rust_primitives.Integers.MkInt 106 -> mk_i32 1653064
  | Rust_primitives.Integers.MkInt 107 -> mk_i32 (-3249728)
  | Rust_primitives.Integers.MkInt 108 -> mk_i32 2389356
  | Rust_primitives.Integers.MkInt 109 -> mk_i32 (-210977)
  | Rust_primitives.Integers.MkInt 110 -> mk_i32 759969
  | Rust_primitives.Integers.MkInt 111 -> mk_i32 (-1316856)
  | Rust_primitives.Integers.MkInt 112 -> mk_i32 189548
  | Rust_primitives.Integers.MkInt 113 -> mk_i32 (-3553272)
  | Rust_primitives.Integers.MkInt 114 -> mk_i32 3159746
  | Rust_primitives.Integers.MkInt 115 -> mk_i32 (-1851402)
  | Rust_primitives.Integers.MkInt 116 -> mk_i32 (-2409325)
  | Rust_primitives.Integers.MkInt 117 -> mk_i32 (-177440)
  | Rust_primitives.Integers.MkInt 118 -> mk_i32 1315589
  | Rust_primitives.Integers.MkInt 119 -> mk_i32 1341330
  | Rust_primitives.Integers.MkInt 120 -> mk_i32 1285669
  | Rust_primitives.Integers.MkInt 121 -> mk_i32 (-1584928)
  | Rust_primitives.Integers.MkInt 122 -> mk_i32 (-812732)
  | Rust_primitives.Integers.MkInt 123 -> mk_i32 (-1439742)
  | Rust_primitives.Integers.MkInt 124 -> mk_i32 (-3019102)
  | Rust_primitives.Integers.MkInt 125 -> mk_i32 (-3881060)
  | Rust_primitives.Integers.MkInt 126 -> mk_i32 (-3628969)
  | Rust_primitives.Integers.MkInt 127 -> mk_i32 3839961
  | Rust_primitives.Integers.MkInt 128 -> mk_i32 2091667
  | Rust_primitives.Integers.MkInt 129 -> mk_i32 3407706
  | Rust_primitives.Integers.MkInt 130 -> mk_i32 2316500
  | Rust_primitives.Integers.MkInt 131 -> mk_i32 3817976
  | Rust_primitives.Integers.MkInt 132 -> mk_i32 (-3342478)
  | Rust_primitives.Integers.MkInt 133 -> mk_i32 2244091
  | Rust_primitives.Integers.MkInt 134 -> mk_i32 (-2446433)
  | Rust_primitives.Integers.MkInt 135 -> mk_i32 (-3562462)
  | Rust_primitives.Integers.MkInt 136 -> mk_i32 266997
  | Rust_primitives.Integers.MkInt 137 -> mk_i32 2434439
  | Rust_primitives.Integers.MkInt 138 -> mk_i32 (-1235728)
  | Rust_primitives.Integers.MkInt 139 -> mk_i32 3513181
  | Rust_primitives.Integers.MkInt 140 -> mk_i32 (-3520352)
  | Rust_primitives.Integers.MkInt 141 -> mk_i32 (-3759364)
  | Rust_primitives.Integers.MkInt 142 -> mk_i32 (-1197226)
  | Rust_primitives.Integers.MkInt 143 -> mk_i32 (-3193378)
  | Rust_primitives.Integers.MkInt 144 -> mk_i32 900702
  | Rust_primitives.Integers.MkInt 145 -> mk_i32 1859098
  | Rust_primitives.Integers.MkInt 146 -> mk_i32 909542
  | Rust_primitives.Integers.MkInt 147 -> mk_i32 819034
  | Rust_primitives.Integers.MkInt 148 -> mk_i32 495491
  | Rust_primitives.Integers.MkInt 149 -> mk_i32 (-1613174)
  | Rust_primitives.Integers.MkInt 150 -> mk_i32 (-43260)
  | Rust_primitives.Integers.MkInt 151 -> mk_i32 (-522500)
  | Rust_primitives.Integers.MkInt 152 -> mk_i32 (-655327)
  | Rust_primitives.Integers.MkInt 153 -> mk_i32 (-3122442)
  | Rust_primitives.Integers.MkInt 154 -> mk_i32 2031748
  | Rust_primitives.Integers.MkInt 155 -> mk_i32 3207046
  | Rust_primitives.Integers.MkInt 156 -> mk_i32 (-3556995)
  | Rust_primitives.Integers.MkInt 157 -> mk_i32 (-525098)
  | Rust_primitives.Integers.MkInt 158 -> mk_i32 (-768622)
  | Rust_primitives.Integers.MkInt 159 -> mk_i32 (-3595838)
  | Rust_primitives.Integers.MkInt 160 -> mk_i32 342297
  | Rust_primitives.Integers.MkInt 161 -> mk_i32 286988
  | Rust_primitives.Integers.MkInt 162 -> mk_i32 (-2437823)
  | Rust_primitives.Integers.MkInt 163 -> mk_i32 4108315
  | Rust_primitives.Integers.MkInt 164 -> mk_i32 3437287
  | Rust_primitives.Integers.MkInt 165 -> mk_i32 (-3342277)
  | Rust_primitives.Integers.MkInt 166 -> mk_i32 1735879
  | Rust_primitives.Integers.MkInt 167 -> mk_i32 203044
  | Rust_primitives.Integers.MkInt 168 -> mk_i32 2842341
  | Rust_primitives.Integers.MkInt 169 -> mk_i32 2691481
  | Rust_primitives.Integers.MkInt 170 -> mk_i32 (-2590150)
  | Rust_primitives.Integers.MkInt 171 -> mk_i32 1265009
  | Rust_primitives.Integers.MkInt 172 -> mk_i32 4055324
  | Rust_primitives.Integers.MkInt 173 -> mk_i32 1247620
  | Rust_primitives.Integers.MkInt 174 -> mk_i32 2486353
  | Rust_primitives.Integers.MkInt 175 -> mk_i32 1595974
  | Rust_primitives.Integers.MkInt 176 -> mk_i32 (-3767016)
  | Rust_primitives.Integers.MkInt 177 -> mk_i32 1250494
  | Rust_primitives.Integers.MkInt 178 -> mk_i32 2635921
  | Rust_primitives.Integers.MkInt 179 -> mk_i32 (-3548272)
  | Rust_primitives.Integers.MkInt 180 -> mk_i32 (-2994039)
  | Rust_primitives.Integers.MkInt 181 -> mk_i32 1869119
  | Rust_primitives.Integers.MkInt 182 -> mk_i32 1903435
  | Rust_primitives.Integers.MkInt 183 -> mk_i32 (-1050970)
  | Rust_primitives.Integers.MkInt 184 -> mk_i32 (-1333058)
  | Rust_primitives.Integers.MkInt 185 -> mk_i32 1237275
  | Rust_primitives.Integers.MkInt 186 -> mk_i32 (-3318210)
  | Rust_primitives.Integers.MkInt 187 -> mk_i32 (-1430225)
  | Rust_primitives.Integers.MkInt 188 -> mk_i32 (-451100)
  | Rust_primitives.Integers.MkInt 189 -> mk_i32 1312455
  | Rust_primitives.Integers.MkInt 190 -> mk_i32 3306115
  | Rust_primitives.Integers.MkInt 191 -> mk_i32 (-1962642)
  | Rust_primitives.Integers.MkInt 192 -> mk_i32 (-1279661)
  | Rust_primitives.Integers.MkInt 193 -> mk_i32 1917081
  | Rust_primitives.Integers.MkInt 194 -> mk_i32 (-2546312)
  | Rust_primitives.Integers.MkInt 195 -> mk_i32 (-1374803)
  | Rust_primitives.Integers.MkInt 196 -> mk_i32 1500165
  | Rust_primitives.Integers.MkInt 197 -> mk_i32 777191
  | Rust_primitives.Integers.MkInt 198 -> mk_i32 2235880
  | Rust_primitives.Integers.MkInt 199 -> mk_i32 3406031
  | Rust_primitives.Integers.MkInt 200 -> mk_i32 (-542412)
  | Rust_primitives.Integers.MkInt 201 -> mk_i32 (-2831860)
  | Rust_primitives.Integers.MkInt 202 -> mk_i32 (-1671176)
  | Rust_primitives.Integers.MkInt 203 -> mk_i32 (-1846953)
  | Rust_primitives.Integers.MkInt 204 -> mk_i32 (-2584293)
  | Rust_primitives.Integers.MkInt 205 -> mk_i32 (-3724270)
  | Rust_primitives.Integers.MkInt 206 -> mk_i32 594136
  | Rust_primitives.Integers.MkInt 207 -> mk_i32 (-3776993)
  | Rust_primitives.Integers.MkInt 208 -> mk_i32 (-2013608)
  | Rust_primitives.Integers.MkInt 209 -> mk_i32 2432395
  | Rust_primitives.Integers.MkInt 210 -> mk_i32 2454455
  | Rust_primitives.Integers.MkInt 211 -> mk_i32 (-164721)
  | Rust_primitives.Integers.MkInt 212 -> mk_i32 1957272
  | Rust_primitives.Integers.MkInt 213 -> mk_i32 3369112
  | Rust_primitives.Integers.MkInt 214 -> mk_i32 185531
  | Rust_primitives.Integers.MkInt 215 -> mk_i32 (-1207385)
  | Rust_primitives.Integers.MkInt 216 -> mk_i32 (-3183426)
  | Rust_primitives.Integers.MkInt 217 -> mk_i32 162844
  | Rust_primitives.Integers.MkInt 218 -> mk_i32 1616392
  | Rust_primitives.Integers.MkInt 219 -> mk_i32 3014001
  | Rust_primitives.Integers.MkInt 220 -> mk_i32 810149
  | Rust_primitives.Integers.MkInt 221 -> mk_i32 1652634
  | Rust_primitives.Integers.MkInt 222 -> mk_i32 (-3694233)
  | Rust_primitives.Integers.MkInt 223 -> mk_i32 (-1799107)
  | Rust_primitives.Integers.MkInt 224 -> mk_i32 (-3038916)
  | Rust_primitives.Integers.MkInt 225 -> mk_i32 3523897
  | Rust_primitives.Integers.MkInt 226 -> mk_i32 3866901
  | Rust_primitives.Integers.MkInt 227 -> mk_i32 269760
  | Rust_primitives.Integers.MkInt 228 -> mk_i32 2213111
  | Rust_primitives.Integers.MkInt 229 -> mk_i32 (-975884)
  | Rust_primitives.Integers.MkInt 230 -> mk_i32 1717735
  | Rust_primitives.Integers.MkInt 231 -> mk_i32 472078
  | Rust_primitives.Integers.MkInt 232 -> mk_i32 (-426683)
  | Rust_primitives.Integers.MkInt 233 -> mk_i32 1723600
  | Rust_primitives.Integers.MkInt 234 -> mk_i32 (-1803090)
  | Rust_primitives.Integers.MkInt 235 -> mk_i32 1910376
  | Rust_primitives.Integers.MkInt 236 -> mk_i32 (-1667432)
  | Rust_primitives.Integers.MkInt 237 -> mk_i32 (-1104333)
  | Rust_primitives.Integers.MkInt 238 -> mk_i32 (-260646)
  | Rust_primitives.Integers.MkInt 239 -> mk_i32 (-3833893)
  | Rust_primitives.Integers.MkInt 240 -> mk_i32 (-2939036)
  | Rust_primitives.Integers.MkInt 241 -> mk_i32 (-2235985)
  | Rust_primitives.Integers.MkInt 242 -> mk_i32 (-420899)
  | Rust_primitives.Integers.MkInt 243 -> mk_i32 (-2286327)
  | Rust_primitives.Integers.MkInt 244 -> mk_i32 183443
  | Rust_primitives.Integers.MkInt 245 -> mk_i32 (-976891)
  | Rust_primitives.Integers.MkInt 246 -> mk_i32 1612842
  | Rust_primitives.Integers.MkInt 247 -> mk_i32 (-3545687)
  | Rust_primitives.Integers.MkInt 248 -> mk_i32 (-554416)
  | Rust_primitives.Integers.MkInt 249 -> mk_i32 3919660
  | Rust_primitives.Integers.MkInt 250 -> mk_i32 (-48306)
  | Rust_primitives.Integers.MkInt 251 -> mk_i32 (-1362209)
  | Rust_primitives.Integers.MkInt 252 -> mk_i32 3937738
  | Rust_primitives.Integers.MkInt 253 -> mk_i32 1400424
  | Rust_primitives.Integers.MkInt 254 -> mk_i32 (-846154)
  | Rust_primitives.Integers.MkInt 255 -> mk_i32 1976782
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
