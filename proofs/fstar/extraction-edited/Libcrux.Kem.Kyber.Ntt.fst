module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul


let v_ZETAS_TIMES_MONTGOMERY_R =
  let list : list (i32_b 1664) =
    [
      (-1044l); (-758l); (-359l); (-1517l); 1493l; 1422l; 287l; 202l; (-171l); 622l; 1577l; 182l;
      962l; (-1202l); (-1474l); 1468l; 573l; (-1325l); 264l; 383l; (-829l); 1458l; (-1602l); (-130l);
      (-681l); 1017l; 732l; 608l; (-1542l); 411l; (-205l); (-1571l); 1223l; 652l; (-552l); 1015l;
      (-1293l); 1491l; (-282l); (-1544l); 516l; (-8l); (-320l); (-666l); (-1618l); (-1162l); 126l;
      1469l; (-853l); (-90l); (-271l); 830l; 107l; (-1421l); (-247l); (-951l); (-398l); 961l;
      (-1508l); (-725l); 448l; (-1065l); 677l; (-1275l); (-1103l); 430l; 555l; 843l; (-1251l); 871l;
      1550l; 105l; 422l; 587l; 177l; (-235l); (-291l); (-460l); 1574l; 1653l; (-246l); 778l; 1159l;
      (-147l); (-777l); 1483l; (-602l); 1119l; (-1590l); 644l; (-872l); 349l; 418l; 329l; (-156l);
      (-75l); 817l; 1097l; 603l; 610l; 1322l; (-1285l); (-1465l); 384l; (-1215l); (-136l); 1218l;
      (-1335l); (-874l); 220l; (-1187l); (-1659l); (-1185l); (-1530l); (-1278l); 794l; (-1510l);
      (-854l); (-870l); 478l; (-108l); (-308l); 996l; 991l; 958l; (-1460l); 1522l; 1628l
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  FStar.Pervasives.assert_norm (List.Tot.index list 1 == -758l);
  Seq.of_list list
  
open Libcrux.Kem.Kyber.Arithmetic

#push-options "--z3rlimit 50"
let ntt_multiply_binomials (a0,a1) (b0,b1) zeta =
  let r0 = montgomery_reduce (mul_i32_b a1 b1) in
  let res = 
  montgomery_reduce (add_i32_b (mul_i32_b a0 b0) (mul_i32_b r0 zeta)),
  montgomery_reduce (add_i32_b (mul_i32_b a0 b1) (mul_i32_b a1 b0)) in
  res
#pop-options

val mul_zeta_red   (#v_K:usize{v v_K >= 1 /\ v v_K <= 4})
                   (#b:nat{b <= v v_K * 3328 * 64}) 
                   (zeta_i:usize{v zeta_i > 0 /\ v zeta_i <= 128} )
                   (layer:usize{v layer > 0 /\ 
                                v layer <= 7 /\ 
                                v zeta_i == pow2 (8 - v layer) /\ 
                                b == v v_K * 3328 * pow2(v layer - 1)})
                   (x:i32_b (2*b))
                   (i:usize{v i < 128 / pow2 (v layer)}) :
                   i32_b (2*b)
let mul_zeta_red #v_K #b zeta_i layer x i = 
    let zeta_i = zeta_i -! sz 1 -! i in
    let zeta:i32_b 1664 = v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] in
    if layer <=. sz 6 then (
      assert (b <= 4 * 3328 * 32);
      assert (2*b*1664 < pow2 31);
      let product:i32_b (2 * b * 1664) = mul_i32_b x zeta in
      let res = montgomery_reduce product in
      res
    ) else (
      assert (v i  < 1);
      assert (zeta_i = sz 1);
      assert (zeta = -758l);
      let zeta:i32_b 758 = zeta in
      let product:i32_b (2 * b * 758) = mul_i32_b x zeta in
      let res = montgomery_reduce product in
      res
    )


val lemma_zeta_decr: orig:usize -> fin:usize -> layer:usize{v layer <= 7} ->
  Lemma (v fin == v orig - 128/(pow2 (v layer)) /\
         v orig == pow2 (8 - v layer) ==>
         v fin == pow2 (7 - v layer))
let lemma_zeta_decr orig fin layer = ()

#push-options "--ifuel 0 --z3rlimit 1200"
let invert_ntt_at_layer #v_K #b zeta_i re layer =
  let step:usize = sz 1 <<! layer in
  assert (v step > 0);
  assert (v step == pow2 (v layer));
  let orig_re = re in
  let orig_zeta_i = zeta_i in
  [@ inline_let]
  let inv = fun (acc:t_PolynomialRingElement_b (2*b) & usize) (i:usize) ->
    let (re,zeta_i) = acc in 
    v zeta_i == v orig_zeta_i - v i /\
    (forall k. (v k >= 2 * v i * v step (* + 2 * v step *)) ==> re.f_coefficients.[k] == orig_re.f_coefficients.[k]) 
  in
  let re, zeta_i: (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b) & usize) =
    Rust_primitives.Iterators.foldi_range #_ #(t_PolynomialRingElement_b (2*b) & usize) #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step
            }
      (cast_poly_b #b #(2*b) re, zeta_i <: (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b) & usize) = temp_0_ in
          let round:usize = round in
          let orig_re_round = re in
          let zeta_i:usize = zeta_i -! sz 1 in
          assert(v round * v step < 128);
          assert(v round * v step + v step <= 128);
          assert(v round * v step * 2 <= 254);
          assert(v round * v step * 2 + 2 * v step <= 256);
          let offset:usize = (round *! step) *! sz 2 in
          assert (v offset + 2 * v step <= 256);
          assert (v offset + v step <= 256);
          assert (forall k. v k >= v offset ==> re.f_coefficients.[k] == orig_re.f_coefficients.[k]);
          [@ inline_let]
          let inv = fun (acc:t_PolynomialRingElement_b (2 * b)) (i:usize) ->
            (forall k. (v k >= v i /\ v k < v offset + v step) ==> acc.f_coefficients.[k] == orig_re.f_coefficients.[k]) /\
            (forall k. (v k >= v i + v step) ==> acc.f_coefficients.[k] == orig_re.f_coefficients.[k])
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2 * b) =
            Rust_primitives.Iterators.foldi_range #_ #_  #inv {
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
            }
              re
              (fun re j ->
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2 * b) = re in
                  assert (re.f_coefficients.[j] == orig_re_round.f_coefficients.[j]);
                  assert (re.f_coefficients.[j +! step] == orig_re_round.f_coefficients.[j +! step]);
                  assert (re.f_coefficients.[j] == orig_re.f_coefficients.[j]);
                  assert (re.f_coefficients.[j +! step] == orig_re.f_coefficients.[j +! step]);
                  let re_j:i32_b b = orig_re.f_coefficients.[j] in
                  let re_j_step:i32_b b = orig_re.f_coefficients.[j +! step] in
                  let j:usize = j in
                  let a_minus_b:i32_b (2*b) = sub_i32_b re_j_step re_j in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2 * b) =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        (add_i32_b re_j re_j_step)
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2 * b)
                  in
                  let red = mul_zeta_red #v_K #b orig_zeta_i layer a_minus_b round in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b) =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        red
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b)
                  in
                  re)
          in
          re, zeta_i <: t_PolynomialRingElement_b (2*b) & usize)
  in
  let hax_temp_output:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b) = re in
  lemma_zeta_decr orig_zeta_i zeta_i layer;
  zeta_i, hax_temp_output <: (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b))  
#pop-options

#push-options "--z3rlimit 500"
let invert_ntt_montgomery v_K re =
  let _:Prims.unit = () <: Prims.unit in
  let b = v v_K * 3328 in
  assert (v v_K <= 4);
  assert (b <= 4 * 3328);
  let zeta_i:usize = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 2 in
  assert (v zeta_i == pow2 (8 - 1));
  let tmp0, out:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b)) =
    invert_ntt_at_layer #v_K #b zeta_i re (sz 1)
  in
  let zeta_i:usize = tmp0 in
  let hoist1 = out in
  let re = hoist1 in
  let tmp0, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (4*b)) =
    invert_ntt_at_layer #v_K zeta_i re (sz 2)
  in
  let zeta_i:usize = tmp0 in
  let tmp0, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*b)) =
    invert_ntt_at_layer #v_K zeta_i re (sz 3)
  in
  let zeta_i:usize = tmp0 in
  assert (8*b = v v_K * 3328 * pow2 (4 - 1));
  let tmp0, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (16*b)) =
    invert_ntt_at_layer #v_K zeta_i re (sz 4)
  in
  let zeta_i:usize = tmp0 in
  assert (16*b == v v_K * 3328 * pow2 (5 - 1));
  let tmp0, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (32*b)) =
    invert_ntt_at_layer #v_K zeta_i re (sz 5)
  in
  let zeta_i:usize = tmp0 in
  assert (32*b = v v_K * 3328 * pow2 (6 - 1));
  let tmp0, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*b)) =
    invert_ntt_at_layer #v_K zeta_i re (sz 6)
  in
  let zeta_i:usize = tmp0 in
  assert (64*b = v v_K * 3328 * pow2 (7 - 1));
  let tmp0, re:(usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (128*b)) =
    invert_ntt_at_layer #v_K zeta_i re (sz 7)
  in
  let zeta_i:usize = tmp0 in
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  admit();
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*b) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 8
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (128*b) = re in
          let i:usize = i in
          {
            re with
            Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i
              (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (re
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                    <:
                    i32)
                <:
                i32)
            <:
            t_Array i32 (sz 256)
          }
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*b))
  in
  re 
#pop-options

#push-options "--z3rlimit 500"
val mul_zeta_red2   (#b:nat{b <= 31175}) 
                   (zeta_i:usize{v zeta_i >= 0 /\ v zeta_i <= 63} )
                   (layer:usize{v layer > 0 /\ 
                                v layer <= 7 /\ 
                                v zeta_i == pow2 (7 - v layer) - 1})
                   (x:i32_b b)
                   (i:usize{v i < 128/(pow2 (v layer))})
                   : i32_b 3328
let mul_zeta_red2 #b zeta_i layer x i = 
    let zeta_i = zeta_i +! sz 1 +! i in
    let zeta = v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] in
    assert (b * 1664 < 65536 * 3328);
    let red = Libcrux.Kem.Kyber.Arithmetic.montgomery_multiply_sfe_by_fer #(3328+b) #1664 x
                             (v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32) in
    red
#pop-options

#push-options "--ifuel 0 --z3rlimit 5000"
let ntt_at_layer #b zeta_i re layer initial_coefficient_bound =
  let step = sz 1 <<! layer in
  let loop_end = sz 128 /! step in
  assert (v loop_end == pow2 (7 - v layer));
  let orig_re = re in
  let orig_zeta_i = zeta_i in
  [@ inline_let]
  let inv = fun (acc:t_PolynomialRingElement_b (3328+b) & usize) (i:usize) ->
    let (re,zeta_i) = acc in 
    v zeta_i == v orig_zeta_i + v i /\
    (forall k. v k >= 2 * v i * v step  ==> re.f_coefficients.[k] == orig_re.f_coefficients.[k]) 
  in
  let re, zeta_i: (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b) & usize) =
    Rust_primitives.Iterators.foldi_range #_ #(t_PolynomialRingElement_b (3328+b) & usize) #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = loop_end
            }
      (cast_poly_b #b #(3328+b) re, zeta_i)
      (fun temp_0_ round ->
          let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b) & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          assert(v round * v step < 128);
          assert(v round * v step + v step <= 128);
          assert(v round * v step * 2 <= 254);
          assert(v round * v step * 2 + 2 * v step <= 256);
          let offset:usize = (round *! step) *! sz 2 in
          assert (v offset + 2 * v step <= 256);
          assert (v offset + v step <= 256);
          [@ inline_let]
          let inv: t_PolynomialRingElement_b (3328+b) -> int_t usize_inttype -> Type0 = 
            fun (acc:t_PolynomialRingElement_b (3328+b)) (i:usize) ->
            (forall k. (v k >= v i /\ v k < v offset + v step) ==> acc.f_coefficients.[k] == orig_re.f_coefficients.[k]) /\
            (forall k. (v k >= v i + v step) ==> acc.f_coefficients.[k] == orig_re.f_coefficients.[k])
          in
          assert (forall k. (v k >= v offset /\ v k < v offset + v step) ==> re.f_coefficients.[k] == orig_re.f_coefficients.[k]);
          assert (forall k. (v k >= v offset + v step) ==> re.f_coefficients.[k] == orig_re.f_coefficients.[k]);
          assert (inv re offset);
      let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+ b) =
            Rust_primitives.Iterators.foldi_range #usize_inttype #(t_PolynomialRingElement_b (3328+b))  #inv {
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
            }
              re
              (fun re j ->
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b) = re in
                  let j:usize = j in
                  assert (re.f_coefficients.[j] == orig_re.f_coefficients.[j]);
                  assert (re.f_coefficients.[j +! step] == orig_re.f_coefficients.[j +! step]);                      
                  let re_j:i32_b b = orig_re.f_coefficients.[j] in
                  let re_j_step:i32_b b = orig_re.f_coefficients.[j +! step] in
                  let t:i32_b 3328 = mul_zeta_red2 #b orig_zeta_i layer 
                                     re_j_step round in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b) =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (sub_i32_b #b #3328 re_j_step t)
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b) =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        (add_i32_b #b #3328 re_j t)
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b)
                  in
                  re)
          in
          re, zeta_i <: (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b) & usize))
  in
  let _:Prims.unit = () <: Prims.unit in
  let hax_temp_output:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b) = re in
  assert (v zeta_i = v orig_zeta_i + 128/v step);
  assert (v zeta_i = v orig_zeta_i + pow2(7 - v layer));
  assert (v zeta_i = pow2(8 - v layer) - 1);
  zeta_i, hax_temp_output
#pop-options

let ntt_at_layer_3_ #b zeta_i re layer = 
  let tmp0, out =
    ntt_at_layer zeta_i re layer (sz 7879)
  in
  let zeta_i:usize = tmp0 in
  let hax_temp_output = out in
  zeta_i, hax_temp_output
 
let ntt_at_layer_3328_ zeta_i re layer = 
  let tmp0, out =
    ntt_at_layer zeta_i re layer (sz 3328)
  in
  let zeta_i:usize = tmp0 in
  let hax_temp_output = out in
  zeta_i, hax_temp_output

#push-options "--ifuel 0 --z3rlimit 1500"
#restart-solver
let ntt_binomially_sampled_ring_element re =
  let _:Prims.unit = () <: Prims.unit in
  let zeta_i:usize = sz 1 in
  [@ inline_let]
  let inv = fun (acc:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 11207)) (i:usize) -> 
             (v i <= 128) /\
             (forall (j:usize). (v j >= v i /\ v j < 128) ==>
                i32_range (acc <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 11207).f_coefficients.[j] 7) /\ 
             (forall (j:usize). (v j >= v i + 128 /\ v j < 256) ==>
                i32_range (acc <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 11207).f_coefficients.[j] 7)
          in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 11207 = cast_poly_b re in
  assert (inv re (sz 0));
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 11207 =
      Rust_primitives.Iterators.foldi_range #_ #(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 11207) #inv ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128
            }
            <:
            Core.Ops.Range.t_Range usize)
      (cast_poly_b re)
      (fun re j ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 11207 = cast_poly_b re in
          let j:usize = j in
          let t:i32_b (7*1600) =
            mul_i32_b (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! sz 128 <: usize ])
                      (-1600l <: i32_b 1600)
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (11207) =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (j +! sz 128 <: usize)
                (sub_i32_b #7 #11200 (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32_b 7) t)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (11207) =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                j
                (add_i32_b (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ]) t)
            }
          in
          re)
  in
  let _:Prims.unit = () <: Prims.unit in
  assert (v zeta_i = pow2 (7 - 6) - 1);
  let zeta_i, re =
    ntt_at_layer_3_ zeta_i re (sz 6)
  in
  let zeta_i, re =
    ntt_at_layer_3_ zeta_i re (sz 5)
  in
  let zeta_i, re =
    ntt_at_layer_3_ zeta_i re (sz 4)
  in
  let zeta_i, re =
    ntt_at_layer_3_ zeta_i re (sz 3)
  in
  let zeta_i, re =
    ntt_at_layer_3_ zeta_i re (sz 2)
  in
  let zeta_i, re =
    ntt_at_layer_3_ zeta_i re (sz 1)
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (6*3328+11207) = re in
  [@ inline_let]
  let inv = fun (acc:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (6*3328+11207))) (i:usize) -> 
             (v i <= 256) /\
             (forall (j:usize). (v j < v i) ==>
                i32_range (acc <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (6*3328+11207)).f_coefficients.[j] 3328)
  in
  assert (inv re (sz 0));
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (6*3328+11207) =
      Rust_primitives.Iterators.foldi_range #_ #(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (6*3328+11207)) #inv ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (6*3328+11207) = re in
          let rei:i32_b (v v_BARRETT_R) = cast_i32_b #(6*3328+11207) #(v v_BARRETT_R) (re
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]) in
          let rei: i32_b (6*3328+11207) = cast_i32_b #3328 #(6*3328+11207) (
            Libcrux.Kem.Kyber.Arithmetic.barrett_reduce rei) in
          let i:usize = i in
          let re_coeffs:t_Array (i32_b (6*3328+11207)) (sz 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i rei in
          {
            re with
            Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            = re_coeffs
          })
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement = down_cast_poly_b #(6*3328+11207) #3328 re in
  re 
#pop-options


#push-options "--z3rlimit 100"
let ntt_multiply lhs rhs =
  let _:Prims.unit = () <: Prims.unit in
  let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 1 =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 4 <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (cast_poly_b out)
      (fun out i ->
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328 = out in
          let i:usize = i in
          assert (v i * 4 + 4 <= 256);
          let product =
            ntt_multiply_binomials ((lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 4 *! i
                    <:
                    usize ]
                  <:
                  i32_b 3328),
                (lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1
                    <:
                    usize ]
                  <:
                  i32_b 3328))
              ((rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 4 *! i <: usize ] <: i32_b 3328),
                (rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1
                    <:
                    usize ]
                  <:
                  i32_b 3328))
              (v_ZETAS_TIMES_MONTGOMERY_R.[ sz 64 +! i <: usize ] <: i32_b 1664)
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328 =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 4 *! i <: usize)
                product._1
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328 =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                product._2
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328
          in
          let product =
            ntt_multiply_binomials ((lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i
                      <:
                      usize) +!
                    sz 2
                    <:
                    usize ]),
                (lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3
                    <:
                    usize ]))

              ((rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 2
                    <:
                    usize ]),
                (rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3
                    <:
                    usize ]))
              (Core.Ops.Arith.Neg.neg (v_ZETAS_TIMES_MONTGOMERY_R.[ sz 64 +! i <: usize ]) <: i32_b 1664)

          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328 =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                product._1
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328 =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                product._2
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328
          in
          out)
  in
  out
#pop-options

#push-options "--ifuel 0 --z3rlimit 200"
let ntt_vector_u v_VECTOR_U_COMPRESSION_FACTOR re =
  let _:Prims.unit = () <: Prims.unit in
  let zeta_i:usize = sz 0 in
  let zeta_i, re =
    ntt_at_layer_3328_ zeta_i re (sz 7)
  in
  let zeta_i, re =
    ntt_at_layer_3328_ zeta_i re (sz 6)
  in
  let zeta_i, re =
    ntt_at_layer_3328_ zeta_i re (sz 5)
  in
  let zeta_i, re =
    ntt_at_layer_3328_ zeta_i re (sz 4)
  in
  let zeta_i, re =
    ntt_at_layer_3328_ zeta_i re (sz 3)
  in
  let zeta_i, re =
    ntt_at_layer_3328_ zeta_i re (sz 2)
  in
  let zeta_i, re =
    ntt_at_layer_3328_ zeta_i re (sz 1)
  in
  [@ inline_let]
  let inv = fun (acc:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328))) (i:usize) -> 
             (v i <= 256) /\
             (forall (j:usize). (v j < v i) ==>
                i32_range (acc <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328)).f_coefficients.[j] 3328)
  in
  assert (inv re (sz 0));
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328) =
      Rust_primitives.Iterators.foldi_range #_ #(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328)) #inv ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            }
            <:
            Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328) = re in
          let i:usize = i in
          {
            re with
            Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i
              (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (re
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]))
          }
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328))
  in
  down_cast_poly_b #(8*3328) #3328 re 
#pop-options
