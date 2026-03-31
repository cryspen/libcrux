module Hacspec_ml_dsa.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Pre-computed zetas: zetas[k] = ζ^BitRev8(k) mod q — FIPS 204, Appendix B.
let v_ZETAS: t_Array i32 (mk_usize 256) =
  let list =
    [
      mk_i32 1; mk_i32 4808194; mk_i32 3765607; mk_i32 3761513; mk_i32 5178923; mk_i32 5496691;
      mk_i32 5234739; mk_i32 5178987; mk_i32 7778734; mk_i32 3542485; mk_i32 2682288; mk_i32 2129892;
      mk_i32 3764867; mk_i32 7375178; mk_i32 557458; mk_i32 7159240; mk_i32 5010068; mk_i32 4317364;
      mk_i32 2663378; mk_i32 6705802; mk_i32 4855975; mk_i32 7946292; mk_i32 676590; mk_i32 7044481;
      mk_i32 5152541; mk_i32 1714295; mk_i32 2453983; mk_i32 1460718; mk_i32 7737789; mk_i32 4795319;
      mk_i32 2815639; mk_i32 2283733; mk_i32 3602218; mk_i32 3182878; mk_i32 2740543; mk_i32 4793971;
      mk_i32 5269599; mk_i32 2101410; mk_i32 3704823; mk_i32 1159875; mk_i32 394148; mk_i32 928749;
      mk_i32 1095468; mk_i32 4874037; mk_i32 2071829; mk_i32 4361428; mk_i32 3241972; mk_i32 2156050;
      mk_i32 3415069; mk_i32 1759347; mk_i32 7562881; mk_i32 4805951; mk_i32 3756790; mk_i32 6444618;
      mk_i32 6663429; mk_i32 4430364; mk_i32 5483103; mk_i32 3192354; mk_i32 556856; mk_i32 3870317;
      mk_i32 2917338; mk_i32 1853806; mk_i32 3345963; mk_i32 1858416; mk_i32 3073009; mk_i32 1277625;
      mk_i32 5744944; mk_i32 3852015; mk_i32 4183372; mk_i32 5157610; mk_i32 5258977; mk_i32 8106357;
      mk_i32 2508980; mk_i32 2028118; mk_i32 1937570; mk_i32 4564692; mk_i32 2811291; mk_i32 5396636;
      mk_i32 7270901; mk_i32 4158088; mk_i32 1528066; mk_i32 482649; mk_i32 1148858; mk_i32 5418153;
      mk_i32 7814814; mk_i32 169688; mk_i32 2462444; mk_i32 5046034; mk_i32 4213992; mk_i32 4892034;
      mk_i32 1987814; mk_i32 5183169; mk_i32 1736313; mk_i32 235407; mk_i32 5130263; mk_i32 3258457;
      mk_i32 5801164; mk_i32 1787943; mk_i32 5989328; mk_i32 6125690; mk_i32 3482206; mk_i32 4197502;
      mk_i32 7080401; mk_i32 6018354; mk_i32 7062739; mk_i32 2461387; mk_i32 3035980; mk_i32 621164;
      mk_i32 3901472; mk_i32 7153756; mk_i32 2925816; mk_i32 3374250; mk_i32 1356448; mk_i32 5604662;
      mk_i32 2683270; mk_i32 5601629; mk_i32 4912752; mk_i32 2312838; mk_i32 7727142; mk_i32 7921254;
      mk_i32 348812; mk_i32 8052569; mk_i32 1011223; mk_i32 6026202; mk_i32 4561790; mk_i32 6458164;
      mk_i32 6143691; mk_i32 1744507; mk_i32 1753; mk_i32 6444997; mk_i32 5720892; mk_i32 6924527;
      mk_i32 2660408; mk_i32 6600190; mk_i32 8321269; mk_i32 2772600; mk_i32 1182243; mk_i32 87208;
      mk_i32 636927; mk_i32 4415111; mk_i32 4423672; mk_i32 6084020; mk_i32 5095502; mk_i32 4663471;
      mk_i32 8352605; mk_i32 822541; mk_i32 1009365; mk_i32 5926272; mk_i32 6400920; mk_i32 1596822;
      mk_i32 4423473; mk_i32 4620952; mk_i32 6695264; mk_i32 4969849; mk_i32 2678278; mk_i32 4611469;
      mk_i32 4829411; mk_i32 635956; mk_i32 8129971; mk_i32 5925040; mk_i32 4234153; mk_i32 6607829;
      mk_i32 2192938; mk_i32 6653329; mk_i32 2387513; mk_i32 4768667; mk_i32 8111961; mk_i32 5199961;
      mk_i32 3747250; mk_i32 2296099; mk_i32 1239911; mk_i32 4541938; mk_i32 3195676; mk_i32 2642980;
      mk_i32 1254190; mk_i32 8368000; mk_i32 2998219; mk_i32 141835; mk_i32 8291116; mk_i32 2513018;
      mk_i32 7025525; mk_i32 613238; mk_i32 7070156; mk_i32 6161950; mk_i32 7921677; mk_i32 6458423;
      mk_i32 4040196; mk_i32 4908348; mk_i32 2039144; mk_i32 6500539; mk_i32 7561656; mk_i32 6201452;
      mk_i32 6757063; mk_i32 2105286; mk_i32 6006015; mk_i32 6346610; mk_i32 586241; mk_i32 7200804;
      mk_i32 527981; mk_i32 5637006; mk_i32 6903432; mk_i32 1994046; mk_i32 2491325; mk_i32 6987258;
      mk_i32 507927; mk_i32 7192532; mk_i32 7655613; mk_i32 6545891; mk_i32 5346675; mk_i32 8041997;
      mk_i32 2647994; mk_i32 3009748; mk_i32 5767564; mk_i32 4148469; mk_i32 749577; mk_i32 4357667;
      mk_i32 3980599; mk_i32 2569011; mk_i32 6764887; mk_i32 1723229; mk_i32 1665318; mk_i32 2028038;
      mk_i32 1163598; mk_i32 5011144; mk_i32 3994671; mk_i32 8368538; mk_i32 7009900; mk_i32 3020393;
      mk_i32 3363542; mk_i32 214880; mk_i32 545376; mk_i32 7609976; mk_i32 3105558; mk_i32 7277073;
      mk_i32 508145; mk_i32 7826699; mk_i32 860144; mk_i32 3430436; mk_i32 140244; mk_i32 6866265;
      mk_i32 6195333; mk_i32 3123762; mk_i32 2358373; mk_i32 6187330; mk_i32 5365997; mk_i32 6663603;
      mk_i32 2926054; mk_i32 7987710; mk_i32 8077412; mk_i32 3531229; mk_i32 4405932; mk_i32 4606686;
      mk_i32 1900052; mk_i32 7598542; mk_i32 1054478; mk_i32 7648983
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 256);
  Rust_primitives.Hax.array_of_list 256 list

/// BitRev8(m) — FIPS 204, Algorithm 43.
/// Reverses the bits of an 8-bit integer.
let bit_rev_8_ (m: usize) : Prims.Pure usize (requires m <. mk_usize 256) (fun _ -> Prims.l_True) =
  let r:usize = mk_usize 0 in
  let v:usize = m in
  let (r: usize), (v: usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 8)
      (fun temp_0_ temp_1_ ->
          let (r: usize), (v: usize) = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      (r, v <: (usize & usize))
      (fun temp_0_ e_i ->
          let (r: usize), (v: usize) = temp_0_ in
          let e_i:i32 = e_i in
          let r:usize = (r <<! mk_i32 1 <: usize) |. (v &. mk_usize 1 <: usize) in
          let v:usize = v >>! mk_i32 1 in
          r, v <: (usize & usize))
  in
  r

/// Single Cooley-Tukey butterfly layer of the NTT — FIPS 204, Algorithm 41.
/// `layer` is the bit-shift exponent: len = 1 << layer.
/// For NTT, layers are applied from 7 down to 0 (len = 128, 64, ..., 1).
/// The zeta index for block `round` at this layer is `128/len + round`.
let ntt_layer (p: t_Array i32 (mk_usize 256)) (layer: usize)
    : Prims.Pure (t_Array i32 (mk_usize 256))
      (requires layer <=. mk_usize 7)
      (fun _ -> Prims.l_True) =
  let len:usize = mk_usize 1 <<! layer in
  let k:usize = mk_usize 128 /! len in
  Hacspec_ml_dsa.createi #i32
    (mk_usize 256)
    #(usize -> i32)
    (fun i ->
        let i:usize = i in
        let round:usize = i /! (mk_usize 2 *! len <: usize) in
        let idx:usize = i %! (mk_usize 2 *! len <: usize) in
        let z:i64 = cast (v_ZETAS.[ round +! k <: usize ] <: i32) <: i64 in
        if idx <. len
        then
          let t:i32 =
            Hacspec_ml_dsa.Arithmetic.mod_q (z *! (cast (p.[ i +! len <: usize ] <: i32) <: i64)
                <:
                i64)
          in
          Hacspec_ml_dsa.Arithmetic.mod_q ((cast (p.[ i ] <: i32) <: i64) +!
              (cast (t <: i32) <: i64)
              <:
              i64)
        else
          let t:i32 =
            Hacspec_ml_dsa.Arithmetic.mod_q (z *! (cast (p.[ i ] <: i32) <: i64) <: i64)
          in
          Hacspec_ml_dsa.Arithmetic.mod_q ((cast (p.[ i -! len <: usize ] <: i32) <: i64) -!
              (cast (t <: i32) <: i64)
              <:
              i64))

/// NTT(w) — FIPS 204, Algorithm 41.
/// Computes the Number Theoretic Transform of polynomial w.
let ntt (w: t_Array i32 (mk_usize 256)) : t_Array i32 (mk_usize 256) =
  let p:t_Array i32 (mk_usize 256) = ntt_layer w (mk_usize 7) in
  let p:t_Array i32 (mk_usize 256) = ntt_layer p (mk_usize 6) in
  let p:t_Array i32 (mk_usize 256) = ntt_layer p (mk_usize 5) in
  let p:t_Array i32 (mk_usize 256) = ntt_layer p (mk_usize 4) in
  let p:t_Array i32 (mk_usize 256) = ntt_layer p (mk_usize 3) in
  let p:t_Array i32 (mk_usize 256) = ntt_layer p (mk_usize 2) in
  let p:t_Array i32 (mk_usize 256) = ntt_layer p (mk_usize 1) in
  ntt_layer p (mk_usize 0)

/// Single Gentleman-Sande butterfly layer of the inverse NTT — FIPS 204, Algorithm 42.
/// `layer` is the bit-shift exponent: len = 1 << layer.
/// For INTT, layers are applied from 0 up to 7 (len = 1, 2, ..., 128).
/// The zeta index for block `round` at this layer is `256/len - 1 - round`.
let intt_layer (p: t_Array i32 (mk_usize 256)) (layer: usize)
    : Prims.Pure (t_Array i32 (mk_usize 256))
      (requires layer <=. mk_usize 7)
      (fun _ -> Prims.l_True) =
  let len:usize = mk_usize 1 <<! layer in
  let k:usize = (mk_usize 256 /! len <: usize) -! mk_usize 1 in
  Hacspec_ml_dsa.createi #i32
    (mk_usize 256)
    #(usize -> i32)
    (fun i ->
        let i:usize = i in
        let round:usize = i /! (mk_usize 2 *! len <: usize) in
        let idx:usize = i %! (mk_usize 2 *! len <: usize) in
        if idx <. len
        then
          Hacspec_ml_dsa.Arithmetic.mod_q ((cast (p.[ i ] <: i32) <: i64) +!
              (cast (p.[ i +! len <: usize ] <: i32) <: i64)
              <:
              i64)
        else
          let z:i64 =
            ((cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64) -!
              (cast (v_ZETAS.[ k -! round <: usize ] <: i32) <: i64)
              <:
              i64) %!
            (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
          in
          Hacspec_ml_dsa.Arithmetic.mod_q (z *!
              ((cast (p.[ i -! len <: usize ] <: i32) <: i64) -! (cast (p.[ i ] <: i32) <: i64)
                <:
                i64)
              <:
              i64))

/// Multiply all coefficients by 256⁻¹ mod q = 8347681.
let reduce_polynomial (p: t_Array i32 (mk_usize 256)) : t_Array i32 (mk_usize 256) =
  let f:i64 = mk_i64 8347681 in
  Hacspec_ml_dsa.createi #i32
    (mk_usize 256)
    #(usize -> i32)
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.Arithmetic.mod_q (f *! (cast (p.[ i ] <: i32) <: i64) <: i64) <: i32)

/// NTT⁻¹(ŵ) — FIPS 204, Algorithm 42.
/// Computes the inverse Number Theoretic Transform.
let intt (w_hat: t_Array i32 (mk_usize 256)) : t_Array i32 (mk_usize 256) =
  let p:t_Array i32 (mk_usize 256) = intt_layer w_hat (mk_usize 0) in
  let p:t_Array i32 (mk_usize 256) = intt_layer p (mk_usize 1) in
  let p:t_Array i32 (mk_usize 256) = intt_layer p (mk_usize 2) in
  let p:t_Array i32 (mk_usize 256) = intt_layer p (mk_usize 3) in
  let p:t_Array i32 (mk_usize 256) = intt_layer p (mk_usize 4) in
  let p:t_Array i32 (mk_usize 256) = intt_layer p (mk_usize 5) in
  let p:t_Array i32 (mk_usize 256) = intt_layer p (mk_usize 6) in
  let p:t_Array i32 (mk_usize 256) = intt_layer p (mk_usize 7) in
  reduce_polynomial p
