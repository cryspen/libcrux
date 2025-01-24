module Libcrux_ml_kem.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let inz (value: u8) =
  let v__orig_value:u8 = value in
  let value:u16 = cast (value <: u8) <: u16 in
  let result:u8 =
    cast ((Core.Num.impl__u16__wrapping_add (~.value <: u16) (mk_u16 1) <: u16) >>! mk_i32 8 <: u16)
    <:
    u8
  in
  let res:u8 = result &. mk_u8 1 in
  let _:Prims.unit =
    if v v__orig_value = 0
    then
      (assert (value == zero);
        lognot_lemma value;
        assert ((~.value +. (mk_u16 1)) == zero);
        assert ((Core.Num.impl__u16__wrapping_add (~.value <: u16) (mk_u16 1) <: u16) == zero);
        logor_lemma value zero;
        assert ((value |. (Core.Num.impl__u16__wrapping_add (~.value <: u16) (mk_u16 1) <: u16)
              <:
              u16) ==
            value);
        assert (v result == v ((value >>! (mk_i32 8))));
        assert ((v value / pow2 8) == 0);
        assert (result == (mk_u8 0));
        logand_lemma (mk_u8 1) result;
        assert (res == (mk_u8 0)))
    else
      (assert (v value <> 0);
        lognot_lemma value;
        assert (v (~.value) = pow2 16 - 1 - v value);
        assert (v (~.value) + 1 = pow2 16 - v value);
        assert (v (value) <= pow2 8 - 1);
        assert ((v (~.value) + 1) = (pow2 16 - pow2 8) + (pow2 8 - v value));
        assert ((v (~.value) + 1) = (pow2 8 - 1) * pow2 8 + (pow2 8 - v value));
        assert ((v (~.value) + 1) / pow2 8 = (pow2 8 - 1));
        assert (v ((Core.Num.impl__u16__wrapping_add (~.value <: u16) (mk_u16 1) <: u16) >>!
                (mk_i32 8)) =
            pow2 8 - 1);
        assert (result = ones);
        logand_lemma (mk_u8 1) result;
        assert (res = (mk_u8 1)))
  in
  res

let is_non_zero (value: u8) = Core.Hint.black_box #u8 (inz value <: u8)

let compare (lhs rhs: t_Slice u8) =
  let (r: u8):u8 = mk_u8 0 in
  let r:u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #u8 lhs <: usize)
      (fun r i ->
          let r:u8 = r in
          let i:usize = i in
          v i <= Seq.length lhs /\
          (if (Seq.slice lhs 0 (v i) = Seq.slice rhs 0 (v i))
            then r == (mk_u8 0)
            else ~(r == (mk_u8 0))))
      r
      (fun r i ->
          let r:u8 = r in
          let i:usize = i in
          let nr:u8 = r |. ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) in
          let _:Prims.unit =
            if r =. (mk_u8 0)
            then
              (if (Seq.index lhs (v i) = Seq.index rhs (v i))
                then
                  (logxor_lemma (Seq.index lhs (v i)) (Seq.index rhs (v i));
                    assert (((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) = zero);
                    logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
                    assert (nr = r);
                    assert (forall j. Seq.index (Seq.slice lhs 0 (v i)) j == Seq.index lhs j);
                    assert (forall j. Seq.index (Seq.slice rhs 0 (v i)) j == Seq.index rhs j);
                    eq_intro (Seq.slice lhs 0 ((v i) + 1)) (Seq.slice rhs 0 ((v i) + 1)))
                else
                  (logxor_lemma (Seq.index lhs (v i)) (Seq.index rhs (v i));
                    assert (((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) <> zero);
                    logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
                    assert (v nr > 0);
                    assert (Seq.index (Seq.slice lhs 0 ((v i) + 1)) (v i) <>
                        Seq.index (Seq.slice rhs 0 ((v i) + 1)) (v i));
                    assert (Seq.slice lhs 0 ((v i) + 1) <> Seq.slice rhs 0 ((v i) + 1))))
            else
              (logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
                assert (v nr >= v r);
                assert (Seq.slice lhs 0 (v i) <> Seq.slice rhs 0 (v i));
                if (Seq.slice lhs 0 ((v i) + 1) = Seq.slice rhs 0 ((v i) + 1))
                then
                  (assert (forall j.
                          j < (v i) + 1 ==>
                          Seq.index (Seq.slice lhs 0 ((v i) + 1)) j ==
                          Seq.index (Seq.slice rhs 0 ((v i) + 1)) j);
                    eq_intro (Seq.slice lhs 0 (v i)) (Seq.slice rhs 0 (v i));
                    assert (False)))
          in
          let r:u8 = nr in
          r)
  in
  is_non_zero r

#push-options "--ifuel 0 --z3rlimit 50"

let select_ct (lhs rhs: t_Slice u8) (selector: u8) =
  let mask:u8 = Core.Num.impl__u8__wrapping_sub (is_non_zero selector <: u8) (mk_u8 1) in
  let _:Prims.unit =
    assert (if selector = (mk_u8 0) then mask = ones else mask = zero);
    lognot_lemma mask;
    assert (if selector = (mk_u8 0) then ~.mask = zero else ~.mask = ones)
  in
  let out:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let out:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
      (fun out i ->
          let out:t_Array u8 (mk_usize 32) = out in
          let i:usize = i in
          v i <= v Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE /\
          (forall j.
              j < v i ==>
              (if (selector =. (mk_u8 0))
                then Seq.index out j == Seq.index lhs j
                else Seq.index out j == Seq.index rhs j)) /\
          (forall j. j >= v i ==> Seq.index out j == (mk_u8 0)))
      out
      (fun out i ->
          let out:t_Array u8 (mk_usize 32) = out in
          let i:usize = i in
          let _:Prims.unit = assert ((out.[ i ] <: u8) = (mk_u8 0)) in
          let outi:u8 =
            ((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
          in
          let _:Prims.unit =
            if (selector = (mk_u8 0))
            then
              (logand_lemma (lhs.[ i ] <: u8) mask;
                assert (((lhs.[ i ] <: u8) &. mask <: u8) == (lhs.[ i ] <: u8));
                logand_lemma (rhs.[ i ] <: u8) (~.mask);
                assert (((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) == zero);
                logor_lemma ((lhs.[ i ] <: u8) &. mask <: u8)
                  ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8);
                assert ((((lhs.[ i ] <: u8) &. mask <: u8) |.
                      ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
                      <:
                      u8) ==
                    (lhs.[ i ] <: u8));
                logor_lemma (out.[ i ] <: u8) (lhs.[ i ] <: u8);
                assert (((out.[ i ] <: u8) |.
                      (((lhs.[ i ] <: u8) &. mask <: u8) |.
                        ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
                        <:
                        u8)
                      <:
                      u8) ==
                    (lhs.[ i ] <: u8));
                assert (outi = (lhs.[ i ] <: u8)))
            else
              (logand_lemma (lhs.[ i ] <: u8) mask;
                assert (((lhs.[ i ] <: u8) &. mask <: u8) == zero);
                logand_lemma (rhs.[ i ] <: u8) (~.mask);
                assert (((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) == (rhs.[ i ] <: u8));
                logor_lemma (rhs.[ i ] <: u8) zero;
                assert ((logor zero (rhs.[ i ] <: u8)) == (rhs.[ i ] <: u8));
                assert ((((lhs.[ i ] <: u8) &. mask <: u8) |.
                      ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)) ==
                    (rhs.[ i ] <: u8));
                logor_lemma (out.[ i ] <: u8) (rhs.[ i ] <: u8);
                assert (((out.[ i ] <: u8) |.
                      (((lhs.[ i ] <: u8) &. mask <: u8) |.
                        ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
                        <:
                        u8)
                      <:
                      u8) ==
                    (rhs.[ i ] <: u8));
                assert (outi = (rhs.[ i ] <: u8)))
          in
          let out:t_Array u8 (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i outi
          in
          out)
  in
  let _:Prims.unit = if (selector =. (mk_u8 0)) then (eq_intro out lhs) else (eq_intro out rhs) in
  out

#pop-options

let compare_ciphertexts_in_constant_time (lhs rhs: t_Slice u8) =
  Core.Hint.black_box #u8 (compare lhs rhs <: u8)

let select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8) =
  Core.Hint.black_box #(t_Array u8 (mk_usize 32))
    (select_ct lhs rhs selector <: t_Array u8 (mk_usize 32))

let compare_ciphertexts_select_shared_secret_in_constant_time (lhs_c rhs_c lhs_s rhs_s: t_Slice u8) =
  let selector:u8 = compare_ciphertexts_in_constant_time lhs_c rhs_c in
  select_shared_secret_in_constant_time lhs_s rhs_s selector
