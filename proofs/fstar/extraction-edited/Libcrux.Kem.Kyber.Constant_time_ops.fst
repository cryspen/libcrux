module Libcrux.Kem.Kyber.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let is_non_zero (value: u8) =
  let orig_value = value in
  let value:u16 = cast (value <: u8) <: u16 in
  let result:u8 = cast ((Core.Num.impl__u16__wrapping_add (~.value <: u16) 1us <: u16) >>! 8l <: u16) in
  let res:u8 = result &. 1uy in
  if v orig_value = 0 then  (
    assert(value == zero);
    lognot_lemma value;
    assert((~.value +. 1us) == zero);
    assert((Core.Num.impl__u16__wrapping_add (~.value <: u16) 1us <: u16) == zero);
    logor_lemma value zero;
    assert((value |. (Core.Num.impl__u16__wrapping_add (~.value <: u16) 1us <: u16) <: u16) == value);
    assert (v result == v ((value >>! 8l)));
    assert ((v value / pow2 8) == 0);
    assert (result == 0uy);
    logand_lemma 1uy result;
    assert (res == 0uy);
    res)
  else (
    assert (v value <> 0);
    lognot_lemma value;
    assert (v (~.value) = pow2 16 - 1 - v value);
    assert (v (~.value) + 1 = pow2 16 - v value);
    assert (v (value) <= pow2 8 - 1);
    assert ((v (~.value) + 1) = (pow2 16 - pow2 8) + (pow2 8 - v value));
    assert ((v (~.value) + 1) = (pow2 8 - 1) * pow2 8 + (pow2 8 - v value));
    assert ((v (~.value) + 1)/pow2 8 = (pow2 8 - 1));
    assert (v ((Core.Num.impl__u16__wrapping_add (~.value <: u16) 1us <: u16) >>! 8l) = pow2 8 - 1);
    assert (result = ones);
    logand_lemma 1uy result;
    assert (res = 1uy);
    res
  )

let compare_ciphertexts_in_constant_time v_CIPHERTEXT_SIZE lhs rhs =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let (r: u8):u8 = 0uy in
  [@ inline_let]
  let inv = fun (acc:u8) (i:usize) ->
    v i <= v v_CIPHERTEXT_SIZE /\
   (if (Seq.slice lhs 0 (v i) = Seq.slice rhs 0 (v i)) then
      acc == 0uy
    else ~ (acc == 0uy))
  in
  let r:u8 =
    Rust_primitives.Iterators.foldi_range #_ #u8  #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_CIPHERTEXT_SIZE
            }
      r
      (fun r i ->
          let r:u8 = r in
          let i:usize = i in
          let nr = r |. ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) <: u8 in
          if r =. 0uy then (
            if (Seq.index lhs (v i) = Seq.index rhs (v i)) then (
               logxor_lemma (Seq.index lhs (v i)) (Seq.index rhs (v i));
               assert (((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) = zero);
               logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
               assert (nr = r);
               assert (forall j. Seq.index (Seq.slice lhs 0 (v i)) j == Seq.index lhs j);
               assert (forall j. Seq.index (Seq.slice rhs 0 (v i)) j == Seq.index rhs j);
               eq_intro (Seq.slice lhs 0 (v i + 1)) (Seq.slice rhs 0 (v i + 1));
               nr
            )
            else (
               logxor_lemma (Seq.index lhs (v i)) (Seq.index rhs (v i));
               assert (((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8) <>  zero);
               logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
               assert (v nr > 0);
               assert (Seq.index (Seq.slice lhs 0 (v i+1)) (v i) <> 
                       Seq.index (Seq.slice rhs 0 (v i+1)) (v i));
               assert (Seq.slice lhs 0 (v i+1) <> Seq.slice rhs 0 (v i + 1));
               nr
            )
          ) else (
            logor_lemma r ((lhs.[ i ] <: u8) ^. (rhs.[ i ] <: u8) <: u8);
            assert (v nr >= v r);
            assert (Seq.slice lhs 0 (v i) <> Seq.slice rhs 0 (v i));
            if (Seq.slice lhs 0 (v i+1) = Seq.slice rhs 0 (v i + 1)) then
              (assert (forall j. j < v i + 1 ==> Seq.index (Seq.slice lhs 0 (v i+1)) j == Seq.index (Seq.slice rhs 0 (v i+1)) j);
               eq_intro (Seq.slice lhs 0 (v i)) (Seq.slice rhs 0 (v i));
               assert(False))
            else nr
          )
     )
  in
  let res = is_non_zero r in
  res

#push-options "--ifuel 0 --z3rlimit 50"
let select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8) =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let mask:u8 = Core.Num.impl__u8__wrapping_sub (is_non_zero selector <: u8) 1uy in
  assert (if selector = 0uy then mask = ones else mask = zero);
  lognot_lemma mask;
  assert (if selector = 0uy then ~.mask = zero else ~.mask = ones);
  let out:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  [@ inline_let]
  let inv = fun (acc:t_Array u8 (sz 32)) (i:usize) ->
    v i <= 32 /\
   (forall j. j < v i ==> (if (selector =. 0uy) then Seq.index acc j == Seq.index lhs j else Seq.index acc j == Seq.index rhs j)) /\
   (forall j. j >= v i ==> Seq.index acc j == 0uy)
  in
  let out:t_Array u8 (sz 32) =
    Rust_primitives.Iterators.foldi_range #_ #(t_Array u8 (sz 32))  #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_SHARED_SECRET_SIZE
            }
      out
      (fun out i ->
          let out:t_Array u8 (sz 32) = out in
          assert ((out.[ i ] <: u8) = 0uy);
          let outi = 
            ((out.[ i ] <: u8) |.
              (((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)
                <:
                u8)
              <:
              u8) in
          if (selector = 0uy) then (
            logand_lemma (lhs.[ i ] <: u8) mask;
            assert (((lhs.[ i ] <: u8) &. mask <: u8) == (lhs.[ i ] <: u8));
            logand_lemma (rhs.[ i ] <: u8) (~.mask);
            assert (((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) == zero);
            logor_lemma ((lhs.[ i ] <: u8) &. mask <: u8) ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8);
            assert ((((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) <: u8) == (lhs.[ i ] <: u8));
            logor_lemma (out.[ i ] <: u8) (lhs.[ i ] <: u8);
            assert (((out.[ i ] <: u8) |. (((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) <: u8) <: u8) == (lhs.[ i ] <: u8));
            assert (outi = (lhs.[ i ] <: u8))
          )
          else (
            logand_lemma (lhs.[ i ] <: u8) mask;
            assert (((lhs.[ i ] <: u8) &. mask <: u8) == zero);
            logand_lemma (rhs.[ i ] <: u8) (~.mask);
            assert (((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) == (rhs.[ i ] <: u8));
            logor_lemma (rhs.[ i ] <: u8) zero;
            assert ((logor zero (rhs.[ i ] <: u8)) == (rhs.[ i ] <: u8));
            assert ((((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8)) == (rhs.[ i ] <: u8));
            logor_lemma (out.[ i ] <: u8) (rhs.[ i ] <: u8);
            assert (((out.[ i ] <: u8) |. (((lhs.[ i ] <: u8) &. mask <: u8) |. ((rhs.[ i ] <: u8) &. (~.mask <: u8) <: u8) <: u8) <: u8) == (rhs.[ i ] <: u8));
            assert (outi = (rhs.[ i ] <: u8))
          );
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            outi
          <:
          t_Array u8 (sz 32))
  in
  if (selector =. 0uy) then (
    eq_intro out lhs;
    out
  )
  else (
    eq_intro out rhs;
    out
  )
#pop-options
