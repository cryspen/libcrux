module Libcrux_secrets.Int.Public_integers
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let secret (#v_T: Type0) (x: v_T) : v_T = x

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : Libcrux_secrets.Traits.t_Classify v_T =
  {
    f_Classified = v_T;
    f_classify_pre = (fun (self: v_T) -> true);
    f_classify_post = (fun (self: v_T) (out: v_T) -> true);
    f_classify = fun (self: v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : Libcrux_secrets.Traits.t_Declassify v_T =
  {
    f_Declassified = v_T;
    f_declassify_pre = (fun (self: v_T) -> true);
    f_declassify_post = (fun (self: v_T) (out: v_T) -> true);
    f_declassify = fun (self: v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : Libcrux_secrets.Traits.t_ClassifyRef v_T =
  {
    f_ClassifiedRef = v_T;
    f_classify_ref_pre = (fun (self: v_T) -> true);
    f_classify_ref_post = (fun (self: v_T) (out: v_T) -> true);
    f_classify_ref = fun (self: v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) : Libcrux_secrets.Traits.t_DeclassifyRef v_T =
  {
    f_DeclassifiedRef = v_T;
    f_declassify_ref_pre = (fun (self: v_T) -> true);
    f_declassify_ref_post = (fun (self: v_T) (out: v_T) -> true);
    f_declassify_ref = fun (self: v_T) -> self
  }

let classify_mut_slice (#v_T: Type0) (x: v_T) : v_T = x
