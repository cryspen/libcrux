module Libcrux_secrets.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Marker trait to constrain the types for which we use SecretScalar
class t_Scalar (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13011033735201511749:Core.Marker.t_Copy v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Scalar u8 = { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_u16: t_Scalar u16 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_u32: t_Scalar u32 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_u64: t_Scalar u64 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_u128: t_Scalar u128 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_i8: t_Scalar i8 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_i16: t_Scalar i16 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_i32: t_Scalar i32 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_i64: t_Scalar i64 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Scalar_for_i128: t_Scalar i128 =
  { _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve }

class t_IntOps (v_Self: Type0) = {
  f_wrapping_add_pre:#v_T: Type0 -> {| i1: Core.Convert.t_Into v_T v_Self |} -> v_Self -> v_T
    -> Type0;
  f_wrapping_add_post:
      #v_T: Type0 ->
      {| i1: Core.Convert.t_Into v_T v_Self |} ->
      v_Self ->
      v_T ->
      v_Self
    -> Type0;
  f_wrapping_add:#v_T: Type0 -> {| i1: Core.Convert.t_Into v_T v_Self |} -> x0: v_Self -> x1: v_T
    -> Prims.Pure v_Self
        (f_wrapping_add_pre #v_T #i1 x0 x1)
        (fun result -> f_wrapping_add_post #v_T #i1 x0 x1 result);
  f_wrapping_sub_pre:#v_T: Type0 -> {| i1: Core.Convert.t_Into v_T v_Self |} -> v_Self -> v_T
    -> Type0;
  f_wrapping_sub_post:
      #v_T: Type0 ->
      {| i1: Core.Convert.t_Into v_T v_Self |} ->
      v_Self ->
      v_T ->
      v_Self
    -> Type0;
  f_wrapping_sub:#v_T: Type0 -> {| i1: Core.Convert.t_Into v_T v_Self |} -> x0: v_Self -> x1: v_T
    -> Prims.Pure v_Self
        (f_wrapping_sub_pre #v_T #i1 x0 x1)
        (fun result -> f_wrapping_sub_post #v_T #i1 x0 x1 result);
  f_wrapping_mul_pre:#v_T: Type0 -> {| i1: Core.Convert.t_Into v_T v_Self |} -> v_Self -> v_T
    -> Type0;
  f_wrapping_mul_post:
      #v_T: Type0 ->
      {| i1: Core.Convert.t_Into v_T v_Self |} ->
      v_Self ->
      v_T ->
      v_Self
    -> Type0;
  f_wrapping_mul:#v_T: Type0 -> {| i1: Core.Convert.t_Into v_T v_Self |} -> x0: v_Self -> x1: v_T
    -> Prims.Pure v_Self
        (f_wrapping_mul_pre #v_T #i1 x0 x1)
        (fun result -> f_wrapping_mul_post #v_T #i1 x0 x1 result);
  f_rotate_left_pre:v_Self -> u32 -> Type0;
  f_rotate_left_post:v_Self -> u32 -> v_Self -> Type0;
  f_rotate_left:x0: v_Self -> x1: u32
    -> Prims.Pure v_Self (f_rotate_left_pre x0 x1) (fun result -> f_rotate_left_post x0 x1 result);
  f_rotate_right_pre:v_Self -> u32 -> Type0;
  f_rotate_right_post:v_Self -> u32 -> v_Self -> Type0;
  f_rotate_right:x0: v_Self -> x1: u32
    -> Prims.Pure v_Self (f_rotate_right_pre x0 x1) (fun result -> f_rotate_right_post x0 x1 result)
}

/// Encode secret arrays into secret integers.
class t_EncodeOps (v_Self: Type0) (v_T: Type0) (v_N: usize) = {
  f_to_le_bytes_pre:v_Self -> Type0;
  f_to_le_bytes_post:v_Self -> t_Array v_T v_N -> Type0;
  f_to_le_bytes:x0: v_Self
    -> Prims.Pure (t_Array v_T v_N)
        (f_to_le_bytes_pre x0)
        (fun result -> f_to_le_bytes_post x0 result);
  f_to_be_bytes_pre:v_Self -> Type0;
  f_to_be_bytes_post:v_Self -> t_Array v_T v_N -> Type0;
  f_to_be_bytes:x0: v_Self
    -> Prims.Pure (t_Array v_T v_N)
        (f_to_be_bytes_pre x0)
        (fun result -> f_to_be_bytes_post x0 result);
  f_from_le_bytes_pre:t_Array v_T v_N -> Type0;
  f_from_le_bytes_post:t_Array v_T v_N -> v_Self -> Type0;
  f_from_le_bytes:x0: t_Array v_T v_N
    -> Prims.Pure v_Self (f_from_le_bytes_pre x0) (fun result -> f_from_le_bytes_post x0 result);
  f_from_be_bytes_pre:t_Array v_T v_N -> Type0;
  f_from_be_bytes_post:t_Array v_T v_N -> v_Self -> Type0;
  f_from_be_bytes:x0: t_Array v_T v_N
    -> Prims.Pure v_Self (f_from_be_bytes_pre x0) (fun result -> f_from_be_bytes_post x0 result)
}

class t_Classify (v_Self: Type0) = {
  f_Classified:Type0;
  f_classify_pre:v_Self -> Type0;
  f_classify_post:v_Self -> f_Classified -> Type0;
  f_classify:x0: v_Self
    -> Prims.Pure f_Classified (f_classify_pre x0) (fun result -> f_classify_post x0 result)
}

class t_ClassifyRef (v_Self: Type0) = {
  f_ClassifiedRef:Type0;
  f_classify_ref_pre:v_Self -> Type0;
  f_classify_ref_post:v_Self -> f_ClassifiedRef -> Type0;
  f_classify_ref:x0: v_Self
    -> Prims.Pure f_ClassifiedRef
        (f_classify_ref_pre x0)
        (fun result -> f_classify_ref_post x0 result)
}

class t_Declassify (v_Self: Type0) = {
  f_Declassified:Type0;
  f_declassify_pre:v_Self -> Type0;
  f_declassify_post:v_Self -> f_Declassified -> Type0;
  f_declassify:x0: v_Self
    -> Prims.Pure f_Declassified (f_declassify_pre x0) (fun result -> f_declassify_post x0 result)
}

class t_DeclassifyRef (v_Self: Type0) = {
  f_DeclassifiedRef:Type0;
  f_declassify_ref_pre:v_Self -> Type0;
  f_declassify_ref_post:v_Self -> f_DeclassifiedRef -> Type0;
  f_declassify_ref:x0: v_Self
    -> Prims.Pure f_DeclassifiedRef
        (f_declassify_ref_pre x0)
        (fun result -> f_declassify_ref_post x0 result)
}

class t_ClassifyRefMut (v_Self: Type0) = {
  f_ClassifiedRefMut:Type0;
  f_classify_ref_mut_pre:v_Self -> Type0;
  f_classify_ref_mut_post:v_Self -> f_ClassifiedRefMut -> Type0;
  f_classify_ref_mut:x0: v_Self
    -> Prims.Pure f_ClassifiedRefMut
        (f_classify_ref_mut_pre x0)
        (fun result -> f_classify_ref_mut_post x0 result)
}

class t_DeclassifyRefMut (v_Self: Type0) = {
  f_DeclassifiedRefMut:Type0;
  f_declassify_ref_mut_pre:v_Self -> Type0;
  f_declassify_ref_mut_post:v_Self -> f_DeclassifiedRefMut -> Type0;
  f_declassify_ref_mut:x0: v_Self
    -> Prims.Pure f_DeclassifiedRefMut
        (f_declassify_ref_mut_pre x0)
        (fun result -> f_declassify_ref_mut_post x0 result)
}
