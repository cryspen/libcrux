module Libcrux_ml_kem.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// Return 1 if `value` is not zero and 0 otherwise.
val inz (value: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          if value =. mk_u8 0 then result =. mk_u8 0 else result =. mk_u8 1)

val is_non_zero (value: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          if value =. mk_u8 0 then result =. mk_u8 0 else result =. mk_u8 1)

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
val compare (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      (requires (Core.Slice.impl__len #u8 lhs <: usize) =. (Core.Slice.impl__len #u8 rhs <: usize))
      (ensures
        fun result ->
          let result:u8 = result in
          if lhs =. rhs then result =. mk_u8 0 else result =. mk_u8 1)

val compare_ciphertexts_in_constant_time (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      (requires (Core.Slice.impl__len #u8 lhs <: usize) =. (Core.Slice.impl__len #u8 rhs <: usize))
      (ensures
        fun result ->
          let result:u8 = result in
          if lhs =. rhs then result =. mk_u8 0 else result =. mk_u8 1)

/// If `selector` is not zero, return the bytes in `rhs`; return the bytes in
/// `lhs` otherwise.
val select_ct (lhs rhs: t_Slice u8) (selector: u8)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      (requires
        (Core.Slice.impl__len #u8 lhs <: usize) =. (Core.Slice.impl__len #u8 rhs <: usize) &&
        (Core.Slice.impl__len #u8 lhs <: usize) =. Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun result ->
          let result:t_Array u8 (mk_usize 32) = result in
          if selector =. mk_u8 0 then result =. lhs else result =. rhs)

val select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      (requires
        (Core.Slice.impl__len #u8 lhs <: usize) =. (Core.Slice.impl__len #u8 rhs <: usize) &&
        (Core.Slice.impl__len #u8 lhs <: usize) =. Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun result ->
          let result:t_Array u8 (mk_usize 32) = result in
          if selector =. mk_u8 0 then result =. lhs else result =. rhs)

val compare_ciphertexts_select_shared_secret_in_constant_time (lhs_c rhs_c lhs_s rhs_s: t_Slice u8)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      (requires
        (Core.Slice.impl__len #u8 lhs_c <: usize) =. (Core.Slice.impl__len #u8 rhs_c <: usize) &&
        (Core.Slice.impl__len #u8 lhs_s <: usize) =. (Core.Slice.impl__len #u8 rhs_s <: usize) &&
        (Core.Slice.impl__len #u8 lhs_s <: usize) =. Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun result ->
          let result:t_Array u8 (mk_usize 32) = result in
          if lhs_c =. rhs_c then result =. lhs_s else result =. rhs_s)
