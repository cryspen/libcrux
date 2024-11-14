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
          (value == 0uy ==> result == 0uy) /\ (value =!= 0uy ==> result == 1uy))

val is_non_zero (value: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          (value == 0uy ==> result == 0uy) /\ (value =!= 0uy ==> result == 1uy))

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
val compare (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      (requires (Core.Slice.impl__len #u8 lhs <: usize) =. (Core.Slice.impl__len #u8 rhs <: usize))
      (ensures
        fun result ->
          let result:u8 = result in
          (lhs == rhs ==> result == 0uy) /\ (lhs =!= rhs ==> result == 1uy))

val compare_ciphertexts_in_constant_time (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      (requires (Core.Slice.impl__len #u8 lhs <: usize) =. (Core.Slice.impl__len #u8 rhs <: usize))
      (ensures
        fun result ->
          let result:u8 = result in
          (lhs == rhs ==> result == 0uy) /\ (lhs =!= rhs ==> result == 1uy))

/// If `selector` is not zero, return the bytes in `rhs`; return the bytes in
/// `lhs` otherwise.
val select_ct (lhs rhs: t_Slice u8) (selector: u8)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires
        (Core.Slice.impl__len #u8 lhs <: usize) =. (Core.Slice.impl__len #u8 rhs <: usize) &&
        (Core.Slice.impl__len #u8 lhs <: usize) =. Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          (selector == 0uy ==> result == lhs) /\ (selector =!= 0uy ==> result == rhs))

val select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires
        (Core.Slice.impl__len #u8 lhs <: usize) =. (Core.Slice.impl__len #u8 rhs <: usize) &&
        (Core.Slice.impl__len #u8 lhs <: usize) =. Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          (selector == 0uy ==> result == lhs) /\ (selector =!= 0uy ==> result == rhs))

val compare_ciphertexts_select_shared_secret_in_constant_time (lhs_c rhs_c lhs_s rhs_s: t_Slice u8)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires
        (Core.Slice.impl__len #u8 lhs_c <: usize) =. (Core.Slice.impl__len #u8 rhs_c <: usize) &&
        (Core.Slice.impl__len #u8 lhs_s <: usize) =. (Core.Slice.impl__len #u8 rhs_s <: usize) &&
        (Core.Slice.impl__len #u8 lhs_s <: usize) =. Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          let selector = if lhs_c =. rhs_c then 0uy else 1uy in
          ((selector == 0uy ==> result == lhs_s) /\ (selector =!= 0uy ==> result == rhs_s)))
