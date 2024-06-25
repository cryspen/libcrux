module Libcrux_sha3.Simd.Arm64
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_uint64x2_t = Core.Core_arch.Arm_shared.Neon.t_uint64x2_t

val v__vbcaxq_u64 (a b c: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint64x2_t Prims.l_True (fun _ -> Prims.l_True)

val v__veor5q_u64 (a b c d e: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint64x2_t Prims.l_True (fun _ -> Prims.l_True)

val v__veorq_n_u64 (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (c: u64)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint64x2_t Prims.l_True (fun _ -> Prims.l_True)

val slice_2_ (a: t_Array (t_Slice u8) (sz 2)) (start len: usize)
    : Prims.Pure (t_Array (t_Slice u8) (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

val rotate_left (v_LEFT v_RIGHT: i32) (x: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint64x2_t Prims.l_True (fun _ -> Prims.l_True)

val v__vrax1q_u64 (a b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint64x2_t Prims.l_True (fun _ -> Prims.l_True)

val v__vxarq_u64 (v_LEFT v_RIGHT: i32) (a b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint64x2_t Prims.l_True (fun _ -> Prims.l_True)

val load_block
      (v_RATE: usize)
      (s: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
      (blocks: t_Array (t_Slice u8) (sz 2))
    : Prims.Pure (t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
      Prims.l_True
      (fun _ -> Prims.l_True)

val load_block_full
      (v_RATE: usize)
      (s: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
      (blocks: t_Array (t_Array u8 (sz 200)) (sz 2))
    : Prims.Pure (t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
      Prims.l_True
      (fun _ -> Prims.l_True)

val store_block
      (v_RATE v_SIZE: usize)
      (s: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
      (out: t_Array (t_Array u8 v_SIZE) (sz 2))
      (start: usize)
    : Prims.Pure (t_Array (t_Array u8 v_SIZE) (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

val store_block_full
      (v_RATE: usize)
      (s: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
    : Prims.Pure (t_Array (t_Array u8 (sz 200)) (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_sha3.Traits.Internal.t_KeccakItem Core.Core_arch.Arm_shared.Neon.t_uint64x2_t
  (sz 2) =
  {
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    f_zero_pre = (fun (_: Prims.unit) -> true);
    f_zero_post = (fun (_: Prims.unit) (out: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) -> true);
    f_zero = (fun (_: Prims.unit) -> Libcrux_intrinsics.Arm64.v__vdupq_n_u64 0uL);
    f_xor5_pre
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (c: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (d: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (e: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_xor5_post
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (c: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (d: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (e: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (out: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_xor5
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (c: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (d: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (e: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        v__veor5q_u64 a b c d e);
    f_rotate_left1_and_xor_pre
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_rotate_left1_and_xor_post
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (out: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_rotate_left1_and_xor
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        v__vrax1q_u64 a b);
    f_xor_and_rotate_pre
    =
    (fun
        (v_LEFT: i32)
        (v_RIGHT: i32)
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_xor_and_rotate_post
    =
    (fun
        (v_LEFT: i32)
        (v_RIGHT: i32)
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (out: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_xor_and_rotate
    =
    (fun
        (v_LEFT: i32)
        (v_RIGHT: i32)
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        v__vxarq_u64 v_LEFT v_RIGHT a b);
    f_and_not_xor_pre
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (c: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_and_not_xor_post
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (c: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (out: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_and_not_xor
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (c: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        v__vbcaxq_u64 a b c);
    f_xor_constant_pre = (fun (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (c: u64) -> true);
    f_xor_constant_post
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (c: u64)
        (out: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_xor_constant
    =
    (fun (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (c: u64) -> v__veorq_n_u64 a c);
    f_xor_pre
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_xor_post
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (out: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        true);
    f_xor
    =
    (fun
        (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        (b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
        ->
        Libcrux_intrinsics.Arm64.v__veorq_u64 a b);
    f_load_block_pre
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Slice u8) (sz 2))
        ->
        true);
    f_load_block_post
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Slice u8) (sz 2))
        (out: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        ->
        true);
    f_load_block
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Slice u8) (sz 2))
        ->
        let hax_temp_output, a:(Prims.unit &
          t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5)) =
          (), load_block v_BLOCKSIZE a b
          <:
          (Prims.unit & t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        in
        a);
    f_store_block_pre
    =
    (fun
        (v_BLOCKSIZE: usize)
        (v_SIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 v_SIZE) (sz 2))
        (start: usize)
        ->
        true);
    f_store_block_post
    =
    (fun
        (v_BLOCKSIZE: usize)
        (v_SIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 v_SIZE) (sz 2))
        (start: usize)
        (out: t_Array (t_Array u8 v_SIZE) (sz 2))
        ->
        true);
    f_store_block
    =
    (fun
        (v_BLOCKSIZE: usize)
        (v_SIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 v_SIZE) (sz 2))
        (start: usize)
        ->
        let hax_temp_output, b:(Prims.unit & t_Array (t_Array u8 v_SIZE) (sz 2)) =
          (), store_block v_BLOCKSIZE v_SIZE a b start
          <:
          (Prims.unit & t_Array (t_Array u8 v_SIZE) (sz 2))
        in
        b);
    f_load_block_full_pre
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 (sz 200)) (sz 2))
        ->
        true);
    f_load_block_full_post
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 (sz 200)) (sz 2))
        (out: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        ->
        true);
    f_load_block_full
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 (sz 200)) (sz 2))
        ->
        let hax_temp_output, a:(Prims.unit &
          t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5)) =
          (), load_block_full v_BLOCKSIZE a b
          <:
          (Prims.unit & t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        in
        a);
    f_store_block_full_pre
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        ->
        true);
    f_store_block_full_post
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        (out: t_Array (t_Array u8 (sz 200)) (sz 2))
        ->
        true);
    f_store_block_full
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
        ->
        store_block_full v_BLOCKSIZE a);
    f_slice_n_pre = (fun (a: t_Array (t_Slice u8) (sz 2)) (start: usize) (len: usize) -> true);
    f_slice_n_post
    =
    (fun
        (a: t_Array (t_Slice u8) (sz 2))
        (start: usize)
        (len: usize)
        (out: t_Array (t_Slice u8) (sz 2))
        ->
        true);
    f_slice_n
    =
    fun (a: t_Array (t_Slice u8) (sz 2)) (start: usize) (len: usize) -> slice_2_ a start len
  }
