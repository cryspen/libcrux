module Libcrux_platform.X86
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let t_Feature_cast_to_repr (x: t_Feature) =
  match x <: t_Feature with
  | Feature_mmx  -> mk_isize 0
  | Feature_sse  -> mk_isize 1
  | Feature_sse2  -> mk_isize 2
  | Feature_sse3  -> mk_isize 3
  | Feature_pclmulqdq  -> mk_isize 4
  | Feature_ssse3  -> mk_isize 5
  | Feature_fma  -> mk_isize 6
  | Feature_movbe  -> mk_isize 7
  | Feature_sse4_1_  -> mk_isize 8
  | Feature_sse4_2_  -> mk_isize 9
  | Feature_popcnt  -> mk_isize 10
  | Feature_aes  -> mk_isize 11
  | Feature_xsave  -> mk_isize 12
  | Feature_osxsave  -> mk_isize 13
  | Feature_avx  -> mk_isize 14
  | Feature_rdrand  -> mk_isize 15
  | Feature_sgx  -> mk_isize 16
  | Feature_bmi1  -> mk_isize 17
  | Feature_avx2  -> mk_isize 18
  | Feature_bmi2  -> mk_isize 19
  | Feature_avx512f  -> mk_isize 20
  | Feature_avx512dq  -> mk_isize 21
  | Feature_rdseed  -> mk_isize 22
  | Feature_adx  -> mk_isize 23
  | Feature_avx512ifma  -> mk_isize 24
  | Feature_avx512pf  -> mk_isize 25
  | Feature_avx512er  -> mk_isize 26
  | Feature_avx512cd  -> mk_isize 27
  | Feature_sha  -> mk_isize 28
  | Feature_avx512bw  -> mk_isize 29
  | Feature_avx512vl  -> mk_isize 30

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_Feature

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_Feature

let impl_1 = impl_1'

assume
val supported': feature: t_Feature -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let supported = supported'

assume
val init': Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

let init = init'
