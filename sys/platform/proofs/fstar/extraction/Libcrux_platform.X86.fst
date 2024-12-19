module Libcrux_platform.X86
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let t_Feature_cast_to_repr (x: t_Feature) =
  match x with
  | Feature_mmx  -> isz 0
  | Feature_sse  -> isz 1
  | Feature_sse2  -> isz 3
  | Feature_sse3  -> isz 6
  | Feature_pclmulqdq  -> isz 10
  | Feature_ssse3  -> isz 15
  | Feature_fma  -> isz 21
  | Feature_movbe  -> isz 28
  | Feature_sse4_1_  -> isz 36
  | Feature_sse4_2_  -> isz 45
  | Feature_popcnt  -> isz 55
  | Feature_aes  -> isz 66
  | Feature_xsave  -> isz 78
  | Feature_osxsave  -> isz 91
  | Feature_avx  -> isz 105
  | Feature_rdrand  -> isz 120
  | Feature_sgx  -> isz 136
  | Feature_bmi1  -> isz 153
  | Feature_avx2  -> isz 171
  | Feature_bmi2  -> isz 190
  | Feature_avx512f  -> isz 210
  | Feature_avx512dq  -> isz 231
  | Feature_rdseed  -> isz 253
  | Feature_adx  -> isz 276
  | Feature_avx512ifma  -> isz 300
  | Feature_avx512pf  -> isz 325
  | Feature_avx512er  -> isz 351
  | Feature_avx512cd  -> isz 378
  | Feature_sha  -> isz 406
  | Feature_avx512bw  -> isz 435
  | Feature_avx512vl  -> isz 465

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_Feature

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_Feature

let impl_1 = impl_1'

assume
val init': Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

let init = init'

assume
val supported': feature: t_Feature -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let supported = supported'
