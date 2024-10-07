module Libcrux_platform.X86
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Feature =
  | Feature_mmx : t_Feature
  | Feature_sse : t_Feature
  | Feature_sse2 : t_Feature
  | Feature_sse3 : t_Feature
  | Feature_pclmulqdq : t_Feature
  | Feature_ssse3 : t_Feature
  | Feature_fma : t_Feature
  | Feature_movbe : t_Feature
  | Feature_sse4_1_ : t_Feature
  | Feature_sse4_2_ : t_Feature
  | Feature_popcnt : t_Feature
  | Feature_aes : t_Feature
  | Feature_xsave : t_Feature
  | Feature_osxsave : t_Feature
  | Feature_avx : t_Feature
  | Feature_rdrand : t_Feature
  | Feature_sgx : t_Feature
  | Feature_bmi1 : t_Feature
  | Feature_avx2 : t_Feature
  | Feature_bmi2 : t_Feature
  | Feature_avx512f : t_Feature
  | Feature_avx512dq : t_Feature
  | Feature_rdseed : t_Feature
  | Feature_adx : t_Feature
  | Feature_avx512ifma : t_Feature
  | Feature_avx512pf : t_Feature
  | Feature_avx512er : t_Feature
  | Feature_avx512cd : t_Feature
  | Feature_sha : t_Feature
  | Feature_avx512bw : t_Feature
  | Feature_avx512vl : t_Feature

val t_Feature_cast_to_repr (x: t_Feature) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

/// Initialize CPU detection.
val init: Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

/// Check hardware [`Feature`] support.
val supported (feature: t_Feature) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)
