module Libcrux_ml_dsa.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let impl__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_2__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_4__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl_4__as_slice (v_SIZE: usize) (self: t_MLDSASignature v_SIZE) = self._0 <: t_Slice u8

let impl__as_slice (v_SIZE: usize) (self: t_MLDSASigningKey v_SIZE) = self._0 <: t_Slice u8

let impl_2__as_slice (v_SIZE: usize) (self: t_MLDSAVerificationKey v_SIZE) = self._0 <: t_Slice u8
