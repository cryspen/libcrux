module Libcrux_ml_kem.Vector.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
unfold
let t_FieldElement = i16

type t_PortableVector = { f_elements:t_Array i16 (sz 16) }

val from_i16_array (array: t_Slice i16)
    : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val zero: Prims.unit -> Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)
