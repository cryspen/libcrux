module Spec.Utils

open FStar.Tactics
open FStar.Mul
open Core

(*** Generic utilities *)
let rec forall_n (n:pos) (p:(x:nat{x < n} -> Type0)): r: Type0 {r <==> forall (x:nat{x < n}). p x}
  = if n = 1 then p 0
             else forall_n (n - 1) p /\ p (n - 1)

/// The arrays [a] and [b] are identical but at index [i]
let modifies1_n #t n
    (a b: t_Array t (sz n))
    (i:usize{v i < n}) = 
    forall_n n (fun j -> (v i <> j) ==> Seq.index a j == Seq.index b j)

/// The arrays [a] and [b] are identical but at indexes [i1] and [i2]
let modifies2_n #t n
    (a b: t_Array t (sz n))
    (i1 i2:(i:usize{v i < n})) = 
    forall_n n (fun i -> ((v i1 <> i) /\ (v i2 <> i)) ==> Seq.index a i == Seq.index b i)

/// The arrays [a] and [b] are identical but at indexes in the range `[i; j]`
let modifies_range_n #t n
        (a b: t_Array t (mk_usize n))
        (i:usize{v i < n}) (j:usize{v j <= n /\ v i <= v j}) =
   forall_n n (fun k -> ((v i > k \/ k >= v j)   ==> Seq.index a k == Seq.index b k))

/// Tactic that unrolls fully any function present in this module
private let unroll (): Tac unit
  = norm [primops; iota; delta_namespace [implode_qn(cur_module ())]; zeta_full];
    trefl ()

(*** Specialized and normalized utilities *)
[@@postprocess_with unroll] let forall2  = forall_n 4
[@@postprocess_with unroll] let forall4  = forall_n 4
[@@postprocess_with unroll] let forall8  = forall_n 8
[@@postprocess_with unroll] let forall16 = forall_n 16
[@@postprocess_with unroll] let forall32 = forall_n 32
[@@postprocess_with unroll] let forall64 = forall_n 64
[@@postprocess_with unroll] let forall128 = forall_n 128
[@@postprocess_with unroll] let forall256 = forall_n 256

[@@postprocess_with unroll] let modifies1_8  = modifies1_n 8
[@@postprocess_with unroll] let modifies1_16 = modifies1_n 16
[@@postprocess_with unroll] let modifies1_32 = modifies1_n 32
[@@postprocess_with unroll] let modifies1_64 = modifies1_n 64
[@@postprocess_with unroll] let modifies1_128 = modifies1_n 128
[@@postprocess_with unroll] let modifies1_256 = modifies1_n 256

[@@postprocess_with unroll] let modifies2_8  = modifies2_n 8
[@@postprocess_with unroll] let modifies2_16 = modifies2_n 16
[@@postprocess_with unroll] let modifies2_32 = modifies2_n 32
[@@postprocess_with unroll] let modifies2_64 = modifies2_n 64
[@@postprocess_with unroll] let modifies2_128 = modifies2_n 128
[@@postprocess_with unroll] let modifies2_256 = modifies2_n 256

[@@postprocess_with unroll] let modifies_range_8  = modifies_range_n 8
[@@postprocess_with unroll] let modifies_range_16 = modifies_range_n 16
[@@postprocess_with unroll] let modifies_range_32 = modifies_range_n 32
[@@postprocess_with unroll] let modifies_range_64 = modifies_range_n 64
[@@postprocess_with unroll] let modifies_range_128 = modifies_range_n 128
[@@postprocess_with unroll] let modifies_range_256 = modifies_range_n 256
