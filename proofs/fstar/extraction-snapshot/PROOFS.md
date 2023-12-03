PREREQUISITES
==============
Verifying this branch requires the core-improvements branch of hax.


Files
=====

Verified
--------
Libcrux.Kem.fst: nothing to prove
Libcrux.Kem.Kyber.Constants.fst: nothing to prove
Libcrux.Digest.fsti
Libcrux.Kem.Kyber.Hash_functions.fst

Libcrux.Kem.Kyber.Kyber768.fst: enforces some preconditions
Libcrux.Kem.Kyber.Kyber1024.fst: enforces some preconditions
Libcrux.Kem.Kyber.Kyber512.fst: enforces some preconditions


Panic Free
--------

Libcrux.Kem.Kyber.fst added one precondition
Libcrux.Kem.Kyber.Types.fst: added four precondition

Libcrux.Kem.Kyber.Ind_cpa.fst: needs loop invariants and assumes
Libcrux.Kem.Kyber.Arithmetic.fst: needs loop invariants and assumes
Libcrux.Kem.Kyber.Compress.fst
Libcrux.Kem.Kyber.Constant_time_ops.fst

Libcrux.Kem.Kyber.Conversions.fst: needs a datatype invariant
Libcrux.Kem.Kyber.Matrix.fst: needs montgomery and barrett preconditions
Libcrux.Kem.Kyber.Sampling.fst:: needs some assumes


Unverified
----------
Libcrux.Kem.Kyber.Ntt.fst
Libcrux.Kem.Kyber.Serialize.fst


DESIRABLE FEATURES
=================

- NEEDED: nice way of propagating loop invariants

- NEEDED: deal with implies in Rust with continuation


- For each module, generate a .fst and a .fsti
  For now, just put the pub and pub(crate) bits in the .fsti
  
  
- Support const functions and their applications in types to avoid
  huge list of constant parameters
  
  

