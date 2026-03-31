# ML-KEM Verification Status

This file keeps track of the current verification status of the modules in the ML-KEM implementation.

Lax Checking means that the module translates to typed code in F* which passes the F* lax checker.
Runtime Safety means that the module has been proved to be free of panics, that it obeys all the preconditions
set by the Rust standard library (e.g. arrays are accessed in bounds, arithmetic operations do not overflow, etc)
as well as the pre-conditions set by all the modules this module depends on (e.g. range preconditions on inputs).
Correctness means that the module has been formally verified for correctness against a high-level mathematical
specifiction of its input-output behavior.

We write "yes" when the module is fully proven to satisfy one of these conditions, and "needs proofs" when some
functions in the modules still need some proofs in that category.


| Category | File              | Lax Checking | Runtime Safety | Correctness  |
| -------- | ----------------- | ------------ | -------------- | ------------ |
| _Generic_  | constant_time_ops | yes          | yes            | yes          |    
|          | hash_functions    | yes          | yes            | yes          |    
|          | ind_cpa           | yes          | yes            | yes          |    
|          | ind_cca           | yes          | yes            | yes          |    
|          | instantiations    | yes          | yes            | yes          |    
|          | multiplexing      | yes          | yes            | yes          |    
|          | polynomial        | yes          | yes            | yes          |    
|          | invert_ntt        | yes          | yes            | yes          |    
|          | ntt               | yes          | yes            | yes          |    
|          | matrix            | yes          | yes	       | yes	      |    
|          | serialize         | yes          | needs proofs   | needs proofs |    
|          | sampling          | yes          | needs proofs   | needs proofs |    
|          | mlkem*            | yes          | yes            | needs proofs |    
| 	   |                   |              |                |              |
| _Portable_ | arithmetic        | yes          | yes            | yes          |
|          | ntt               | yes          | yes            | yes          |
|          | serialize         | yes          | yes            | yes          |
|          | compress          | yes          | yes            | yes          |
|          | sampling          | yes          | yes            | needs proofs |
|          |                   |              |                |              |
| _Avx2_     | arithmetic        | yes        | yes            | yes          |
|          | ntt               | yes          | yes            | yes          |
|          | serialize         | yes          | yes            | yes          |
|          | compress          | yes          | yes            | yes	      |
|          | sampling          | yes          | yes            | needs proofs |
|          |                   |              |                |              |
| _Neon_     | arithmetic        | yes        | needs proofs   | needs proofs |
|          | ntt               | yes          | needs proofs   | needs proofs |
|          | compress          | yes          | needs proofs   | needs proofs |
|          | serialize         | yes          | needs proofs   | needs proofs |
|          | sampling          | yes          | needs proofs   | needs proofs |

