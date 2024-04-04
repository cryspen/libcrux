# F\* Proofs for Libcrux Kyber

This directory holds F\* proofs for code compiled by hax from the
Libcrux Rust implementation of Kyber.

Each Rust module `m` in the implementation is translated to two files:
`M.fst` contains the functionalized F\* code compiled from Rust, and
`M.fsti` contains the F\* types for each function.

## Specifications

A partial high-level specification of Kyber is included in
Spec.Kyber.fst. This file is hand-written and includes the
specification of the IND-CCA KEM, the IND-CPA PKE, and the sampling
and serialization functions from the ML-KEM draft standard (FIPS 203).

The specification currently assumes, but does not define, the matrix
operations and the NTT polynomial definitions. We intend to fill out
the specification to be fully standalone in the future.

We extend the types and function declarations in each interface file
`M.fsti` to reflect the specification. For example, if a Rust function
`m::f` is intended to implement the specification function
`Spec.Kyber.f`, then we annotate the post-condition of `f` in `M.fsti`
to say that the input-output behavior of this function should match
`Spec.Kyber.f`. Then, when we typecheck `M.fst`, F\* will try to prove
this post-condition, and hence try to prove functional correctness for
the implementation of `m::f`.

## Panic Freedom

The first guarantee we need to prove for the Rust code is that it never panics.
In particular, we would like to prove that:

- arithmetic operations never over- or under-flow
- array and vector operations never go out of bounds
- `unwrap`s always succeed and `panic`s are always unreachable

To achieve this, we compile each primitive operation in Rust to the
equivalent operation in F\*, as specified in
`hax/proof-libs/fstar/rust_primitives`. For example, the Rust
addition operation `+` translates to the polymorphic, strict machine
integer operation `+!` in F\*, which requires, as a precondition, that
the addition of its inputs does not overflow the target type.

Similarly, each array access is compiled to an instance of the `Index`
or `IndexMut` typeclass in F\*, both of which require as preconditions
that the index is not out-of-bounds.

Consequently, when we typecheck the code in `M.fst` we need to prove
that all its arithmetic operations, array accesses, etc are
type-safe. This proof often requires the pre-conditions to be
propagated to the calling functions, leading to additional annotations
to the functions types in the `M.fsti` interface files.

Sometimes, it is more convenient to track integer bounds within the
types themselves, and for this we use refinement types like `i32_b
33328` to refer to 32-bit signed integers `x:i32` that obey `-3328 <=
x <= 3328`. Packaging these bounds within a refinement type allows us
to more easily propagate them in F\*, but also requires us to add
annotations to the F\* code in `M.fst` because these refinement types
do not exist in Rust.

The code in this directory has been verified for panic freedom
on all possible inputs. Currently, the proofs of panic freedom are
interleaved with the proofs of functional correctness, but we plan
to separate them out in the future.

## Implementation Correctness

In addition to panic freedom, we would like to prove functional
correctness for the Rust code with respect to the high-level
specification in `Spec.Kyber.fst`.

The main work here is to show that the low-level optimizations
implemented in the Rust code are correct. In particular, we use
montgomery and barrett reduction to speed up arithmetic, and we delay
these reductions as much as possible during NTT polynomial
multiplication, and in various matrix operations. We also implement
optimized serialization and deserialization functions for various bit
lengths, and we implement constant-time programming patterns for
compression and comparisons. None of these optimizations are in the
specification and hence must be verified.

As mentioned above, we annotate each function `M.f` in the code with
a post-condition linking the input-output behavior of `M.f` with
the corresponding function in `Spec.Kyber.fst`. If we can verify
the entire function, except for this correctness post-condition,
we say that the function is panic-free but not (yet) verified for correctness.
If the function is fully verified without any `admit` or `assume`, we
say that it is verified.

As of January 15, 2023, the following modules are fully verified:

- Libcrux.Kem.Kyber.Constants.fst
- Libcrux.Kem.Kyber.Types.fst
- Libcrux.Kem.Kyber.Arithmetic.fsti
- Libcrux.Kem.Kyber.fst
- Libcrux.Kem.Kyber.Compress.fst
- Libcrux.Kem.Kyber.Serialize.PartA.fst
- Libcrux.Kem.Kyber.Constant_time_ops.fst
- Libcrux.Kem.Kyber.Kyber512.fst
- Libcrux.Kem.Kyber.Kyber768.fst
- Libcrux.Kem.Kyber.Kyber1024.fst

The following modules are panic free but only partially verified:

- Libcrux.Kem.Kyber.Ntt.fst: Functional correctness remaining
- Libcrux.Kem.Kyber.Matrix.fst: Functional correctness remaining
- Libcrux.Kem.Kyber.Sampling.fst: Functional correctness remaining
- Libcrux.Kem.Kyber.Serialize.PartB.fst: High-level serialization functions remaining
- Libcrux.Kem.Kyber.Ind_cpa.fst: IND-CPA verified, some serialization functions remaining

The proofs for the above modules are ongoing.

## Secret Independence

We prove secret independence for the Rust code by typechecking the generated F\* code
against a library of _secret integers_ in hax. The proofs of secret independence are in
a separate directory `../extraction-secret-independent`, since they require very few
annotations and rely on different assumptions on the `rust_primitives` library.

We note that our secret independence analysis was able to find a new timing bug
in our Rust code, which we then subsequently discovered in other Kyber implementations,
including the PQ-Crystals reference code. In response to our findings, the code in PQ Crystals,
PQ Clean, liboqs, and many other implementations have now been patched.

This timing bug was later independently discovered by Dan Bernstein, who calls it [KyberSlash](https://kyberslash.cr.yp.to/)
