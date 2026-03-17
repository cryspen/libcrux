# libcrux - a high-assurance cryptographic library in Rust

libcrux is a cryptographic library written in Rust. It uses formally verified
code generated from the [HACL* project](https://github.com/hacl-star/hacl-star) and includes Rust code that is
directly verified for runtime safety and functional correctness using the
[hax toolchain](https://github.com/cryspen/hax). For more details, see below.

libcrux is in pre-release (all of its crates are versioned < `0.1`). If you wish to use any of these crates
in production, get in touch with the [maintainers](mailto:info@cryspen.com) and we can advise you on whether
libcrux is a good fit for your use-case.

## Which crate to use?

Libcrux is organized in different sub-crates which implement cryptographic algorithms, primitives and protocols.

TODO: Add guide on which crate implements what.

This repository also contains an unpublished `libcrux` crate, which is a simple re-exporter of the functionality offered by the individual sub-crates and is useful for us to ensure sub-crate versions remain compatible with each other. We recommend you use the individual sub-crates that provide the functionality you need instead of the main `libcrux` crate.

## Minimum Supported Rust Version (MSRV)

The default feature set has a MSRV of `1.78.0`. `no_std` environments
are supported starting from Rust version `1.81.0`.

## `no_std` support
`libcrux` and the individual primitive crates it depends on support
`no_std` environments given a global allocator for the target
platform.

## Verification status

As a quick indicator of overall verification status, subcrates in this workspace include the following badges:

- ![pre-verification] to indicate that most (or all) of the code that
  is contained in default features of that crate is not (yet)
  verified.
- ![verified-hacl] to indicate that algorithms in a crate have been verified and extracted to Rust as part of the HACL* project. The source F* code in HACL* is verified for memory safety, functional correctness against a high-level spec, and secret independence (for details, see [these](https://eprint.iacr.org/2017/536) [papers](https://arxiv.org/abs/1703.00053).) Top-level Rust APIs in these crates accessing the code from HACL* may not be verified.

- ![verified] to indicate that most (or all) of the Rust code that is contained in the default feature set is verified using the [hax toolchain](https://github.com/cryspen/hax). Where indicated, the code is verified to be panic free and functionally correct against a mathematical spec (for an overview of hax, see [this paper](https://eprint.iacr.org/2025/142))

Importantly, executables compiled from the code in this repository are *not* verified to be side-channel resistant, although we try to enforce that the source code is secret-independent (also sometimes called “constant-time”).

In every case, please refer to the more detailed notes on verification in each sub-crate to learn more about what has (or has not) been verified in the particular case, and [reach out to us](mailto:info@cryspen.com) if you have any questions.

## Publications

Libcrux was introduced in this article at RWC 2023. The verification methodology used to build libcrux is described in [this paper](https://eprint.iacr.org/2025/142).

[architecture]: ./Architecture.md
[hacspec]: https://hacspec.org
[formal verification]: ./formal_verification

[verified-hacl]: ./.assets/verified-hacl-rs-brightgreen.svg
[verified]: ./.assets/verified-brightgreen.svg
[pre-verification]: ./.assets/pre_verification-orange.svg
