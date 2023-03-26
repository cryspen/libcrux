# HPKE 🤝 hacspec

> 💡 This is a hacspec representation of the [HPKE RFC].
> The text is mostly verbatim from the RFC with changes where required.
> It demonstrates the possibilities of hacspec for specifications.

This document describes a scheme for hybrid public-key encryption (HPKE).
This scheme provides a variant of public-key encryption of arbitrary-sized
plaintexts for a recipient public key. It also includes three authenticated
variants, including one which authenticates possession of a pre-shared key,
and two optional ones which authenticate possession of a KEM private key.
HPKE works for any combination of an asymmetric key encapsulation mechanism
(KEM), key derivation function (KDF), and authenticated encryption with
additional data (AEAD) encryption function. Some authenticated variants may not
be supported by all KEMs. We provide instantiations of the scheme using widely
used and efficient primitives, such as Elliptic Curve Diffie-Hellman key
agreement, HKDF, and SHA2.

The original document is a product of the Crypto Forum Research Group (CFRG) in the IRTF.

# Introduction

Encryption schemes that combine asymmetric and symmetric algorithms have been
specified and practiced since the early days of public-key cryptography, e.g.,
[RFC1421]. Combining the two yields the key management advantages of asymmetric
cryptography and the performance benefits of symmetric cryptography. The traditional
combination has been "encrypt the symmetric key with the public key." "Hybrid"
public-key encryption schemes (HPKE), specified here, take a different approach:
"generate the symmetric key and its encapsulation with the public key."
Specifically, encrypted messages convey an encryption key encapsulated with a
public-key scheme, along with one or more arbitrary-sized ciphertexts encrypted
using that key. This type of public key encryption has many applications in
practice, including Messaging Layer Security [mls-protocol] and
TLS Encrypted ClientHello [tls-esni].

Currently, there are numerous competing and non-interoperable standards and
variants for hybrid encryption, mostly based on ECIES, including [ANSI X9.63 (ECIES)],
[IEEE1363], [ISO/IEC 18033-2], and [SECG SEC 1].
See [MAEA10] for a thorough comparison. All these existing
schemes have problems, e.g., because they rely on outdated primitives, lack
proofs of IND-CCA2 security, or fail to provide test vectors.

This document defines an HPKE scheme that provides a subset
of the functions provided by the collection of schemes above, but
specified with sufficient clarity that they can be interoperably
implemented. The HPKE construction defined herein is secure against (adaptive)
chosen ciphertext attacks (IND-CCA2 secure) under classical assumptions about
the underlying primitives [HPKEAnalysis], [ABHKLR20]. A summary of
these analyses is in Section 9.1.

This document represents the consensus of the Crypto Forum Research Group (CFRG).

# Notation

The following terms are used throughout this document to describe the
operations, roles, and behaviors of HPKE:

- `(skX, pkX)`: A Key Encapsulation Mechanism (KEM) key pair used in role X,
  where X is one of S, R, or E as sender, recipient, and ephemeral, respectively;
  `skX` is the private key and `pkX` is the public key.
- `pk(skX)`: The KEM public key corresponding to the KEM private key `skX`.
- Sender (S): Role of entity which sends an encrypted message.
- Recipient (R): Role of entity which receives an encrypted message.
- Ephemeral (E): Role of a fresh random value meant for one-time use.
- `I2OSP(n, w)`: Convert non-negative integer `n` to a `w`-length,
  big-endian byte string as described in [RFC8017].
- `OS2IP(x)`: Convert byte string `x` to a non-negative integer as
  described in [RFC8017], assuming big-endian byte order.
- `concat(x0, ..., xN)`: Concatenation of byte strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`.
- `random(n)`: A pseudorandom byte string of length `n` bytes
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

- A Key Encapsulation Mechanism ([KEM](`mod@crate::hpke::kem`))
- A Key Derivation Function ([KDF](`crate::hpke::kdf`))
- An [AEAD](`crate::hpke::aead`) encryption algorithm [RFC5116]

A _ciphersuite_ is a triple (KEM, KDF, AEAD) containing a choice of algorithm
for each primitive.

A set of algorithm identifiers for concrete instantiations of these
primitives is provided in [KEM](`crate::hpke::kem::KEM`), [KDF](`crate::hpke::kdf::KDF`), and [AEAD](`crate::hpke::aead::AEAD`).
Algorithm identifier values are two bytes long.
Future specifications may introduce new KEM, KDF, and AEAD algorithm
identifiers and retain the security guarantees presented in this document.

Note that [`GenerateKeyPair`](<`crate::hpke::kem::GenerateKeyPair()`>) can be implemented as [`DeriveKeyPair(random(Nsk))`](<`crate::hpke::kem::DeriveKeyPair()`>).

The notation `pk(skX)`, depending on its use and the KEM and its
implementation, is either the
computation of the public key using the private key, or just syntax
expressing the retrieval of the public key assuming it is stored along
with the private key object.

# Hybrid Public Key Encryption

In this section, we define a few HPKE variants. All variants take a
recipient public key and a sequence of plaintexts `pt`, and produce an
encapsulated key `enc` and a sequence of ciphertexts `ct`. These outputs are
constructed so that only the holder of `skR` can decapsulate the key from
`enc` and decrypt the ciphertexts. All the algorithms also take an
`info` parameter that can be used to influence the generation of keys
(e.g., to fold in identity information) and an `aad` parameter that
provides Additional Authenticated Data to the [`AEAD`](`crate::hpke::aead::AEAD`) algorithm in use.

In addition to the base case of encrypting to a public key, we
include three authenticated variants, one which authenticates
possession of a pre-shared key, one which authenticates
possession of a [KEM](`mod@crate::hpke::kem`) private key, and one which authenticates possession of both
a pre-shared key and a [KEM](`mod@crate::hpke::kem`) private key. All authenticated variants contribute
additional keying material to the encryption operation. The following one-byte
values will be used to distinguish between modes:

| Mode          | Value |
| :------------ | :---- |
| mode_base     | 0x00  |
| mode_psk      | 0x01  |
| mode_auth     | 0x02  |
| mode_auth_psk | 0x03  |

All these cases follow the same basic two-step pattern:

1. Set up an encryption context that is shared between the sender
   and the recipient.
2. Use that context to encrypt or decrypt content.

A _context_ is an implementation-specific structure that encodes
the AEAD algorithm and key in use, and manages the nonces used so
that the same nonce is not used with multiple plaintexts. It also
has an interface for exporting secret values, as described in
[`Context_Export`]. See [HPKE DEM](`ContextS_Seal`) for a description of this structure
and its interfaces. HPKE decryption fails when the underlying AEAD
decryption fails.

The constructions described here presume that the relevant non-private
parameters (`enc`, `psk_id`, etc.) are transported between the sender and the
recipient by some application making use of HPKE. Moreover, a recipient with more
than one public key needs some way of determining which of its public keys was
used for the encapsulation operation. As an example, applications may send this
information alongside a ciphertext from sender to recipient. Specification of
such a mechanism is left to the application. See [Message Encoding](#message-encoding) for more
details.

Note that some KEMs may not support [`AuthEncap()`](<crate::hpke::kem::AuthEncap()>) or [`AuthDecap()`](<crate::hpke::kem::AuthDecap()>).
For such KEMs, only `mode_base` or `mode_psk` are supported. Future specifications
which define new KEMs MUST indicate whether these modes are supported.
See [Future KEMs](mod@crate::hpke::kem#future-kems) for more details.

The procedures described in this section are laid out in a
Python-like pseudocode. The algorithms in use are left implicit.
See the [Implementation Considerations Section](#hacspec-implementation-considerations)
for details on the differences to this hacspec implementation.

## Creating the Encryption Context

The variants of HPKE defined in this document share a common
key schedule that translates the protocol inputs into an encryption
context.

See [`KeySchedule()`] for details.

### Encryption to a Public Key

The most basic function of an HPKE scheme is to enable encryption
to the holder of a given KEM private key.

See [`SetupBaseS()`] and [`SetupBaseR()`] for details.

### Authentication using a Pre-Shared Key

This variant extends the base mechanism by allowing the recipient to
authenticate that the sender possessed a given PSK.

See [`SetupPSKS()`] and [`SetupPSKR()`] for details.

### Authentication using an Asymmetric Key

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given KEM private key.

See [`SetupAuthS()`] and [`SetupAuthR()`] for details.

### Authentication using both a PSK and an Asymmetric Key

This mode is a straightforward combination of the PSK and
authenticated modes.

See [`SetupAuthPSKS()`] and [`SetupAuthPSKR()`] for details.

## Encryption and Decryption

HPKE allows multiple encryption operations to be done based on a
given setup transaction.

See [`ContextS_Seal`] and [`ContextR_Open`] for details.

## Secret Export

HPKE provides an interface for exporting secrets from the encryption context
using a variable-length PRF, similar to the TLS 1.3 exporter interface.

See [`Context_Export`] for details.

# Single-Shot APIs

## Encryption and Decryption - Single-Shot

In many cases, applications encrypt only a single message to a recipient's public key.

See [`HpkeSeal`] and [`HpkeOpen`] for details.

## Secret Export - Single-Shot

Applications may also want to derive a secret known only to a given recipient.
This section provides templates for HPKE APIs that implement stateless
"single-shot" secret export using APIs specified in [Secret Export](#secret-export):

See [`SendExport`] and [`ReceiveExport`].

As in [Single Shot Encryption](#encryption-and-decryption---single-shot), the `MODE` template parameter is one of Base, PSK,
Auth, or AuthPSK. The optional parameters indicated by "..." depend on `MODE` and may
be empty.

# Algorithm Identifiers

This section lists algorithm identifiers suitable for different HPKE configurations.
Future specifications may introduce new KEM, KDF, and AEAD algorithm identifiers
and retain the security guarantees presented in this document provided they adhere
to the security requirements in [KEM Security](mod@crate::hpke::kem#security-requirements-on-a-kem-used-within-hpke), [KDF Security](mod@crate::hpke::kdf#security-requirements-on-a-kdf), and
[AEAD Security](mod@crate::hpke::aead#security-requirements-on-an-aead), respectively.

See [KDF](mod@crate::hpke::kdf), [KEM](mod@crate::hpke::kem), and [AEAD](mod@crate::hpke::aead) for details on the algorithms.

# API Considerations

This section documents considerations for interfaces to implementations of HPKE.
This includes error handling considerations and recommendations that improve
interoperability when HPKE is used in applications.

## Auxiliary Authenticated Application Information

HPKE has two places at which applications can specify auxiliary authenticated information:
(1) during context construction via the Setup `info` parameter, and (2) during Context
operations, i.e., with the `aad` parameter for `Open()` and `Seal()`, and the `exporter_context` parameter
for `Export()`. Application information applicable to multiple operations on a single Context
should use the Setup `info` parameter. This avoids redundantly processing this information for
each Context operation. In contrast, application information that varies on a per-message basis
should be specified via the Context APIs (`Seal()`, `Open()`, or `Export()`).

Applications that only use the single-shot APIs described in {{single-shot-apis}} should use the
Setup `info` parameter for specifying auxiliary authenticated information. Implementations which
only expose single-shot APIs should not allow applications to use both Setup `info` and Context
`aad` or `exporter_context` auxiliary information parameters.

## Errors

The high-level, public HPKE APIs specified in this document are all fallible.

See [Errors](mod@crate::hpke::errors) for details.

# Message Encoding

This document does not specify a wire format encoding for HPKE messages. Applications
that adopt HPKE must therefore specify an unambiguous encoding mechanism which includes,
minimally: the encapsulated value `enc`, ciphertext value(s) (and order if there are
multiple), and any info values that are not implicit. One example of a non-implicit
value is the recipient public key used for encapsulation, which may be needed if a
recipient has more than one public key.

The AEAD interface used in this document is based on [RFC5116], which produces and
consumes a single ciphertext value. As discussed in [RFC5116], this ciphertext value
contains the encrypted plaintext as well as any authentication data, encoded in a manner
described by the individual AEAD scheme. Some implementations are not structured in this
way, instead providing a separate ciphertext and authentication tag. When such
AEAD implementations are used in HPKE implementations, the HPKE implementation must combine
these inputs into a single ciphertext value within [`Seal()`](<`HpkeSeal()`>), and parse them out within
[`Open()`](<`HpkeOpen()`>), where the parsing details are defined by the AEAD scheme. For example, with
the AES-GCM schemes specified in this document, the GCM authentication tag is placed in
the last Nt bytes of the ciphertext output.

[hpke rfc]: https://datatracker.ietf.org/doc/draft-irtf-cfrg-hpke/
[rfc1421]: https://datatracker.ietf.org/doc/rfc1421/
[tls-esni]: https://datatracker.ietf.org/doc/draft-ietf-tls-esni/
[mls-protocol]: https://datatracker.ietf.org/doc/draft-ietf-mls-protocol/
[ansi x9.63 (ecies)]: https://webstore.ansi.org/Standards/ASCX9/ANSIX9632011R2017
[ieee1363]: https://standards.ieee.org/standard/1363a-2004.html
[iso/iec 18033-2]: https://webstore.iec.ch/publication/10633&preview=1
[secg sec 1]: https://secg.org/sec1-v2.pdf
[maea10]: https://ieeexplore.ieee.org/abstract/document/5604194/
[hpkeanalysis]: https://eprint.iacr.org/2020/243
[abhklr20]: https://eprint.iacr.org/2020/1499
[rfc8017]: https://datatracker.ietf.org/doc/rfc8017/
[rfc5116]: https://www.rfc-editor.org/info/rfc5116
[publication queue]: https://www.rfc-editor.org/current_queue.php
