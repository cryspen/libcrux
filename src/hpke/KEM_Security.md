## Security Requirements on a KEM used within HPKE

A KEM used within HPKE MUST allow HPKE to satisfy its desired security
properties described in its security properties section.

In particular, the KEM
shared secret MUST be a uniformly random byte string of length [`Nsecret`].
This means, for instance, that it would not be sufficient if the KEM
shared secret is only uniformly random as an element of some set prior
to its encoding as byte string.

### Encap/Decap Interface

As mentioned in [sec-considerations], [CS01] provides some indications
that if the KEM's [`Encap()`]/[`Decap()`] interface (which is used in the Base
and PSK modes), is IND-CCA2-secure, HPKE is able to satisfy its desired
security properties. An appropriate definition of IND-CCA2-security for
KEMs can be found in [CS01] and [BHK09].

### AuthEncap/AuthDecap Interface

The analysis of HPKE's Auth mode single-shot encryption API in [ABHKLR20]
provides composition theorems that guarantee that HPKE's Auth mode achieves
its desired security properties if the KEM's [`AuthEncap()`]/[`AuthDecap()`]
interface satisfies multi-user Outsider-CCA, Outsider-Auth, and
Insider-CCA security as defined in the same paper.

Intuitively, Outsider-CCA security formalizes confidentiality, and
Outsider-Auth security formalizes authentication of the KEM shared secret
in case none of the sender or recipient private keys are compromised.
Insider-CCA security formalizes confidentiality of the KEM shared secret
in case the sender private key is known or chosen by the adversary.
(If the recipient private key is known or chosen by the adversary,
confidentiality is trivially broken, because then the adversary knows
all secrets on the recipient's side).

An Insider-Auth security notion would formalize authentication of the
KEM shared secret in case the recipient private key is known or chosen
by the adversary. (If the sender private key is known or chosen by the
adversary, it can create KEM ciphertexts in the name of the sender).
Because of the generic attack on an analogous Insider-Auth security
notion of HPKE, a definition of
Insider-Auth security for KEMs used within HPKE is not useful.

### KEM Key Reuse

An `ikm` input to [`DeriveKeyPair()`] MUST NOT be
reused elsewhere, in particular not with [`DeriveKeyPair()`] of a
different KEM.

The randomness used in [`Encap()`] and [`AuthEncap()`] to generate the
KEM shared secret or its encapsulation MUST NOT be reused elsewhere.

As a sender or recipient KEM key pair works with all modes, it can
be used with multiple modes in parallel. HPKE is constructed to be
secure in such settings due to domain separation using the `suite_id`
variable. However, there is no formal proof of security at the time of
writing for using multiple modes in parallel; [HPKEAnalysis] and
[ABHKLR20] only analyze isolated modes.

[hpkeanalysis]: https://eprint.iacr.org/2020/243
[abhklr20]: https://eprint.iacr.org/2020/1499
[CS01]: https://eprint.iacr.org/2001/108
[BHK09]: https://eprint.iacr.org/2009/418
