## Security Properties

HPKE has several security goals, depending on the mode of operation,
against active and adaptive attackers that can compromise partial
secrets of senders and recipients. The desired security goals are
detailed below:

- Message secrecy: Confidentiality of the sender's messages against
  chosen ciphertext attacks
- Export key secrecy: Indistinguishability of each export
  secret from a uniformly random bitstring of equal length, i.e.,
  `Context.Export` is a variable-length PRF
- Sender authentication: Proof of sender origin for PSK, Auth, and
  AuthPSK modes

These security goals are expected to hold for any honest sender and
honest recipient keys, as well as if the honest sender and honest
recipient keys are the same.

HPKE mitigates malleability problems (called benign malleability [SECG SEC 1]) in prior
public key encryption standards based on ECIES by including all public keys in the
context of the key schedule.

HPKE does not provide forward secrecy with respect to recipient compromise.
In the Base and Auth modes, the secrecy properties are only expected to
hold if the recipient private key `skR` is not compromised at any point
in time. In the PSK and AuthPSK modes, the secrecy properties are
expected to hold if the recipient private key `skR` and the pre-shared key
are not both compromised at any point in time. See [the non-goals section](#application-embedding-and-non-goals) for more
details.

In the Auth mode, sender authentication is generally expected to hold if
the sender private key `skS` is not compromised at the time of message
reception. In the AuthPSK mode, sender authentication is generally
expected to hold if at the time of message reception, the sender private
key skS and the pre-shared key are not both compromised.

Besides forward secrecy and key-compromise impersonation, which are highlighted
in this section because of their particular cryptographic importance, HPKE
has other non-goals that are described in [the non-goals section](#application-embedding-and-non-goals): no tolerance of
message reordering or loss, no downgrade or replay prevention, no hiding of the
plaintext length, no protection against bad ephemeral randomness. [The non-goals section](#application-embedding-and-non-goals)
suggests application-level mitigations for some of them.

### Key-Compromise Impersonation

The DHKEM variants defined in this document are
vulnerable to key-compromise impersonation attacks [BJM97],
which means that sender authentication cannot be expected to hold in the
Auth mode if the recipient private key `skR` is compromised, and in the
AuthPSK mode if the pre-shared key and the recipient private key `skR` are
both compromised. NaCl's `box` interface [NaCl] has the same issue. At
the same time, this enables repudiability.

As shown by [ABHKLR20], key-compromise impersonation attacks are generally possible on HPKE
because KEM ciphertexts are not bound to HPKE messages. An adversary who
knows a recipient's private key can decapsulate an observed KEM ciphertext,
compute the key schedule, and encrypt an arbitrary message that the recipient
will accept as coming from the original sender. Importantly, this is possible even
with a KEM that is resistant to key-compromise impersonation attacks. As a
result, mitigating this issue requires fundamental changes that are out-of-scope
of this specification.

Applications that require resistance against key-compromise impersonation
SHOULD take extra steps to prevent this attack. One possibility is to
produce a digital signature over `(enc, ct)` tuples using a sender's
private key -- where `ct` is an AEAD ciphertext produced by the single-shot
or multi-shot API, and `enc` the corresponding KEM encapsulated key.

Given these properties, pre-shared keys strengthen both the authentication and the
secrecy properties in certain adversary models. One particular example in which
this can be useful is a hybrid quantum setting: if a
non-quantum-resistant KEM used with HPKE is broken by a
quantum computer, the security properties are preserved through the use
of a pre-shared key. As described in [RFC8696] Section 7 this
assumes that the pre-shared key has not been compromised.

### Computational Analysis

It is shown in [CS01] that a hybrid public-key encryption scheme of
essentially the same form as the Base mode described here is
IND-CCA2-secure as long as the underlying KEM and AEAD schemes are
IND-CCA2-secure. Moreover, it is shown in [HHK06] that IND-CCA2 security
of the KEM and the data encapsulation mechanism are necessary conditions
to achieve IND-CCA2 security for hybrid public-key encryption.
The main difference between the scheme proposed in [CS01]
and the Base mode in this document (both named HPKE) is that we interpose
some KDF calls between the KEM and the AEAD. Analyzing the HPKE Base mode
instantiation in this document therefore requires verifying that the
additional KDF calls do not cause the IND-CCA2 property to fail, as
well as verifying the additional export key secrecy property.

Analysis of the PSK, Auth, and AuthPSK modes defined in this document
additionally requires verifying the sender authentication property.
While the PSK mode just adds supplementary keying material to the key
schedule, the Auth and AuthPSK modes make use of a non-standard
authenticated KEM construction. Generally, the authenticated modes of
HPKE can be viewed and analyzed as flavors of signcryption [SigncryptionDZ10].

A preliminary computational analysis of all HPKE modes has been done
in [HPKEAnalysis], indicating asymptotic security for the case where
the KEM is DHKEM, the AEAD is any IND-CPA and INT-CTXT-secure scheme,
and the DH group and KDF satisfy the following conditions:

- DH group: The gap Diffie-Hellman (GDH) problem is hard in the
  appropriate subgroup [GAP].
- `Extract()` and `Expand()`: `Extract()` can be modeled as a random oracle.
  `Expand()` can be modeled as a pseudorandom function, wherein the first
  argument is the key.

In particular, the KDFs and DH groups defined in this document (see
[kdf-ids](`crate::hpke::kdf::KDF`) and [kem-ids](`crate::hpke::kem::KEM`)) satisfy these properties when used as
specified. The analysis in [HPKEAnalysis] demonstrates that under these
constraints, HPKE continues to provide IND-CCA2 security, and provides
the additional properties noted above. Also, the analysis confirms the
expected properties hold under the different key compromise cases
mentioned above. The analysis considers a sender that sends one message
using the encryption context, and additionally exports two independent
secrets using the secret export interface.

The table below summarizes the main results from [HPKEAnalysis]. N/A
means that a property does not apply for the given mode, whereas `y` means
the given mode satisfies the property.

| Variant | Message Sec. | Export Sec. | Sender Auth. |
| :------ | :----------: | :---------: | :----------: |
| Base    |      y       |      y      |     N/A      |
| PSK     |      y       |      y      |      y       |
| Auth    |      y       |      y      |      y       |
| AuthPSK |      y       |      y      |      y       |

If non-DH-based KEMs are to be used with HPKE, further analysis will be
necessary to prove their security. The results from [CS01] provide
some indication that any IND-CCA2-secure KEM will suffice here, but are
not conclusive given the differences in the schemes.

A detailed computational analysis of HPKE's Auth mode single-shot
encryption API has been done in [ABHKLR20].
The paper defines security notions for authenticated
KEMs and for authenticated public key encryption, using the outsider and
insider security terminology known from signcryption [SigncryptionDZ10].
The analysis proves that DHKEM's [`AuthEncap()`](<`crate::hpke::kem::AuthEncap()`>)/[`AuthDecap()`](<`crate::hpke::kem::AuthDecap()`>) interface
fulfills these notions for all Diffie-Hellman groups specified in this document,
and indicates exact security bounds, under the assumption that the
gap Diffie-Hellman (GDH) problem is hard in the appropriate subgroup [GAP],
and that HKDF can be modeled as a random oracle.

Further, [ABHKLR20] proves composition theorems, showing that HPKE's
Auth mode fulfills the security notions of authenticated public key encryption
for all KDFs and AEAD schemes specified in this document, given any
authenticated KEM satisfying the previously defined security notions
for authenticated KEMs. The theorems assume that the KEM is perfectly correct;
they could easily be adapted to work with KEMs that have a non-zero but negligible
probability for decryption failure. The assumptions on the KDF are that `Extract()`
and `Expand()` can be modeled as pseudorandom functions wherein the first
argument is the key, respectively. The assumption for the AEAD is
IND-CPA and IND-CTXT security.

In summary, the analysis in [ABHKLR20] proves that the single-shot encryption API of HPKE's
Auth mode satisfies the desired message confidentiality and sender
authentication properties listed at the beginning of this section;
it does not consider multiple messages, nor the secret export API.

### Post-Quantum Security

All of [CS01], [HPKEAnalysis], and [ABHKLR20] are premised on
classical security models and assumptions, and do not consider
adversaries capable of quantum computation. A full proof of post-quantum
security would need to take appropriate security models and assumptions
into account, in addition to simply using a post-quantum KEM. However,
the composition theorems from [ABHKLR20] for HPKE's Auth mode only make
standard assumptions (i.e., no random oracle assumption) that are expected
to hold against quantum adversaries (although with slightly worse bounds).
Thus, these composition theorems, in combination with a post-quantum-secure
authenticated KEM, guarantee the post-quantum security of HPKE's Auth mode.

In future work, the analysis from [ABHKLR20] can be extended to cover
HPKE's other modes and desired security properties.
The hybrid quantum-resistance property described above, which is achieved
by using the PSK or AuthPSK mode, is not proven in [HPKEAnalysis] because
this analysis requires the random oracle model; in a quantum
setting, this model needs adaption to, for example, the quantum random
oracle model.

## Pre-Shared Key Recommendations

In the PSK and AuthPSK modes, the PSK MUST have at least 32 bytes of
entropy and SHOULD be of length [`Nh`](<`crate::hpke::kdf::Nh()`>) bytes or longer. Using a PSK longer than
32 bytes but shorter than [`Nh`](<`crate::hpke::kdf::Nh()`>) bytes is permitted.

HPKE is specified to use HKDF as key derivation function. HKDF is not
designed to slow down dictionary attacks, see [RFC5869]. Thus, HPKE's
PSK mechanism is not suitable for use with a low-entropy password as the
PSK: in scenarios in which the adversary knows the KEM shared secret
`shared_secret` and has access to an oracle that allows to distinguish between
a good and a wrong PSK, it can perform PSK-recovering attacks. This oracle
can be the decryption operation on a captured HPKE ciphertext or any other
recipient behavior which is observably different when using a wrong PSK.
The adversary knows the KEM shared secret `shared_secret` if it knows all
KEM private keys of one participant. In the PSK mode this is trivially
the case if the adversary acts as sender.

To recover a lower entropy PSK, an attacker in this scenario can trivially
perform a dictionary attack. Given a set `S` of possible PSK values, the
attacker generates an HPKE ciphertext for each value in `S`, and submits
the resulting ciphertexts to the oracle to learn which PSK is being used by
the recipient. Further, because HPKE uses AEAD schemes that are not key-committing,
an attacker can mount a partitioning oracle attack [LGR20] which can recover
the PSK from a set of `S` possible PSK values, with |S| = m\*k, in roughly
m + log k queries to the oracle using ciphertexts of length proportional to
k, the maximum message length in blocks. (Applying the multi-collision algorithm from
[LGR20] requires a small adaptation to the algorithm wherein the appropriate nonce
is computed for each candidate key. This modification adds one call to HKDF per key.
The number of partitioning oracle queries remains unchanged.) As a result, the PSK
must therefore be chosen with sufficient entropy so that m + log k is prohibitive for
attackers (e.g., 2^128). Future specifications can define new AEAD algorithms which
are key-committing.

## Domain Separation

HPKE allows combining a DHKEM variant `DHKEM(Group, KDF')` and a KDF
such that both KDFs are instantiated by the same KDF. By design, the
calls to `Extract()` and `Expand()` inside DHKEM and the remainder of
HPKE use separate input domains. This justifies modeling them as
independent functions even if instantiated by the same KDF.
This domain separation between DHKEM and the remainder of HPKE is achieved by
the `suite_id` values in `LabeledExtract()` and `LabeledExpand()`:
The values used (`KEM...` in DHKEM and `HPKE...` in the remainder of HPKE)
are prefix-free (a set is prefix-free if no element is a prefix of
another within the set).

Future KEM instantiations MUST ensure, should `Extract()` and
`Expand()` be used internally, that they can be modeled as functions
independent from the invocations of `Extract()` and `Expand()` in the
remainder of HPKE. One way to ensure this is by using `LabeledExtract()`
and `LabeledExpand()` with a `suite_id` as defined in [base-crypto],
which will ensure input domain separation as outlined above.
Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's `Extract()` or `Expand()`, such as `Hash()` and `HMAC()` in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside `Extract()` or
`Expand()`. In HPKE's `KeySchedule()` this is avoided by using `Extract()` instead of
`Hash()` on the arbitrary-length inputs `info` and `psk_id`.

The string literal "HPKE-v1" used in `LabeledExtract()` and `LabeledExpand()`
ensures that any secrets derived in HPKE are bound to the scheme's name
and version, even when possibly derived from the same Diffie-Hellman or
KEM shared secret as in another scheme or version.

## Application Embedding and Non-Goals

HPKE is designed to be a fairly low-level mechanism. As a result, it assumes
that certain properties are provided by the application in which HPKE is
embedded, and leaves certain security properties to be provided by other
mechanisms. Otherwise said, certain properties are out-of-scope for HPKE.

### Message Order and Message Loss

The primary requirement that HPKE imposes on applications is the requirement
that ciphertexts MUST be presented to `ContextR.Open()` in the same order in
which they were generated by `ContextS.Seal()`. When the single-shot API is
used (see [single-shot-apis]), this is trivially true (since there is only
ever one ciphertext. Applications that allow for multiple invocations of
`Open()` / `Seal()` on the same context MUST enforce the ordering property
described above.

Ordering requirements of this character are usually fulfilled by providing a
sequence number in the framing of encrypted messages. Whatever information is
used to determine the ordering of HPKE-encrypted messages SHOULD be included in
the AAD passed to `ContextS.Seal()` and `ContextR.Open()`. The specifics of
this scheme are up to the application.

HPKE is not tolerant of lost messages. Applications MUST be able to detect when
a message has been lost. When an unrecoverable loss is detected, the application MUST discard
any associated HPKE context.

### Downgrade Prevention

HPKE assumes that the sender and recipient agree on what algorithms to use.
Depending on how these algorithms are negotiated, it may be possible for an
intermediary to force the two parties to use suboptimal algorithms.

### Replay Protection

The requirement that ciphertexts be presented to the `ContextR.Open()` function
in the same order they were generated by `ContextS.Seal()` provides a degree of
replay protection within a stream of ciphertexts resulting from a given context.
HPKE provides no other replay protection.

### Forward Secrecy

HPKE ciphertexts are not forward secret with respect to recipient compromise
in any mode. This means that compromise of long-term recipient secrets allows
an attacker to decrypt past ciphertexts encrypted under said secrets. This is because
only long-term secrets are used on the side of the recipient.

HPKE ciphertexts are forward secret with respect to sender compromise in all
modes. This is because ephemeral randomness is used on the sender's side, which
is supposed to be erased directly after computation of the KEM shared secret and
ciphertext.

### Bad Ephemeral Randomness

If the randomness used for KEM encapsulation is bad -- i.e. of low entropy or
compromised because of a broken or subverted random number generator -- the
confidentiality guarantees of HPKE degrade significantly. In Base mode,
confidentiality guarantees can be lost completely; in the other modes, at least forward secrecy with
respect to sender compromise can be lost completely.

Such a situation could also lead to the reuse of the same KEM shared secret
and thus to the reuse of same key-nonce pairs for the AEAD.
The AEADs specified in this document are not secure
in case of nonce reuse. This attack vector is particularly relevant in
authenticated modes because knowledge of the ephemeral randomness is not
enough to derive `shared_secret` in these modes.

One way for applications to mitigate the impacts of bad ephemeral randomness is
to combine ephemeral randomness with a local long-term secret that has been
generated securely, as described in [RFC8937].

### Hiding Plaintext Length

AEAD ciphertexts produced by HPKE do not hide the plaintext length. Applications
requiring this level of privacy should use a suitable padding mechanism. See
[tls-esni] and [RFC8467] for examples of protocol-specific
padding policies.

## Bidirectional Encryption

HPKE encryption is unidirectional from sender
to recipient. Applications that require bidirectional encryption can derive
necessary keying material with the Secret Export interface.
The type and length of such keying material depends on the application use
case.

As an example, if an application needs AEAD encryption from recipient to
sender, it can derive a key and nonce from the corresponding HPKE context
as follows:

```text
key = context.Export("response key", Nk)
nonce = context.Export("response nonce", Nn)
```

In this example, the length of each secret is based on the AEAD algorithm
used for the corresponding HPKE context.

Note that HPKE's limitations with regard to sender authentication become limits
on recipient authentication in this context. In particular, in the Base mode,
there is no authentication of the remote party at all. Even in the Auth mode,
where the remote party has proven that they hold a specific private key, this
authentication is still subject to Key-Compromise Impersonation, as discussed
in [kci](#key-compromise-impersonation).

## Metadata Protection

The authenticated modes of HPKE (PSK, Auth, AuthPSK) require that the recipient
know what key material to use for the sender. This can be signaled in
applications by sending the PSK ID (`psk_id` above) and/or the sender's public
key (`pkS`). However, these values themselves might be considered sensitive,
since in a given application context, they might identify the sender.

An application that wishes to protect these metadata values without requiring
further provisioning of keys can use an additional instance of HPKE, using the
unauthenticated Base mode. Where the application might have sent `(psk_id, pkS, enc, ciphertext)` before, it would now send `(enc2, ciphertext2, enc, ciphertext)`,
where `(enc2, ciphertext2)` represent the encryption of the `psk_id` and `pkS`
values.

The cost of this approach is an additional KEM operation each for the sender and
the recipient. A potential lower-cost approach (involving only symmetric
operations) would be available if the nonce-protection schemes in [BNT19]
could be extended to cover other metadata. However, this construction would
require further analysis.

[cs01]: https://eprint.iacr.org/2001/108
[signcryptiondz10]: https://doi.org/10.1007/978-3-540-89411-7
[gap]: https://link.springer.com/content/pdf/10.1007/3-540-44586-2_8.pdf
[lgr20]: https://eprint.iacr.org/2020/1491
[rfc5869]: https://www.rfc-editor.org/info/rfc5869
[nacl]: https://nacl.cr.yp.to/box.html
[bjm97]: https://doi.org/10.1007/bfb0024447
[rfc8696]: https://www.rfc-editor.org/info/rfc8696
[rfc8937]: https://www.rfc-editor.org/info/rfc8937
[rfc8467]: https://www.rfc-editor.org/info/rfc8467
[bnt19]: http://dx.doi.org/10.1007/978-3-030-26948-7_9
[hhk06]: https://eprint.iacr.org/2006/265
