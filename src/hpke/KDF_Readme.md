# Key Derivation

> 💡 This is a hacspec representation of the [HPKE RFC].
> The text is mostly verbatim from the RFC with changes where required.
> It demonstrates the possibilities of hacspec for specifications.

A Key Derivation Function (KDF):

- `Extract(salt, ikm)`: Extract a pseudorandom key of fixed length `Nh` bytes
  from input keying material `ikm` and an optional byte string
  `salt`.
- `Expand(prk, info, L)`: Expand a pseudorandom key `prk` using
  optional string `info` into `L` bytes of output keying material.
- `Nh`: The output size of the `Extract()` function in bytes.

HKDF is the only specified KDF and an external dependency: [`hacspec-hkdf`].

# Labeled HKDF

The following two functions are defined to facilitate domain separation of
KDF calls as well as context binding:

```text
def LabeledExtract(salt, label, ikm):
  labeled_ikm = concat("HPKE-v1", suite_id, label, ikm)
  return Extract(salt, labeled_ikm)

def LabeledExpand(prk, label, info, L):
  labeled_info = concat(I2OSP(L, 2), "HPKE-v1", suite_id,
                        label, info)
  return Expand(prk, labeled_info, L)
```

The value of `suite_id` depends on where the KDF is used; it is assumed
implicit from the implementation and not passed as a parameter. If used
inside a KEM algorithm, `suite_id` MUST start with "KEM" and identify
this KEM algorithm; if used in the remainder of HPKE, it MUST start with
"HPKE" and identify the entire ciphersuite in use.

# Security Requirements on a KDF

The choice of the KDF for HPKE SHOULD be made based on the security
level provided by the KEM and, if applicable, by the PSK. The KDF
SHOULD at least have the security level of the KEM and SHOULD
at least have the security level provided by the PSK.

## Domain Separation

HPKE allows combining a DHKEM variant `DHKEM(Group, KDF')` and a KDF
such that both KDFs are instantiated by the same KDF. By design, the
calls to `Extract()` and `Expand()` inside DHKEM and the remainder of
HPKE use separate input domains. This justifies modeling them as
independent functions even if instantiated by the same KDF.
This domain separation between DHKEM and the remainder of HPKE is achieved by
the `suite_id` values in [`LabeledExtract()`] and [`LabeledExpand()`]:
The values used (`KEM...` in DHKEM and `HPKE...` in the remainder of HPKE)
are prefix-free (a set is prefix-free if no element is a prefix of
another within the set).

Future KEM instantiations MUST ensure, should `Extract()` and
`Expand()` be used internally, that they can be modeled as functions
independent from the invocations of `Extract()` and `Expand()` in the
remainder of HPKE. One way to ensure this is by using `LabeledExtract()`
and `LabeledExpand()` with a `suite_id` as defined in {{base-crypto}},
which will ensure input domain separation as outlined above.
Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's `Extract()` or `Expand()`, such as `Hash()` and `HMAC()` in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside `Extract()` or
`Expand()`. In HPKE's `KeySchedule()` this is avoided by using `Extract()` instead of
`Hash()` on the arbitrary-length inputs `info` and `psk_id`.

The string literal "HPKE-v1" used in [`LabeledExtract()`] and [`LabeledExpand()`]
ensures that any secrets derived in HPKE are bound to the scheme's name
and version, even when possibly derived from the same Diffie-Hellman or
KEM shared secret as in another scheme or version.

## Input Length Restrictions

This document defines [`LabeledExtract()`] and [`LabeledExpand()`] based on the
KDFs listed above. These functions add prefixes to their respective
inputs `ikm` and `info` before calling the KDF's `Extract()` and `Expand()`
functions. This leads to a reduction of the maximum input length that
is available for the inputs `psk`, `psk_id`, `info`, `exporter_context`,
`ikm`, i.e., the variable-length parameters provided by HPKE applications.
The following table lists the maximum allowed lengths of these fields
for the KDFs defined in this document, as inclusive bounds in bytes:

| Input               | HKDF-SHA256  | HKDF-SHA384   | HKDF-SHA512   |
|:--------------------|:-------------|:--------------|:--------------|
| psk                 | 2^{61} - 88  | 2^{125} - 152 | 2^{125} - 152 |
| psk_id              | 2^{61} - 93  | 2^{125} - 157 | 2^{125} - 157 |
| info                | 2^{61} - 91  | 2^{125} - 155 | 2^{125} - 155 |
| exporter_context    | 2^{61} - 120 | 2^{125} - 200 | 2^{125} - 216 |
| ikm (DeriveKeyPair) | 2^{61} - 84  | 2^{125} - 148 | 2^{125} - 148 |

This shows that the limits are only marginally smaller than the maximum
input length of the underlying hash function; these limits are large and
unlikely to be reached in practical applications. Future specifications
which define new KDFs MUST specify bounds for these variable-length
parameters.

The RECOMMENDED limit for these values is 64 bytes. This would enable
interoperability with implementations that statically allocate memory
for these inputs to avoid memory allocations.

The values for `psk`, `psk_id`, `info`, and `ikm` which are inputs to
[`LabeledExtract()`] were computed with the following expression:

~~~text
max_size_hash_input - Nb - size_version_label -
    size_suite_id - size_input_label
~~~

The value for `exporter_context` which is an input to [`LabeledExpand()`]
was computed with the following expression:

~~~text
max_size_hash_input - Nb - Nh - size_version_label -
    size_suite_id - size_input_label - 2 - 1
~~~

In these equations, `max_size_hash_input` is the maximum input length
of the underlying hash function in bytes, `Nb` is the block size of the
underlying hash function in bytes, `size_version_label` is the size
of "HPKE-v1" in bytes and equals 7, `size_suite_id` is the size of the
`suite_id` in bytes and equals 5 for DHKEM (relevant for `ikm`) and 10 for the
remainder of HPKE (relevant for `psk`, `psk_id`, `info`, `exporter_context`),
and `size_input_label` is the size in bytes of the label used as parameter to
[`LabeledExtract()`] or [`LabeledExpand()`], the maximum of which is 13
across all labels in this document.

[hpke rfc]: https://datatracker.ietf.org/doc/draft-irtf-cfrg-hpke/
[publication queue]: https://www.rfc-editor.org/current_queue.php
