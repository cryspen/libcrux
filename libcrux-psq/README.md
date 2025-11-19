# Post-Quantum Pre-Shared-Key Protocol (PSQ) #

![pre-verification]

This crate implements a protocol for establishing, and registering a
post-quantum shared secret between an initiator and a responder.

## Query Mode

Query mode is a two-message protocol between initiator and responder.


```
Common inputs:
    - ctx

Inputs of A:
    - query_payload
    - query_aad
    - pk_B = g^s
    
Inputs of B: 
    - (sk_B = s, pk_B = g^s)
    - response_aad
    - query handler f

A: 
    (esk_A = x, epk_A = g^x) <- DH.KeyGen()
    tx0 = hash(0 | ctx | pk_B | epk_A)
    dh_shared_secret_query = DH.Derive(esk_A, pk_B)
    K_0  = KDF(dh_shared_secret_query, tx0)
    (enc_query, tag_query) <- AEAD.Encrypt(K_0, query_payload, query_aad)
    
A -> B: (epk_A, enc_query, tag_query, query_aad)

B:
    tx0 = hash(0 | ctx | pk_B | epk_A)
    dh_shared_secret_query = DH.Derive(sk_B, epk_A)
    K_0 = KDF(dh_shared_secret_query)
    query_payload = AEAD.Decrypt(K_0, enc_query, tag_query, query_aad)
    ...
    response_payload <- f(query_payload)
    ...
    (esk_B = y, epk_B = g^y) <- DH.KeyGen()
    tx2 = hash(2 | tx0 | epk_B)
    dh_shared_secret_response_1 = DH.Derive(sk_B, epk_A)
    dh_shared_secret_response_2 = DH.Derive(esk_B, epk_A)
    K_2 = KDF(K_0 | dh_shared_secret_response_1 | dh_shared_secret_response_2, tx2)
    (enc_response, tag_response) <- AEAD.Encrypt(K_2, response_payload, response_aad)

B -> A: (epk_B, enc_response, tag_response, response_aad)

A:
    tx2 = hash(2 | tx0 | epk_B)
    dh_shared_secret_response_1 = DH.Derive(esk_A, pk_B)
    dh_shared_secret_response_2 = DH.Derive(esk_A, epk_B)
    K_2 = KDF(K_0 | dh_shared_secret_response_1 | dh_shared_secret_response_2, tx2)
    response_payload = AEAD.Decrypt(K_2, enc_response, tag_response, response_aad)
```

## Registration Mode

### Handshake
```
Common Inputs:
    - ctx
    
Inputs of A: 
    - registration_payload
    - registration_outer_aad
    - registration_inner_aad
    - pk_B = g^s
    - (sk_A = c, pk_A = g^c)
    - pqpk_B (optional)
    
Inputs of B: 
    - (sk_B = s, pk_B = g^s)
    - (pqsk_B, pqpk_B)
    - query handler f,
    - response_aad, 
    - registration handler f
    
A: 
    (esk_A = x, epk_A = g^x) <- DH.KeyGen()
    tx0 = hash(0 | ctx | pk_B | epk_A)
    dh_shared_secret_outer = DH.Derive(esk_A, pk_B)
    K_0  = KDF(dh_shared_secret_outer, tx0)
    if pqpk_S provided
        (enc_pq, pq_shared_secret) <- PQKEM.Encapsulate(pqpk_S)
    tx1 = hash(1 | tx0 | pk_A | [pqpk_S] | [enc_pq])
    dh_shared_secret_inner = DH.Derive(sk_A, pk_B)
    K_1 = KDF(K_0 | dh_shared_secret_inner | [pq_shared_secret], tx1)
    (enc_inner, tag_inner) <- AEAD.Encrypt(K_1, registration_payload, registration_inner_aad)
    (enc_outer, tag_outer) <- AEAD.Encrypt(K_0, (pk_A | enc_inner | tag_inner | registration_inner_aad | [enc_pq]), registration_outer_aad)
    
A -> B: (epk_A, enc_outer, tag_outer, registration_outer_aad)

B:
    tx0 = hash(0 | ctx | pk_B | epk_A)
    dh_shared_secret_outer = DH.Derive(sk_B, epk_A)
    K_0 = KDF(dh_shared_secret_outer)
    (pk_A | enc_inner | tag_inner | registration_inner_aad | [enc_pq]) = AEAD.Decrypt(K_0, enc_outer, tag_outer, registration_outer_aad)
    if enc_pq provided
        pq_shared_secret <- PQKEM.Decapsulate(pqsk_B, enc_pq)
    tx1 = hash(1 | tx0 | pk_A | [pqpk_S] | [enc_pq])
    dh_shared_secret_inner = DH.Derive(sk_B, pk_A)
    K_1 = KDF(K_0 | dh_shared_secret_inner | [pq_shared_secret], tx1)
    registration_payload = AEAD.Decrypt(K_1, enc_inner, tag_inner, registration_inner_aad)
    ...
    response_payload <- f(registration_payload)
    ...
    (esk_B = y, epk_B = g^y) <- DH.KeyGen()
    tx2 = hash(2 | tx1 | epk_B)
    dh_shared_secret_response_1 = DH.Derive(esk_B, pk_A)
    dh_shared_secret_response_2 = DH.Derive(esk_B, epk_A)
    K_2 = KDF(K_1 | dh_shared_secret_response_1 | dh_shared_secret_response_2, tx2)
    (enc_response, tag_response) <- AEAD.Encrypt(K_2, response_payload, response_aad)
    
B -> A: (epk_B, enc_response, tag_response, response_aad)

A: 
    tx2 = hash(2 | tx1 | epk_B)
    dh_shared_secret_response_1 = DH.Derive(sk_A, epk_B)
    dh_shared_secret_response_2 = DH.Derive(esk_A, epk_B)
    K_2 = KDF(K_1 | dh_shared_secret_response_1 | dh_shared_secret_response_2, tx2)
    response_payload = AEAD.Decrypt(K_2, enc_response, tag_response, response_aad)

```

### Client-authenticating Handshake (Proposal)
```
Common Inputs:
    - ctx
    
Inputs of A: 
    - registration_payload
    - registration_outer_aad
    - registration_inner_aad
    - pk_B = g^s
    - (sk_A, vk_A)
    - pqpk_B (optional)
    
Inputs of B: 
    - (sk_B = s, pk_B = g^s)
    - (pqsk_B, pqpk_B)
    - query handler f,
    - response_aad, 
    - registration handler f
    
A: 
    (esk_A = x, epk_A = g^x) <- DH.KeyGen()
    tx0 = hash(0 | ctx | pk_B | epk_A)
    dh_shared_secret_outer = DH.Derive(esk_A, pk_B)
    K_0  = KDF(dh_shared_secret_outer, tx0)
    if pqpk_S provided
        (enc_pq, pq_shared_secret) <- PQKEM.Encapsulate(pqpk_S)
    tx1 = hash(1 | tx0 | vk_A | [pqpk_S] | [enc_pq])
    sigC = Sig.Sign(sk_A, tx1)
    K_1 = KDF(K_0 | [pq_shared_secret], tx1 | sigC)
    (enc_inner, tag_inner) <- AEAD.Encrypt(K_1, registration_payload, registration_inner_aad)
    (enc_outer, tag_outer) <- AEAD.Encrypt(K_0, (vk_A | enc_inner | tag_inner | registration_inner_aad | | sigC | [enc_pq]), registration_outer_aad)
    
A -> B: (epk_A, enc_outer, tag_outer, registration_outer_aad)

B:
    tx0 = hash(0 | ctx | pk_B | epk_A)
    dh_shared_secret_outer = DH.Derive(sk_B, epk_A)
    K_0 = KDF(dh_shared_secret_outer)
    (vk_A | enc_inner | tag_inner | registration_inner_aad | sigC | [enc_pq]) = AEAD.Decrypt(K_0, enc_outer, tag_outer, registration_outer_aad)
    tx1 = hash(1 | tx0 | vk_A | [pqpk_S] | [enc_pq])
    if !Sig.Verify(vk_A, tx1, sigC)
        abort
    if enc_pq provided
        pq_shared_secret <- PQKEM.Decapsulate(pqsk_B, enc_pq)
    K_1 = KDF(K_0 | [pq_shared_secret], tx1 | sigC)
    registration_payload = AEAD.Decrypt(K_1, enc_inner, tag_inner, registration_inner_aad)
    ...
    response_payload <- f(registration_payload)
    ...
    (esk_B = y, epk_B = g^y) <- DH.KeyGen()
    tx2 = hash(2 | tx1 | epk_B)
    dh_shared_secret_response = DH.Derive(esk_B, epk_A)
    K_2 = KDF(K_1 | dh_shared_secret_response, tx2)
    (enc_response, tag_response) <- AEAD.Encrypt(K_2, response_payload, response_aad)
    
B -> A: (epk_B, enc_response, tag_response, response_aad)

A: 
    tx2 = hash(2 | tx1 | epk_B)
    dh_shared_secret_response = DH.Derive(esk_A, epk_B)
    K_2 = KDF(K_1 | dh_shared_secret_response, tx2)
    response_payload = AEAD.Decrypt(K_2, enc_response, tag_response, response_aad)

```

### Derived Sessions

TODO

## PSQ v1
Under optional feature `v1`, this crate implements the first version of PSQ, a
protocol for establishing and mutually registering a pre-shared key
such that the protocol messages are secure against
harvest-now-decrypt-later (HNDL) passive quantum attackers.

This implementation is exposed via the `libcrux_psq::v1` module.

The protocol between initator `A` and receiver `B` roughly works as follows:

```
A:  (K_pq, enc_pq) <- PQPSK.Encaps(pqpk_B, sctx)
    (K_regA, N_regA) <- KDF(K_pq, "AEAD-Responder-Initiator")
    (K_regB, N_regB) <- KDF(K_pq, "AEAD-Initiator-Responder")
    PSK <- KDF(K_pq, "PSK-Registration")
    ts <- get_timestamp()
    signature <- Sign(sk_A, enc_pq)

A -> B: (enc_pq, ctxt_A = AEAD.Encrypt(K_regA, N_regA, ts || signature || vk_A || ...))

B:  K_pq <- PQPSK.Decaps(pqsk_B, pqpk_B, sctx)
    (K_regA, N_regA) <- KDF(K_pq, "AEAD-Responder-Initiator")
    (K_regB, N_regB) <- KDF(K_pq, "AEAD-Initiator-Responder")
    (ts || signature || vk_A || ...) <- AEAD.Decrypt(K_reqA, N_regA, ctxt)
    if Verify(vk, signature, enc_pq) != 1 || ts_elapsed(ts, psk_ttl) then 
        ABORT
    else
    PSK <- KDF(K_pq, "PSK-Registration")
    psk_handle <- gen_handle()
    store (psk_handle, PSK)

B -> A: ctxt_B = AEAD.Encrypt(K_regB, N_regB, psk_handle)

A:  psk_handle <- AEAD.Decrypt(K_reqB, N_regB, ctxt_B)
    PSK <- KDF(K_pq, "PSK-Registration")
        store (psk_handle, PSK)
```

where `PQPSK.Encaps(pqpk_B, sctx)` denotes the following procedure:

```
(ik, enc) <- PQ-KEM.Encaps(pk_B)
K_0 <- KDF(ik, pk_B || enc || sctxt)
K_m <- KDF(K_0, "Confirmation")
K <- KDF(K_0, "PQ-PSK")
mac <- MAC(K_m, "MAC-Input")
return (K, enc||mac)
```

`PQPSK.Decaps(sk_B, pk_B, enc||mac)` denotes the following procedure:

```
ik <- PQ-KEM.Decaps(pqsk_B, enc)
K_0 <- KDF(ik, pk_B || enc || sctxt)
K_m <- KDF(K_0, "Confirmation")
K <- KDF(K_0, "PQ-PSK")
recomputed_mac <- MAC(K_m, "MAC-Input")
if mac != recomputed_mac then ABORT
else return K
```

and

* `pqpk_B` is the receiver's KEM public key,
* `pqsk_B` is the receiver's KEM private key,
* `sctx` is context information for the given session of the protocol,
* `psk_ttl` specifies for how long the PSK should be considered valid, and
* `psk_handle` is a storage handle for the established PSK, designated by the responder.
  
The crate implements the protocol based on several different internal
KEMs:

* `MlKem768`, a lattice-based post-quantum KEM, in the process
 of being standardized by NIST
* `XWingKemDraft02`, a hybrid post-quantum KEM, combining `X25519`
 and `ML-KEM 768` based KEMs
* `Classic McEliece`, a code-based post-quantum KEM & Round 4
 candidate in the NIST PQ competition, available under feature
 `classic-mceliece` and implemented using the third-party crate
 [`classic-mceliece-rust`](https://crates.io/crates/classic-mceliece-rust).
* `X25519`, an elliptic-curve Diffie-Hellman KEM. ⚠️ This KEM *does
 not* provide post-quantum security and is included only for testing
 and benchmarking purposes under feature `test-utils`.

For `MlKem768`, `XWingKemDraft06`, and `X25519` we use `libcrux`'s
own optimized implementations.

[verified]: https://img.shields.io/badge/verified-brightgreen.svg?style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0idXRmLTgiPz48IS0tIFVwbG9hZGVkIHRvOiBTVkcgUmVwbywgd3d3LnN2Z3JlcG8uY29tLCBHZW5lcmF0b3I6IFNWRyBSZXBvIE1peGVyIFRvb2xzIC0tPg0KPHN2ZyB3aWR0aD0iODAwcHgiIGhlaWdodD0iODAwcHgiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4NCjxwYXRoIGQ9Ik05IDEyTDExIDE0TDE1IDkuOTk5OTlNMjAgMTJDMjAgMTYuNDYxMSAxNC41NCAxOS42OTM3IDEyLjY0MTQgMjAuNjgzQzEyLjQzNjEgMjAuNzkgMTIuMzMzNCAyMC44NDM1IDEyLjE5MSAyMC44NzEyQzEyLjA4IDIwLjg5MjggMTEuOTIgMjAuODkyOCAxMS44MDkgMjAuODcxMkMxMS42NjY2IDIwLjg0MzUgMTEuNTYzOSAyMC43OSAxMS4zNTg2IDIwLjY4M0M5LjQ1OTk2IDE5LjY5MzcgNCAxNi40NjExIDQgMTJWOC4yMTc1OUM0IDcuNDE4MDggNCA3LjAxODMzIDQuMTMwNzYgNi42NzQ3QzQuMjQ2MjcgNi4zNzExMyA0LjQzMzk4IDYuMTAwMjcgNC42Nzc2NiA1Ljg4NTUyQzQuOTUzNSA1LjY0MjQzIDUuMzI3OCA1LjUwMjA3IDYuMDc2NCA1LjIyMTM0TDExLjQzODIgMy4yMTA2N0MxMS42NDYxIDMuMTMyNzEgMTEuNzUgMy4wOTM3MyAxMS44NTcgMy4wNzgyN0MxMS45NTE4IDMuMDY0NTcgMTIuMDQ4MiAzLjA2NDU3IDEyLjE0MyAzLjA3ODI3QzEyLjI1IDMuMDkzNzMgMTIuMzUzOSAzLjEzMjcxIDEyLjU2MTggMy4yMTA2N0wxNy45MjM2IDUuMjIxMzRDMTguNjcyMiA1LjUwMjA3IDE5LjA0NjUgNS42NDI0MyAxOS4zMjIzIDUuODg1NTJDMTkuNTY2IDYuMTAwMjcgMTkuNzUzNyA2LjM3MTEzIDE5Ljg2OTIgNi42NzQ3QzIwIDcuMDE4MzMgMjAgNy40MTgwOCAyMCA4LjIxNzU5VjEyWiIgc3Ryb2tlPSIjMDAwMDAwIiBzdHJva2Utd2lkdGg9IjIiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ryb2tlLWxpbmVqb2luPSJyb3VuZCIvPg0KPC9zdmc+
[pre-verification]: https://img.shields.io/badge/pre_verification-orange.svg?style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0idXRmLTgiPz48IS0tIFVwbG9hZGVkIHRvOiBTVkcgUmVwbywgd3d3LnN2Z3JlcG8uY29tLCBHZW5lcmF0b3I6IFNWRyBSZXBvIE1peGVyIFRvb2xzIC0tPg0KPHN2ZyB3aWR0aD0iODAwcHgiIGhlaWdodD0iODAwcHgiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4NCjxwYXRoIGQ9Ik05IDEySDE1TTIwIDEyQzIwIDE2LjQ2MTEgMTQuNTQgMTkuNjkzNyAxMi42NDE0IDIwLjY4M0MxMi40MzYxIDIwLjc5IDEyLjMzMzQgMjAuODQzNSAxMi4xOTEgMjAuODcxMkMxMi4wOCAyMC44OTI4IDExLjkyIDIwLjg5MjggMTEuODA5IDIwLjg3MTJDMTEuNjY2NiAyMC44NDM1IDExLjU2MzkgMjAuNzkgMTEuMzU4NiAyMC42ODNDOS40NTk5NiAxOS42OTM3IDQgMTYuNDYxMSA0IDEyVjguMjE3NTlDNCA3LjQxODA4IDQgNy4wMTgzMyA0LjEzMDc2IDYuNjc0N0M0LjI0NjI3IDYuMzcxMTMgNC40MzM5OCA2LjEwMDI3IDQuNjc3NjYgNS44ODU1MkM0Ljk1MzUgNS42NDI0MyA1LjMyNzggNS41MDIwNyA2LjA3NjQgNS4yMjEzNEwxMS40MzgyIDMuMjEwNjdDMTEuNjQ2MSAzLjEzMjcxIDExLjc1IDMuMDkzNzMgMTEuODU3IDMuMDc4MjdDMTEuOTUxOCAzLjA2NDU3IDEyLjA0ODIgMy4wNjQ1NyAxMi4xNDMgMy4wNzgyN0MxMi4yNSAzLjA5MzczIDEyLjM1MzkgMy4xMzI3MSAxMi41NjE4IDMuMjEwNjdMMTcuOTIzNiA1LjIyMTM0QzE4LjY3MjIgNS41MDIwNyAxOS4wNDY1IDUuNjQyNDMgMTkuMzIyMyA1Ljg4NTUyQzE5LjU2NiA2LjEwMDI3IDE5Ljc1MzcgNi4zNzExMyAxOS44NjkyIDYuNjc0N0MyMCA3LjAxODMzIDIwIDcuNDE4MDggMjAgOC4yMTc1OVYxMloiIHN0cm9rZT0iIzAwMDAwMCIgc3Ryb2tlLXdpZHRoPSIyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiLz4NCjwvc3ZnPg==

