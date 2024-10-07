# Post-Quantum Pre-Shared-Key Protocol (PSQ) #

![pre-verification]

This crate implements a protocol for establishing and mutually
registering a pre-shared key such that the protocol messages are
secure against harvest-now-decrypt-later (HNDL) passive quantum
attackers.

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
* `X25519`, an elliptic-curve Diffie-Hellman KEM (not post-quantum
 secure; for performance comparison)
* `ML-KEM 768`, a lattice-based post-quantum KEM, in the process
 of being standardized by NIST
* `Classic McEliece`, a code-based post-quantum KEM & Round 4
 candidate in the NIST PQ competition,
* `XWingKemDraft02`, a hybrid post-quantum KEM, combining `X25519`
 and `ML-KEM 768` based KEMs

For x25519 and ML-KEM, we use `libcrux`'s optimized implementations,
the Classic McEliece-based protocol uses crate
[`classic-mceliece-rust`](https://crates.io/crates/classic-mceliece-rust).


[verified]: https://img.shields.io/badge/verified-brightgreen.svg?style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0idXRmLTgiPz48IS0tIFVwbG9hZGVkIHRvOiBTVkcgUmVwbywgd3d3LnN2Z3JlcG8uY29tLCBHZW5lcmF0b3I6IFNWRyBSZXBvIE1peGVyIFRvb2xzIC0tPg0KPHN2ZyB3aWR0aD0iODAwcHgiIGhlaWdodD0iODAwcHgiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4NCjxwYXRoIGQ9Ik05IDEyTDExIDE0TDE1IDkuOTk5OTlNMjAgMTJDMjAgMTYuNDYxMSAxNC41NCAxOS42OTM3IDEyLjY0MTQgMjAuNjgzQzEyLjQzNjEgMjAuNzkgMTIuMzMzNCAyMC44NDM1IDEyLjE5MSAyMC44NzEyQzEyLjA4IDIwLjg5MjggMTEuOTIgMjAuODkyOCAxMS44MDkgMjAuODcxMkMxMS42NjY2IDIwLjg0MzUgMTEuNTYzOSAyMC43OSAxMS4zNTg2IDIwLjY4M0M5LjQ1OTk2IDE5LjY5MzcgNCAxNi40NjExIDQgMTJWOC4yMTc1OUM0IDcuNDE4MDggNCA3LjAxODMzIDQuMTMwNzYgNi42NzQ3QzQuMjQ2MjcgNi4zNzExMyA0LjQzMzk4IDYuMTAwMjcgNC42Nzc2NiA1Ljg4NTUyQzQuOTUzNSA1LjY0MjQzIDUuMzI3OCA1LjUwMjA3IDYuMDc2NCA1LjIyMTM0TDExLjQzODIgMy4yMTA2N0MxMS42NDYxIDMuMTMyNzEgMTEuNzUgMy4wOTM3MyAxMS44NTcgMy4wNzgyN0MxMS45NTE4IDMuMDY0NTcgMTIuMDQ4MiAzLjA2NDU3IDEyLjE0MyAzLjA3ODI3QzEyLjI1IDMuMDkzNzMgMTIuMzUzOSAzLjEzMjcxIDEyLjU2MTggMy4yMTA2N0wxNy45MjM2IDUuMjIxMzRDMTguNjcyMiA1LjUwMjA3IDE5LjA0NjUgNS42NDI0MyAxOS4zMjIzIDUuODg1NTJDMTkuNTY2IDYuMTAwMjcgMTkuNzUzNyA2LjM3MTEzIDE5Ljg2OTIgNi42NzQ3QzIwIDcuMDE4MzMgMjAgNy40MTgwOCAyMCA4LjIxNzU5VjEyWiIgc3Ryb2tlPSIjMDAwMDAwIiBzdHJva2Utd2lkdGg9IjIiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ryb2tlLWxpbmVqb2luPSJyb3VuZCIvPg0KPC9zdmc+
[pre-verification]: https://img.shields.io/badge/pre_verification-orange.svg?style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0idXRmLTgiPz48IS0tIFVwbG9hZGVkIHRvOiBTVkcgUmVwbywgd3d3LnN2Z3JlcG8uY29tLCBHZW5lcmF0b3I6IFNWRyBSZXBvIE1peGVyIFRvb2xzIC0tPg0KPHN2ZyB3aWR0aD0iODAwcHgiIGhlaWdodD0iODAwcHgiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4NCjxwYXRoIGQ9Ik05IDEySDE1TTIwIDEyQzIwIDE2LjQ2MTEgMTQuNTQgMTkuNjkzNyAxMi42NDE0IDIwLjY4M0MxMi40MzYxIDIwLjc5IDEyLjMzMzQgMjAuODQzNSAxMi4xOTEgMjAuODcxMkMxMi4wOCAyMC44OTI4IDExLjkyIDIwLjg5MjggMTEuODA5IDIwLjg3MTJDMTEuNjY2NiAyMC44NDM1IDExLjU2MzkgMjAuNzkgMTEuMzU4NiAyMC42ODNDOS40NTk5NiAxOS42OTM3IDQgMTYuNDYxMSA0IDEyVjguMjE3NTlDNCA3LjQxODA4IDQgNy4wMTgzMyA0LjEzMDc2IDYuNjc0N0M0LjI0NjI3IDYuMzcxMTMgNC40MzM5OCA2LjEwMDI3IDQuNjc3NjYgNS44ODU1MkM0Ljk1MzUgNS42NDI0MyA1LjMyNzggNS41MDIwNyA2LjA3NjQgNS4yMjEzNEwxMS40MzgyIDMuMjEwNjdDMTEuNjQ2MSAzLjEzMjcxIDExLjc1IDMuMDkzNzMgMTEuODU3IDMuMDc4MjdDMTEuOTUxOCAzLjA2NDU3IDEyLjA0ODIgMy4wNjQ1NyAxMi4xNDMgMy4wNzgyN0MxMi4yNSAzLjA5MzczIDEyLjM1MzkgMy4xMzI3MSAxMi41NjE4IDMuMjEwNjdMMTcuOTIzNiA1LjIyMTM0QzE4LjY3MjIgNS41MDIwNyAxOS4wNDY1IDUuNjQyNDMgMTkuMzIyMyA1Ljg4NTUyQzE5LjU2NiA2LjEwMDI3IDE5Ljc1MzcgNi4zNzExMyAxOS44NjkyIDYuNjc0N0MyMCA3LjAxODMzIDIwIDcuNDE4MDggMjAgOC4yMTc1OVYxMloiIHN0cm9rZT0iIzAwMDAwMCIgc3Ryb2tlLXdpZHRoPSIyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiLz4NCjwvc3ZnPg==

