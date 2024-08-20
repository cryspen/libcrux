# Post-Quantum Pre-Shared-Key Protocol (PSQ) #

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

