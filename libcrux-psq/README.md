# Post-Quantum Pre-Shared-Key Protocol (PSQ) #

This crate implements a protocol for agreeing on a pre-shared key such
that the protocol messages are secure against
harvest-now-decrypt-later (HNDL) passive quantum attackers.

The protocol between initator `A` and receiver `B` roughly works as follows:
```
A:  (ik, enc) <- PQ-KEM(pk_B)
    K_0 <- KDF(ik, pk_B || enc || sctxt)
    K_m <- KDF(K_0, "Confirmation")
    K <- KDF(K_0, "PSK")
    mac_ttl <- MAC(K_m, psk_ttl)
A -> B: (enc, psk_ttl, mac_ttl)
```
Where 
* `pk_B` is the receiver's KEM public key, 
* `sctx` is context information for the given session of the protocol,
* `psk_ttl` specifies for how long the PSK should be considered valid, and
* `K` is the final PSK that is derived from the decapsulated shared
  secret based on the internal KEM.
  
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
