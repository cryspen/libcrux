# Linting for PQC

Lining pqc public keys.

## ML-KEM

| Lint                      | Name       | Implementation                               |
| ------------------------- | ---------- | -------------------------------------------- |
| Empty parameters          | ML_KEM_001 | only in certs                                |
| Key usage                 | ML_KEM_002 | only in certs                                |
| Correct aid encoding      | ML_KEM_003 | only in certs                                |
| Correct ek length         | ML_KEM_004 | Enforced by API                              |
| Correct seed length       | ML_KEM_005 | Enforced by API (as part of ML_KEM_004)      |
| Correct matrix dimensions | ML_KEM_006 | Implied                                      |
| Valid public key space    | ML_KEM_007 | Checked by `validate_public_key` or `decode` |
| Correct vector            | ML_KEM_008 | Implied                                      |
| Correct matrix entries    | ML_KEM_009 | Implied                                      |
| Correct matrix entries    | ML_KEM_010 | Implied                                      |
| Pk seed non-zero          | ML_KEM_011 | Checked by `validate_public_key` or `decode` |
