# Linting for PQC

Lining pqc public keys.

## ML-KEM

| Lint                 | Name       | Implementation  |
| -------------------- | ---------- | --------------- |
| Empty parameters     | ML_KEM_001 | only in certs   |
| Key usage            | ML_KEM_002 | only in certs   |
| Correct aid encoding | ML_KEM_003 | only in certs   |
| Correct ek length    | ML_KEM_004 | Enforced by API |
