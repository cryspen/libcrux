# Linting for PQC

Lining pqc public keys.

## Lints


| Lint                           | ID              | Name                               | S?     | Implementation | Description                                                                                                                                  |
|--------------------------------|-----------------|------------------------------------|--------|--------------------|----------------------------------------------------------------------------------------------------------------------------------------------|
| Correct key usage              | ML_DSA_INTER_01 | e_ml_dsa_key_usage                 |        | In Java            | A certificate with an ML-DSA public key must have only one or more of the following key usage values: digitalSignature, nonRepudiation, keyCertSign, cRLSign.                                                |
| Correct PK aid encoding        | ML_DSA_INTER_02 | e_ml_dsa_public_key_aid_encoding   |        | In Java | The algorithm identifier in the public key of a certificate with an ML-DSA public key must have the correct encoding.                        |
| Correct signature aid encoding | ML_DSA_INTER_03 | e_ml_dsa_signature_aid_encoding    |        | In Java | The algorithm identifier in the signature of a certificate signed by an ML-DSA public key must have the correct encoding.                    |
|                                | ML_DSA_DIM_01   | e_ml_dsa_pk_length                 |        |         | An encoded ML-DSA public key must be of the correct length.                                                                            |
|                                | ML_DSA_DIM_02   | e_ml_dsa_pk_seed_length            | Y      |        | The seed contained in the extracted public key must be of the correct length.                                                             |
|                                | ML_DSA_DIM_03   | e_ml_dsa_pk_vector_dimension       | Y    |         | The vector contained in the extracted ML-DSA public key must have the correct dimension.                     |
|                                | ML_DSA_DIM_04   | e_ml_dsa_pk_matrix_dimension       | Y   |         | The matrix expanded from the seed, that is contained in the extracted ML-DSA public key, must have the correct dimensions.                                         |
|                                | ML_DSA_DOM_01   | e_ml_dsa_pk_matrix_entries         | Y     |         | The matrix expanded from the seed, that is contained in the extracted ML-DSA public key, must have entries from the correct space.            |
|                                | ML_DSA_DOM_02   | e_ml_dsa_pk_vector                 | Y           |         | The vector contained in the extracted ML-DSA public key, must have entries from the correct space.                                |
|                                | ML_DSA_DIS_01   | e_ml_dsa_pk_seed_entry_frequency   |   |         | The seed contained in the extracted ML-DSA public key must not have too many occurrences of the same element.                                   |
|                                | ML_DSA_DIS_02   | e_ml_dsa_pk_seed_entry_run         |         |        | The seed contained in the extracted ML-DSA public key must not have a too long run of the same element.                                         |
|                                | ML_DSA_DIS_03   | e_ml_dsa_pk_matrix_entry_frequency |  |        | The matrix expanded from the seed, that is contained in the extracted ML-DSA public key must not have too many occurrences of the same element.                                            |
|                                | ML_DSA_DIS_04   | e_ml_dsa_pk_matrix_entry_run       |       |        | The matrix expanded from the seed, that is contained in the extracted ML-DSA public key must not have a too long run of the same element. |
|                                | ML_DSA_DIS_05   | e_ml_dsa_pk_matrix_sl_entries      |      |        | The matrix expanded from the seed, that is contained in the extracted ML-DSA public key must not have too small or too large entries.      |
| Known encoded public key       | GEN_01   | e_known_encoded_key |                | In Java | A public key whose corresponding private key is known to be compromised, is weak, or is leaked must not be placed in a certificate.          |

