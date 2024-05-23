#! /usr/bin/env python3

from dilithium import Dilithium2, Dilithium3, Dilithium5
from aes256_ctr_drbg import AES256_CTR_DRBG

import json
import hashlib


def generate_matrix_A_sampling_KATs():
    algorithm = Dilithium3

    for i in range(1):
        pk, sk = algorithm.keygen()
        print([x for x in algorithm.A_rejection_sampling_seed])
        print([x for x in algorithm.A_sampled_ring_element])


def generate_nistkats():
    for algorithm in [Dilithium2, Dilithium3, Dilithium5]:
        kats_formatted = []

        entropy_input = bytes([i for i in range(48)])
        rng = AES256_CTR_DRBG(entropy_input)

        print("Generating KATs for ML-DSA-{}{}.".format(algorithm.k, algorithm.l))

        for i in range(100):
            seed = rng.random_bytes(48)

            algorithm.set_drbg_seed(seed)

            pk, sk = algorithm.keygen()

            msg_len = 33 * (i + 1)
            msg = rng.random_bytes(msg_len)
            sig = algorithm.sign(sk, msg)

            kats_formatted.append(
                {
                    "key_generation_seed": bytes(algorithm.keygen_seed).hex(),
                    "sha3_256_hash_of_public_key": bytes(
                        hashlib.sha3_256(pk).digest()
                    ).hex(),
                    "sha3_256_hash_of_secret_key": bytes(
                        hashlib.sha3_256(sk).digest()
                    ).hex(),
                    "message": bytes(msg).hex(),
                    "sha3_256_hash_of_signature": bytes(
                        hashlib.sha3_256(sig).digest()
                    ).hex(),
                }
            )

            with open("nistkats-{}{}.json".format(algorithm.k, algorithm.l), "w") as f:
                json.dump(kats_formatted, f, ensure_ascii=False, indent=4)


# generate_matrix_A_sampling_KATs()
generate_nistkats()
