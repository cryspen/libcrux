#! /usr/bin/env pypy3

from kyber import *
import Crypto
from tqdm import tqdm
import argparse


class RNG:
    def __init__(self):
        self.shake = SHAKE128.new()
        self.shake.update(b"")

    def read(self, length):
        return self.shake.read(length)


parser = argparse.ArgumentParser()
parser.add_argument(
    "--kat-rounds",
    required=True,
    help="Number of consecutive rounds of KATs to hash.",
    type=int,
)
args = parser.parse_args()

for params in [params512, params768, params1024]:
    kats_formatted = []
    rng = RNG()
    kat_hasher = SHAKE128.new()

    if params == params512:
        params_string = "Kyber512"
        ciphertext_size = 768
    elif params == params768:
        params_string = "Kyber768"
        ciphertext_size = 1088
    elif params == params1024:
        params_string = "Kyber1024"
        ciphertext_size = 1568

    print(
        "{}: Generating SHAKE-128 32-byte hash using {} sets of KATs.".format(
            params_string, args.kat_rounds
        )
    )

    for i in tqdm(range(args.kat_rounds)):
        kseed = rng.read(64)
        eseed = rng.read(32)

        ek, dk = KeyGen(kseed, params)

        ct, ss = Enc(ek, eseed, params)

        random_ct = rng.read(ciphertext_size)
        ss_fail = Dec(dk, random_ct, params)

        kat_hasher.update(ek)
        kat_hasher.update(dk)
        kat_hasher.update(ct)
        kat_hasher.update(ss)
        kat_hasher.update(ss_fail)

    print(bytes(kat_hasher.read(32)).hex())
