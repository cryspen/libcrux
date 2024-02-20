0. To run the `generate_shake128_kats_hash.py` script you'll need [PyPy](https://www.pypy.org/).

1. Install dependencies using `pip install -r requirements. txt`.

2. Generate the JSON KAT files for all parameter sets using `./generate_nist_kats.py`.

3. Generate the SHAKE128 hash of 100 SHAKE128-RNG KATs for all parameter sets using `./generate_shake128_kats_hash.py --kat-rounds=100`.
