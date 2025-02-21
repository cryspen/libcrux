#!/bin/bash

set -e

# Extract
sudo docker pull ghcr.io/cryspen/libcrux-c:unstable
sudo docker run -v $PWD:/home/user/libcrux \
    --rm ghcr.io/cryspen/libcrux-c:unstable bash \
    -c "cd libcrux/libcrux-ml-kem && ./boring.sh && cargo clean && ./c.sh && cd ../libcrux-ml-dsa && ./boring.sh"

# Build & test
cd libcrux-ml-kem/c
LIBCRUX_BENCHMARKS=1 CC=clang-18 CXX=clang++-18 cmake -B build -G "Ninja Multi-Config"
cmake --build build
./build/Debug/ml_kem_test

cd ../cg
LIBCRUX_BENCHMARKS=1 CC=clang-18 CXX=clang++-18 cmake -B build -G "Ninja Multi-Config"
cmake --build build
./build/Debug/ml_kem_test

cd ../../libcrux-ml-dsa/cg
CC=clang-18 CXX=clang++-18 cmake -B build -G "Ninja Multi-Config"
cmake --build build
./build/Debug/ml_dsa_test
