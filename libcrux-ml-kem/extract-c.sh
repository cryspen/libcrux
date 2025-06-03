#!/bin/bash

# C
./c.sh --config cg.yaml --mlkem768 --no-glue --no-unrolling --no-karamel_include \
    --out c

# C++
./c.sh --config cg.yaml --mlkem768 --no-glue --no-unrolling --no-karamel_include \
    --cpp17 --out cg
