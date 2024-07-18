#!/bin/bash

set -e

SED=$(which gsed &>/dev/null && echo gsed || echo sed)

# Extract the C code
# cargo clean
./c.sh --config cg.yaml --out cg --mlkem768 \
    --no-glue --no-unrolling --no-karamel_include --no-karamel_include

clang-format --style=Google -i cg/*.h

if [[ -n "$BORINGSSL_HOME" ]]; then
    echo "Copying the files into $BORINGSSL_HOME/third_party/libcrux/"

    cp cg/*.h $BORINGSSL_HOME/third_party/libcrux/
    cp cg/code_gen.txt $BORINGSSL_HOME/third_party/libcrux/
    cp -r cg/karamel $BORINGSSL_HOME/third_party/libcrux/
    cp -r cg/intrinsics $BORINGSSL_HOME/third_party/libcrux/
    libcrux_rev=$(git rev-parse HEAD)
    echo "libcrux: $libcrux_rev" >> $BORINGSSL_HOME/third_party/libcrux/code_gen.txt
fi
