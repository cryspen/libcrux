#!/bin/bash

set -e

SED=$(which gsed &>/dev/null && echo gsed || echo sed)

no_clean=0

# Parse command line arguments.
all_args=("$@")
while [ $# -gt 0 ]; do
    case "$1" in
    --no-clean) no_clean=1 ;;
    esac
    shift
done

# Extract the C code
if [[ "$no_clean" = 0 ]]; then
    cargo clean
fi
./c.sh --config cg.yaml --out cg --mlkem768 --kyber768 \
    --no-glue --no-unrolling --no-karamel_include --no-karamel_include

clang-format-18 --style=Google -i cg/*.h

if [[ -n "$BORINGSSL_HOME" ]]; then
    echo "Copying the files into $BORINGSSL_HOME/third_party/libcrux/"

    cp cg/*.h $BORINGSSL_HOME/third_party/libcrux/
    cp cg/code_gen.txt $BORINGSSL_HOME/third_party/libcrux/
    cp -r cg/karamel $BORINGSSL_HOME/third_party/libcrux/
    cp -r cg/intrinsics $BORINGSSL_HOME/third_party/libcrux/
    libcrux_rev=$(git rev-parse HEAD)
    echo "libcrux: $libcrux_rev" >> $BORINGSSL_HOME/third_party/libcrux/code_gen.txt
fi
