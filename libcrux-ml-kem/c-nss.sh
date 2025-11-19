#!/usr/bin/env bash

set -e
set -o pipefail

./c.sh --mlkem768

if [[ -n "$NSS_HOME" ]]; then
    files=(libcrux_core.c libcrux_core.h libcrux_mlkem768.h libcrux_mlkem768_portable.c libcrux_mlkem768_portable.h libcrux_mlkem_portable.c libcrux_mlkem_portable.h libcrux_sha3.h libcrux_sha3_internal.h)
    echo "copying ..."
    for file in "${files[@]}"; do
        echo "  c/$file"
        cp c/$file $NSS_HOME/lib/freebl/verified/
    done
    
    internal_files=(libcrux_core.h  libcrux_mlkem_portable.h libcrux_sha3_internal.h)
    for file in "${internal_files[@]}"; do
        echo "  c/internal/$file"
        cp c/internal/$file $NSS_HOME/lib/freebl/verified/internal/
    done
fi
