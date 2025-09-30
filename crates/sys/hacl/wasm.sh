# A helper script to build the sys crate for wasm and run tests for wasm.
# Note that this requires an emscripten toolchain to be present and in the
# path https://emscripten.org/.

#!/bin/bash

show_help() {
    echo "
    WASM helper for the HACL sys crate.
    The C code is built with emscripten to get a correct C ABI.
    Note however that this intended to be used with a wasm32-unknown-unknown
    target, not wasm32-unknown-emscripten.

    Usage: ./wasm.sh [--build|--test]
        --build     build for wasm
        --test      test with wasm for node
"
}

all_args=("$@")
while [ $# -gt 0 ]; do
    case "$1" in
    --build)
         CC=emcc AR=emar cargo build --target=wasm32-unknown-unknown
         exit 0
        ;;
    --test)
         CC=emcc AR=emar wasm-pack test --node
         exit 0
        ;;
    *)
        show_help
        exit 2
        ;;
    esac
    shift
done

show_help
exit 2
