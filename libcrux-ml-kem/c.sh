#!/usr/bin/env bash

set -e
set -o pipefail

if [[ -z "$CHARON_HOME" ]]; then
    echo "Please set CHARON_HOME to the Charon directory" 1>&2
    exit 1
fi
if [[ -z "$EURYDICE_HOME" ]]; then
    echo "Please set EURYDICE_HOME to the Eurydice directory" 1>&2
    exit 1
fi

portable_only=0
no_hacl=0
no_charon=0
clean=0

# Parse command line arguments.
all_args=("$@")
while [ $# -gt 0 ]; do
    case "$1" in
    -p | --portable) portable_only=1 ;;
    --no-hacl) no_hacl=1 ;;
    --no-charon) no_charon=1 ;;
    -c | --clean) clean=1 ;;
    esac
    shift
done

if [[ "$portable_only" = 1 ]]; then
    export LIBCRUX_DISABLE_SIMD256=1
    export LIBCRUX_DISABLE_SIMD128=1
fi

# TODO: add LIBCRUX_ENABLE_SIMD128=1 LIBCRUX_ENABLE_SIMD256=1 charon invocations
if [[ "$no_charon" = 0 ]]; then
    rm -rf ../libcrux_ml_kem.llbc ../libcrux_sha3.llbc
    echo "Running charon (sha3) ..."
    (cd ../libcrux-sha3 && RUSTFLAGS="--cfg eurydice" $CHARON_HOME/bin/charon --errors-as-warnings)
    if ! [[ -f ../libcrux_sha3.llbc ]]; then
      echo "😱😱😱 You are the victim of this bug: https://hacspec.zulipchat.com/#narrow/stream/433829-Circus/topic/charon.20declines.20to.20generate.20an.20llbc.20file"
      echo "Suggestion: rm -rf ../target or cargo clean"
      exit 1
    fi
    echo "Running charon (ml-kem) ..."
    RUSTFLAGS="--cfg eurydice" $CHARON_HOME/bin/charon --errors-as-warnings
else
    echo "Skipping charon"
fi

mkdir -p c
cd c

# Clean only when requesting it.
# Note that we can not extract for all platforms on any platform right now.
# Make sure to keep files from other platforms.
if [[ "$clean" = 1 ]]; then
    rm -rf *.c *.h
    rm -rf internal/*.h
fi

echo "Running eurydice ..."
$EURYDICE_HOME/eurydice --config ../c.yaml ../../libcrux_ml_kem.llbc ../../libcrux_sha3.llbc
cp $EURYDICE_HOME/include/eurydice_glue.h .

clang-format --style=Google -i *.c *.h
clang-format --style=Google -i internal/*.h
clang-format --style=Google -i intrinsics/*.h

# Write out infos about the used tools
[[ -z "$CHARON_REV" && -d $CHARON_HOME/.git ]] && export CHARON_REV=$(git -C $CHARON_HOME rev-parse HEAD)
[[ -z "$EURYDICE_REV" && -d $EURYDICE_HOME/.git ]] && export EURYDICE_REV=$(git -C $EURYDICE_HOME rev-parse HEAD)
[[ -z "$KRML_REV" && -d $KRML_HOME/.git ]] && export KRML_REV=$(git -C $KRML_HOME rev-parse HEAD)
[[ -z "$FSTAR_REV" && -d $FSTAR_HOME/.git ]] && export FSTAR_REV=$(git -C $FSTAR_HOME rev-parse HEAD)
rm -f code_gen.txt
echo "This code was generated with the following tools:" >> code_gen.txt
echo -n "Charon: " >> code_gen.txt
echo "$CHARON_REV" >> code_gen.txt
echo -n "Eurydice: " >> code_gen.txt
echo "$EURYDICE_REV" >> code_gen.txt
echo -n "Karamel: " >> code_gen.txt
echo "$KRML_REV" >> code_gen.txt
echo -n "F*: " >> code_gen.txt
echo "$FSTAR_REV" >> code_gen.txt
