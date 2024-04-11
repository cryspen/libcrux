rm -rf c

if [[ -z "$CHARON_HOME" ]]; then
    echo "Please set CHARON_HOME to the Charon directory" 1>&2
    exit 1
fi
if [[ -z "$EURYDICE_HOME" ]]; then
    echo "Please set EURYDICE_HOME to the Eurydice directory" 1>&2
    exit 1
fi

echo "Running charon ..."
$CHARON_HOME/bin/charon --errors-as-warnings
mkdir -p c
cd c

echo "Running eurydice ..."
$EURYDICE_HOME/eurydice --config ../c.yaml ../libcrux_kyber.llbc
cp $EURYDICE_HOME/include/eurydice_glue.h .

if [[ -n "$HACL_PACKAGES_HOME" ]]; then
    clang-format --style=Mozilla -i libcrux_kyber.c libcrux_kyber.h
    cp internal/*.h $HACL_PACKAGES_HOME/libcrux/include/internal/
    cp *.h $HACL_PACKAGES_HOME/libcrux/include
    cp *.c $HACL_PACKAGES_HOME/libcrux/src
else
    echo "Please set HACL_PACKAGES_HOME to the hacl-packages directory to copy the code over" 1>&2
fi
