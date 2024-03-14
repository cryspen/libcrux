#!/usr/bin/env bash

set -e

SCRIPTPATH="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
cd "$SCRIPTPATH"

DENYLIST="Makefile Kyber.fst.config.json PROOFS.md"

# `prepare_folder SRC DEST` copies F* files from SRC to DEST/<basename SRC>
prepare_folder() {
    original="$1"
    workdir="$2"
    find "$original" \( -name '*.fst' -o -name '*.fsti' \) -exec cp --parents \{\} "$workdir" \;
}

# `patch_folder ORIGINAL DESTINATION PATCH` creates the folder
# `DESTINATION` out of the folder `ORIGINAL` given the patch `PATCH`
patch_folder() {
    original="$1"
    destination="$2"
    patch="$3"
    TEMPDIR=$(mktemp -d)
    
    prepare_folder $original "$TEMPDIR"
    
    original_basename=$(basename "$original")
    patch --directory="$TEMPDIR/$original_basename" -s -p1 < "$patch" || {
        cd "$TEMPDIR/$original_basename"
        echo '::error::Patches don'"'"'t apply. Keep in mind the CI regenerates `extraction` using the latest hax on `main`.'
        for rejection in *.rej; do
            echo "::group::cat $rejection"
            cat "$rejection"
            echo '::endgroup::'
        done
        exit 1
    }
    
    DIR="$TEMPDIR/$original_basename"
    cp -rfT "$DIR" "$destination"

    rm -rf "$TEMPDIR"
}

case $1 in
    apply)
        for target in extraction-edited extraction-secret-independent; do
            find "$target" \
                 \( -name '*.fst' -o -name '*.fsti' \) \
                 -type f \
                 -exec rm -f {} +
        done

        patch_folder extraction extraction-edited \
                     extraction-edited.patch
        patch_folder extraction-edited extraction-secret-independent \
                     extraction-secret-independent.patch
        ;;

    create)
        TEMPDIR=$(mktemp -d)

        for i in extraction extraction-edited extraction-secret-independent; do
            prepare_folder "$i" "$TEMPDIR"
        done

        (
            cd "$TEMPDIR"
            diff -ruN extraction extraction-edited > extraction-edited.patch || true
            diff -ruN extraction-edited extraction-secret-independent > extraction-secret-independent.patch || true

            
        )
        mv "$TEMPDIR/extraction-edited.patch" extraction-edited.patch
        mv "$TEMPDIR/extraction-secret-independent.patch" extraction-secret-independent.patch
        
        rm -rf "$TEMPDIR"
        ;;
    
    *)
        echo 'Usage: `'"$0"' COMMAND`'
        echo '  - `'"$0"' apply`: recreate `extraction-*` folders from the `*.patch` files'
        echo '  - `'"$0"' create`: recreate `*.patch` files from the `extraction-*` folders'
        ;;
esac
