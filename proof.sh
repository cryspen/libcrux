#!/bin/bash
# Helper for proofs.

# Usage info
show_help() {
    echo "Usage: ./proof.sh [extract]"
}

extract_all() {
    cargo hax into -i '-** +kem::kyber::** -kem::kyber::arithmetic::mutable_operations::**' fstar
    cd specs/kyber
    cargo hax into fstar
}

# Parse command line arguments.
all_args=("$@")
while [ $# -gt 0 ]; do
    case "$1" in
    extract)
        extract_all
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
