#!/usr/bin/env bash
#
# Reconfigure, rebuild, and profile one of the ML-KEM/ML-DSA benchmark
# binaries with `samply`, then open the recording in the Firefox Profiler
# (https://profiler.firefox.com), which renders it as a flamegraph among
# other views.
#
# Requires `samply` (https://github.com/mstange/samply):
#   cargo install samply
#
# Usage:
#   scripts/flamegraph.sh <binary> [benchmark_filter]
#
# Examples:
#   scripts/flamegraph.sh ml_kem_bench768
#   scripts/flamegraph.sh ml_kem_bench768 key_generation
#   scripts/flamegraph.sh ml_dsa_bench65 sign
#
# Set LIBCRUX_BENCHMARK_MIN_TIME to control how long the benchmark runs for
# (default: 5s), giving the profiler enough samples to work with.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
BUILD_DIR="${PROJECT_DIR}/build"
CONFIG="Release"
MIN_TIME="${LIBCRUX_BENCHMARK_MIN_TIME:-5s}"

if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <binary> [benchmark_filter]" >&2
    exit 1
fi

BINARY_NAME="$1"
FILTER="${2:-.}"

if ! command -v samply >/dev/null 2>&1; then
    echo "error: 'samply' not found. Install it with 'cargo install samply'." >&2
    echo "       (https://github.com/mstange/samply)" >&2
    exit 1
fi

# Single-config generators (plain Ninja/Makefiles with -DCMAKE_BUILD_TYPE=...)
# put the binary directly in build/; multi-config generators (Ninja Multi-
# Config, Xcode, Visual Studio -- the ones the README's build instructions
# use) put it in build/<Config>/.
find_binary() {
    if [[ -f "${BUILD_DIR}/${BINARY_NAME}" ]]; then
        echo "${BUILD_DIR}/${BINARY_NAME}"
    elif [[ -f "${BUILD_DIR}/${CONFIG}/${BINARY_NAME}" ]]; then
        echo "${BUILD_DIR}/${CONFIG}/${BINARY_NAME}"
    fi
}

# A pre-existing build/ configured with a different generator (e.g. plain
# Makefiles, or single-config Ninja) can't be reconfigured in place -- CMake
# errors out on a generator mismatch. Wipe it so we can switch cleanly.
if [[ -f "${BUILD_DIR}/CMakeCache.txt" ]] && ! grep -q '^CMAKE_GENERATOR:INTERNAL=Ninja Multi-Config$' "${BUILD_DIR}/CMakeCache.txt"; then
    echo "==> Removing ${BUILD_DIR} (configured with a different generator)" >&2
    rm -rf "${BUILD_DIR}"
fi

echo "==> Configuring and building ${BINARY_NAME} (${CONFIG}, LIBCRUX_BENCHMARKS=1)" >&2
# LIBCRUX_BENCHMARKS is read by CMakeLists.txt at configure time, so it must
# be set here too, not just for the build step below -- otherwise a
# pre-existing build/ configured without it would never gain the bench
# targets. Always reconfigure/rebuild so stale binaries never get profiled.
# Uses the same "Ninja Multi-Config" generator as the README's build
# instructions, so the binary lands in build/<Config>/.
LIBCRUX_BENCHMARKS=1 cmake -B "${BUILD_DIR}" -S "${PROJECT_DIR}" -G "Ninja Multi-Config"
LIBCRUX_BENCHMARKS=1 cmake --build "${BUILD_DIR}" --config "${CONFIG}" --target "${BINARY_NAME}"

BIN="$(find_binary)"
if [[ -z "${BIN}" || ! -x "${BIN}" ]]; then
    echo "error: ${BINARY_NAME} not found (looked in ${BUILD_DIR} and ${BUILD_DIR}/${CONFIG})" >&2
    exit 1
fi

echo "==> Recording with samply (opens profiler.firefox.com when done)" >&2
samply record -- "${BIN}" --benchmark_filter="${FILTER}" --benchmark_min_time="${MIN_TIME}"
