# cmake -B build -G "Ninja Multi-Config"
# cmake --build build
# # For release (benchmarks)
# cmake --build build --config Release

cmake_minimum_required(VERSION 3.10)

project(libcrux-ml-kem
    VERSION 0.1.0
    LANGUAGES C CXX
)

set(CMAKE_C_STANDARD 11)
add_compile_options(
    -Wall
    # -Wextra
    # -pedantic
    # -Wconversion
    # -Wsign-conversion
    $<$<CONFIG:DEBUG>:-g>
    $<$<CONFIG:DEBUG>:-Og>
    $<$<CONFIG:RELEASE>:-g>
    $<$<CONFIG:RELEASE>:-O3>
    -fno-omit-frame-pointer
    -flto
)
add_link_options(-flto)
set(CMAKE_COLOR_DIAGNOSTICS "ON")
include_directories(
    ${PROJECT_SOURCE_DIR}
    ${PROJECT_SOURCE_DIR}/internal
    ${PROJECT_SOURCE_DIR}/karamel/include
)
file(GLOB SOURCES
    ${PROJECT_SOURCE_DIR}/libcrux_core.c
    ${PROJECT_SOURCE_DIR}/libcrux_platform.c
    ${PROJECT_SOURCE_DIR}/libcrux_mlkem512.c
    ${PROJECT_SOURCE_DIR}/libcrux_mlkem768.c
    ${PROJECT_SOURCE_DIR}/libcrux_mlkem1024.c
    ${PROJECT_SOURCE_DIR}/libcrux_polynomial.c
)
# file(GLOB VEC128_SOURCES
#     libcrux_sha3_neon.c
# )
file(GLOB SOURCES_vec256
    ${PROJECT_SOURCE_DIR}/libcrux_mlkem_avx2.c
    ${PROJECT_SOURCE_DIR}/libcrux_sha3_avx2.c
)

# set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)

if(${CMAKE_SYSTEM_NAME} MATCHES Linux)
    add_compile_options(
        -fPIC
    )
endif(${CMAKE_SYSTEM_NAME} MATCHES Linux)

add_library(ml_kem SHARED ${SOURCES})
add_library(ml_kem_static STATIC ${SOURCES})

# if(LIBCRUX_VEC256)
add_library(ml_kem_vec256 OBJECT ${SOURCES_vec256})
target_sources(ml_kem_static PRIVATE $<TARGET_OBJECTS:ml_kem_vec256>)
target_sources(ml_kem PRIVATE $<TARGET_OBJECTS:ml_kem_vec256>)
target_compile_options(ml_kem_vec256 PRIVATE
    -mavx
    -mavx2
)
# endif()

# --- Tests

# Get gtests
include(FetchContent)
FetchContent_Declare(googletest
DOWNLOAD_EXTRACT_TIMESTAMP TRUE
    URL https://github.com/google/googletest/archive/refs/tags/release-1.11.0.zip
)

# For Windows: Prevent overriding the parent project's compiler/linker settings
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

# Get nlohmann json
FetchContent_Declare(json
DOWNLOAD_EXTRACT_TIMESTAMP TRUE
    URL https://github.com/nlohmann/json/archive/refs/tags/v3.10.3.zip
)
FetchContent_MakeAvailable(json)

add_executable(ml_kem_test
    ${PROJECT_SOURCE_DIR}/tests/mlkem768.cc
)
target_link_libraries(ml_kem_test PRIVATE
    ml_kem_static
    gtest_main
    nlohmann_json::nlohmann_json
)

add_executable(sha3_test
    ${PROJECT_SOURCE_DIR}/tests/sha3.cc
)
target_link_libraries(sha3_test PRIVATE
    ml_kem_static
    gtest_main
    nlohmann_json::nlohmann_json
)

# --- Benchmarks

FetchContent_Populate(benchmark
    GIT_REPOSITORY  https://github.com/google/benchmark.git
    # The latest release 1.7.1 is broken due to https://github.com/google/benchmark/pull/1517
    # But also: need the fix for https://github.com/google/benchmark/pull/1669
    GIT_TAG         bc946b919cac6f25a199a526da571638cfde109f
)
add_subdirectory(${benchmark_SOURCE_DIR} ${benchmark_BINARY_DIR})

add_executable(ml_kem_bench
    ${PROJECT_SOURCE_DIR}/benches/mlkem768.cc
)
target_link_libraries(ml_kem_bench PRIVATE
    ml_kem_static
    benchmark::benchmark
)
target_compile_definitions(ml_kem_bench PUBLIC HACL_CAN_COMPILE_VEC256)
target_compile_options(ml_kem_bench PRIVATE
    -mavx
    -mavx2
)

add_executable(ml_kem_keygen
    ${PROJECT_SOURCE_DIR}/benches/mlkem768_keygen.cc
)
target_link_libraries(ml_kem_keygen PRIVATE
    ml_kem_static
    benchmark::benchmark
)
target_compile_definitions(ml_kem_keygen PUBLIC HACL_CAN_COMPILE_VEC256)
target_compile_options(ml_kem_keygen PRIVATE
    -mavx
    -mavx2
)

add_executable(ml_kem_encaps
    ${PROJECT_SOURCE_DIR}/benches/mlkem768_encaps.cc
)
target_link_libraries(ml_kem_encaps PRIVATE
    ml_kem_static
    benchmark::benchmark
)
target_compile_definitions(ml_kem_encaps PUBLIC HACL_CAN_COMPILE_VEC256)
target_compile_options(ml_kem_encaps PRIVATE
    -mavx
    -mavx2
)

add_executable(sha3_bench
    ${PROJECT_SOURCE_DIR}/benches/sha3.cc
)
target_link_libraries(sha3_bench PRIVATE
    ml_kem_static
    benchmark::benchmark
)
target_compile_definitions(sha3_bench PUBLIC HACL_CAN_COMPILE_VEC256)
target_compile_options(sha3_bench PRIVATE
    -mavx
    -mavx2
)