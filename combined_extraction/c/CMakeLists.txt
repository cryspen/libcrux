# cmake -B build -G "Ninja Multi-Config"
# cmake --build build
# # For release (benchmarks)
# cmake --build build --config Release

cmake_minimum_required(VERSION 3.10..4.0)

project(libcrux-ml-dsa
    VERSION 0.1.0
    LANGUAGES C CXX
)

set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 20) # C++20 for the split-source (non-header-only) variant

# Get gtests
include(FetchContent)
FetchContent_Declare(googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.16.0
)

# For Windows: Prevent overriding the parent project's compiler/linker settings
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

# Get nlohmann json
FetchContent_Declare(json
    GIT_REPOSITORY https://github.com/nlohmann/json.git
    GIT_TAG v3.11.3
)
FetchContent_MakeAvailable(json)

if(NOT MSVC)
    add_compile_options(
        -Wall
        -fstack-usage
        -Wno-unused-variable
        -fdiagnostics-color=always
        -pedantic
        $<$<CONFIG:DEBUG>:-g>
        $<$<CONFIG:DEBUG>:-Og>
        $<$<CONFIG:RELEASE>:-g>
        $<$<CONFIG:RELEASE>:-O3>
    )
endif(NOT MSVC)

option(ENABLE_SANITIZERS "Enable ASan and UBSan" OFF)
if(ENABLE_SANITIZERS)
    if(CMAKE_C_COMPILER_ID MATCHES "GNU|Clang" OR CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
        # Compile flags: Enable ASan + UBSan and keep frame pointers for good stack traces
        add_compile_options(-fsanitize=address,undefined -fno-omit-frame-pointer)
        # Link flags: Ensure the sanitizer runtime libraries are linked
        add_link_options(-fsanitize=address,undefined)
        message(STATUS "Sanitizers (ASan + UBSan) ENABLED")
    elseif(MSVC)
        # MSVC natively supports ASan (UBSan requires clang-cl)
        add_compile_options(/fsanitize=address)
        message(STATUS "AddressSanitizer ENABLED (MSVC)")
    endif()
endif()

if((CMAKE_C_COMPILER_ID STREQUAL "Clang" AND
    CMAKE_C_COMPILER_VERSION VERSION_GREATER_EQUAL "13.0.0") OR
    (CMAKE_C_COMPILER_ID STREQUAL "AppleClang" AND
    CMAKE_C_COMPILER_VERSION VERSION_GREATER_EQUAL "13.1.6"))
    add_compile_options(
        -Werror
        # KRML_MUSTINLINE expands to `inline __attribute__((always_inline))`,
        # which has external linkage, but some of these functions call
        # internal-linkage `static inline` glue functions (e.g. in the
        # glue code). That violates C11 6.7.4p3, but works today because the
        # header declarations of these functions aren't themselves marked
        # `inline` (adding that would likely cause linker errors). Only
        # clang warns about it, not gcc.
        -Wno-static-in-inline
        # Eurydice emits some functions that end up unused in a given build
        # configuration.
        -Wno-unused-function
    )
endif()

set(CMAKE_COLOR_DIAGNOSTICS "ON")
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)
include_directories(
  ${PROJECT_SOURCE_DIR}
  ${PROJECT_SOURCE_DIR}/internal
  ${PROJECT_SOURCE_DIR}/karamel
)
file(GLOB SOURCES
  ${PROJECT_SOURCE_DIR}/combined_core.c
  ${PROJECT_SOURCE_DIR}/libcrux_ct_ops.c
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa44_portable.c
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa65_portable.c
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa87_portable.c
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa_core.c
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa_portable.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem512_portable.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem768_portable.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem1024_portable.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem_core.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem_portable.c
  ${PROJECT_SOURCE_DIR}/libcrux_sha3_portable.c
)
file(GLOB SOURCES_vec256
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa44_avx2.c
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa65_avx2.c
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa87_avx2.c
  ${PROJECT_SOURCE_DIR}/libcrux_mldsa_avx2.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem_avx2.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem512_avx2.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem768_avx2.c
  ${PROJECT_SOURCE_DIR}/libcrux_mlkem1024_avx2.c
  ${PROJECT_SOURCE_DIR}/libcrux_sha3_avx2.c
)

add_library(combined SHARED ${SOURCES})
add_library(combined_static STATIC ${SOURCES})

if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|amd64|AMD64")
  message(STATUS "Detected an x64 architecture")
  add_compile_definitions(LIBCRUX_X64)

  add_library(combined_vec256 OBJECT ${SOURCES_vec256})
  set_target_properties(combined_vec256 PROPERTIES POSITION_INDEPENDENT_CODE ON)
  target_sources(combined_static PRIVATE $<TARGET_OBJECTS:combined_vec256>)
  target_sources(combined PRIVATE $<TARGET_OBJECTS:combined_vec256>)
endif()

if(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64|arm64v8" AND DEFINED ENV{LIBCRUX_NEON})
    message(STATUS "Detected an arm64 architecture")
    add_compile_definitions(LIBCRUX_AARCH64)
endif()


# --- Tests

# tests/mldsa.cc and tests/mlkem.cc are single, variant-parameterized source
# files (see MLDSA_VARIANT / MLKEM_VARIANT in the files themselves); each
# target below compiles the same source with a different variant defined.

add_executable(ml_dsa_test44
    ${PROJECT_SOURCE_DIR}/tests/mldsa.cc
)
target_compile_definitions(ml_dsa_test44 PRIVATE MLDSA_VARIANT=44)
target_link_libraries(ml_dsa_test44 PRIVATE
    combined_static
    gtest_main
    nlohmann_json::nlohmann_json
)

add_executable(ml_dsa_test65
    ${PROJECT_SOURCE_DIR}/tests/mldsa.cc
)
target_compile_definitions(ml_dsa_test65 PRIVATE MLDSA_VARIANT=65)
target_link_libraries(ml_dsa_test65 PRIVATE
    combined_static
    gtest_main
    nlohmann_json::nlohmann_json
)

add_executable(ml_dsa_test87
    ${PROJECT_SOURCE_DIR}/tests/mldsa.cc
)
target_compile_definitions(ml_dsa_test87 PRIVATE MLDSA_VARIANT=87)
target_link_libraries(ml_dsa_test87 PRIVATE
    combined_static
    gtest_main
    nlohmann_json::nlohmann_json
)

add_executable(ml_kem_test512
    ${PROJECT_SOURCE_DIR}/tests/mlkem.cc
)
target_compile_definitions(ml_kem_test512 PRIVATE MLKEM_VARIANT=512)
target_link_libraries(ml_kem_test512 PRIVATE
    combined_static
    gtest_main
    nlohmann_json::nlohmann_json
)

add_executable(ml_kem_test768
    ${PROJECT_SOURCE_DIR}/tests/mlkem.cc
)
target_compile_definitions(ml_kem_test768 PRIVATE MLKEM_VARIANT=768)
target_link_libraries(ml_kem_test768 PRIVATE
    combined_static
    gtest_main
    nlohmann_json::nlohmann_json
)

add_executable(ml_kem_test1024
    ${PROJECT_SOURCE_DIR}/tests/mlkem.cc
)
target_compile_definitions(ml_kem_test1024 PRIVATE MLKEM_VARIANT=1024)
target_link_libraries(ml_kem_test1024 PRIVATE
    combined_static
    gtest_main
    nlohmann_json::nlohmann_json
)

# NOTE: Kyber is not part of the combined extraction. This test target is
# optional (gated on LIBCRUX_KYBER) and intentionally does not link combined_static.
if(DEFINED ENV{LIBCRUX_KYBER})
    add_executable(kyber_test
        ${PROJECT_SOURCE_DIR}/tests/kyber768.cc
    )
    target_link_libraries(kyber_test PRIVATE
        gtest_main
        nlohmann_json::nlohmann_json
    )
endif(DEFINED ENV{LIBCRUX_KYBER})

add_executable(sha3_test
    ${PROJECT_SOURCE_DIR}/tests/sha3.cc
)
target_link_libraries(sha3_test PRIVATE
    combined_static
    gtest_main
    nlohmann_json::nlohmann_json
)

# --- CTest registration

enable_testing()
add_test(NAME ml_dsa_test44 COMMAND ml_dsa_test44)
add_test(NAME ml_dsa_test65 COMMAND ml_dsa_test65)
add_test(NAME ml_dsa_test87 COMMAND ml_dsa_test87)
add_test(NAME ml_kem_test512 COMMAND ml_kem_test512)
add_test(NAME ml_kem_test768 COMMAND ml_kem_test768)
add_test(NAME ml_kem_test1024 COMMAND ml_kem_test1024)
add_test(NAME sha3_test COMMAND sha3_test)
if(DEFINED ENV{LIBCRUX_KYBER})
    add_test(NAME kyber_test COMMAND kyber_test)
endif(DEFINED ENV{LIBCRUX_KYBER})
