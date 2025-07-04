if(NOT MSVC)
    add_compile_options(
        -Wall
        -fstack-usage
        -Wunused-function
        -fdiagnostics-color=always
        -pedantic
        $<$<CONFIG:DEBUG>:-g>
        $<$<CONFIG:DEBUG>:-Og>
        $<$<CONFIG:RELEASE>:-g>
        $<$<CONFIG:RELEASE>:-O3>
    )
endif(NOT MSVC)

set(CMAKE_COLOR_DIAGNOSTICS "ON")
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)

if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|amd64|AMD64")
    message(STATUS "Detected an x64 architecture")
    add_compile_definitions(LIBCRUX_X64)
endif()

if(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64|arm64v8" AND DEFINED ENV{LIBCRUX_NEON})
    message(STATUS "Detected an arm64 architecture")
    add_compile_definitions(LIBCRUX_AARCH64)
endif()

# --- Tests

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

add_executable(ml_kem_test
    ${PROJECT_SOURCE_DIR}/tests/mlkem768.cc
)
target_link_libraries(ml_kem_test PRIVATE
    gtest_main
    nlohmann_json::nlohmann_json
)

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
    gtest_main
    nlohmann_json::nlohmann_json
)

# --- Benchmarks
if(DEFINED ENV{LIBCRUX_BENCHMARKS})
    FetchContent_Declare(benchmark
        GIT_REPOSITORY https://github.com/google/benchmark.git
        GIT_TAG v1.9.2
    )
    FetchContent_MakeAvailable(benchmark)

    add_executable(ml_kem_bench
        ${PROJECT_SOURCE_DIR}/benches/mlkem768.cc
    )
    target_link_libraries(ml_kem_bench PRIVATE
        benchmark::benchmark
    )

    if(DEFINED ENV{SYMCRYPT_PATH})
        message("Symcrypt path: $ENV{SYMCRYPT_PATH}")
        add_compile_definitions(LIBCRUX_SYMCRYPT)
        target_include_directories(ml_kem_bench PRIVATE $ENV{SYMCRYPT_PATH})
        target_link_directories(ml_kem_bench PRIVATE $ENV{SYMCRYPT_PATH}/bin/lib)
        target_link_libraries(ml_kem_bench PRIVATE symcrypt)
    endif(DEFINED ENV{SYMCRYPT_PATH})

    add_executable(ml_kem_keygen
        ${PROJECT_SOURCE_DIR}/benches/mlkem768_keygen.cc
    )
    target_link_libraries(ml_kem_keygen PRIVATE
        benchmark::benchmark
    )

    add_executable(ml_kem_encaps
        ${PROJECT_SOURCE_DIR}/benches/mlkem768_encaps.cc
    )
    target_link_libraries(ml_kem_encaps PRIVATE
        benchmark::benchmark
    )

    if(NOT MSVC)
        # We benchmark internal functions here that are inlined and thus not available
        # in MSVC.
        add_executable(sha3_bench
            ${PROJECT_SOURCE_DIR}/benches/sha3.cc
        )
        target_link_libraries(sha3_bench PRIVATE
            benchmark::benchmark
        )
    endif(NOT MSVC)
endif(DEFINED ENV{LIBCRUX_BENCHMARKS})
