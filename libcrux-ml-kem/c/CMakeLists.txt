# cmake -B build -G "Ninja Multi-Config"
# cmake --build build

cmake_minimum_required(VERSION 3.10)

project(libcrux-ml-kem
    VERSION 0.1.0
    LANGUAGES C CXX
)

set(CMAKE_C_FLAGS " -Wall ")
set(CMAKE_COLOR_DIAGNOSTICS "ON")
include_directories(
    ${PROJECT_SOURCE_DIR}
    ${PROJECT_SOURCE_DIR}/internal
    ${PROJECT_SOURCE_DIR}/karamel/include
)
file(GLOB SOURCES
    ${PROJECT_SOURCE_DIR}/libcrux_core.c
    ${PROJECT_SOURCE_DIR}/libcrux_mlkem512.c
    ${PROJECT_SOURCE_DIR}/libcrux_mlkem768.c
    ${PROJECT_SOURCE_DIR}/libcrux_mlkem1024.c
    ${PROJECT_SOURCE_DIR}/libcrux_polynomial.c
    ${PROJECT_SOURCE_DIR}/libcrux_sha3.c
)
# file(GLOB VEC128_SOURCES
#     libcrux_sha3_neon.c
# )
file(GLOB SOURCES_vec256
    ${PROJECT_SOURCE_DIR}/libcrux_mlkem_avx2.c
    ${PROJECT_SOURCE_DIR}/libcrux_sha3_avx2.c
)

if(${CMAKE_SYSTEM_NAME} MATCHES Linux)
    add_compile_options(
        -fPIC
    )
endif(${CMAKE_SYSTEM_NAME} MATCHES Linux)

add_library(ml_kem_vec256 OBJECT ${SOURCES_vec256})
add_library(ml_kem SHARED ${SOURCES})
add_library(ml_kem_static STATIC ${SOURCES})

target_compile_options(ml_kem_vec256 PRIVATE
    -mavx
    -mavx2
)

# if(LIBCRUX_VEC256)
target_sources(ml_kem_static PRIVATE $<TARGET_OBJECTS:ml_kem_vec256>)
target_sources(ml_kem PRIVATE $<TARGET_OBJECTS:ml_kem_vec256>)
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
    ${PROJECT_SOURCE_DIR}/tests/sha3.cc
)
target_link_libraries(ml_kem_test PRIVATE
    ml_kem_static
    gtest_main
    nlohmann_json::nlohmann_json
)
