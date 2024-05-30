# cmake -B build -G "Ninja Multi-Config"
# cmake --build build

cmake_minimum_required(VERSION 3.10)

project(libcrux-sha3
    VERSION 0.1.0
    LANGUAGES C CXX
)

set(CMAKE_C_FLAGS " -Wall ")
include_directories(
    ${PROJECT_SOURCE_DIR}
    ${PROJECT_SOURCE_DIR}/internal
    ${PROJECT_SOURCE_DIR}/karamel/include
)
file(GLOB SOURCES
    ${PROJECT_SOURCE_DIR}/libcrux_core.c
    ${PROJECT_SOURCE_DIR}/libcrux_sha3.c
)
# file(GLOB VEC128_SOURCES
#     libcrux_sha3_neon.c
# )
file(GLOB SOURCES_vec256
    ${PROJECT_SOURCE_DIR}/libcrux_sha3_avx2.c
)

if(${CMAKE_SYSTEM_NAME} MATCHES Linux)
    add_compile_options(
        -fPIC
    )
endif(${CMAKE_SYSTEM_NAME} MATCHES Linux)

add_library(sha3_vec256 OBJECT ${SOURCES_vec256})
add_library(sha3 SHARED ${SOURCES})
add_library(sha3_static STATIC ${SOURCES})

target_compile_options(sha3_vec256 PRIVATE
    -mavx
    -mavx2
)

# if(LIBCRUX_VEC256)
target_sources(sha3_static PRIVATE $<TARGET_OBJECTS:sha3_vec256>)
target_sources(sha3 PRIVATE $<TARGET_OBJECTS:sha3_vec256>)
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

add_executable(sha3_test
    ${PROJECT_SOURCE_DIR}/tests/sha3.cc
)
target_link_libraries(sha3_test PRIVATE
    sha3_static
    gtest_main
    nlohmann_json::nlohmann_json
)
