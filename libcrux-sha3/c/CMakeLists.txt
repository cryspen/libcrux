# cmake -B build -G "Ninja Multi-Config"
# cmake --build build

cmake_minimum_required(VERSION 3.10)

project(libcrux-sha3
    VERSION 0.1.0
    LANGUAGES C
)

set(CMAKE_C_FLAGS " -Wall ")
include_directories(
    ${PROJECT_SOURCE_DIR}
    ${PROJECT_SOURCE_DIR}/internal
    ${PROJECT_SOURCE_DIR}/karamel/include
)
file(GLOB SOURCES 
    core.c
    libcrux_sha3.c
)
# file(GLOB VEC128_SOURCES
#     libcrux_sha3_neon.c
# )
file(GLOB SOURCES_vec256
    libcrux_sha3_avx2.c
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
