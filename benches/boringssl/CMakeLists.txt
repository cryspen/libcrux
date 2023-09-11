cmake_minimum_required(VERSION 3.14)

include(FetchContent)

# Defer enabling C and CXX languages.
project(BORINGSSL_BENCHMARKS CXX)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

FetchContent_Declare(
  boringssl
  GIT_REPOSITORY https://boringssl.googlesource.com/boringssl
  GIT_TAG        1e3da32f3754b1b9136247ee26308cfd959cbeba
)
FetchContent_MakeAvailable(boringssl)

add_executable(kyber768 kyber768.cxx)
target_compile_options(kyber768 PRIVATE -Wall -Wextra)
target_link_libraries(kyber768 crypto)
