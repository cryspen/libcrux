cmake_minimum_required(VERSION 3.14)

include(FetchContent)

# Defer enabling C and CXX languages.
project(BENCHMARKS CXX)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(BENCHMARK_ENABLE_GTEST_TESTS OFF)
FetchContent_Declare(
  benchmark
  GIT_REPOSITORY https://github.com/google/benchmark.git
  GIT_TAG        344117638c8ff7e239044fd0fa7085839fc03021
  GIT_SHALLOW    ON
)
FetchContent_MakeAvailable(benchmark)

FetchContent_Declare(
  boringssl
  GIT_REPOSITORY https://boringssl.googlesource.com/boringssl
  GIT_TAG        1eda2363f9e79aaa5febe91d31b6756ae4f24f30
)
FetchContent_MakeAvailable(boringssl)

add_executable(kyber768 kyber768.cxx)
target_compile_options(kyber768 PRIVATE -Wall -Wextra)
target_link_libraries(kyber768 crypto benchmark::benchmark)

add_executable(shake shake.cxx)
target_include_directories(shake PRIVATE ${boringssl_SOURCE_DIR})
target_compile_options(shake PRIVATE -Wall -Wextra)
target_link_libraries(shake crypto benchmark::benchmark)
