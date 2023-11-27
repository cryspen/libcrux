cmake_minimum_required(VERSION 3.0)
project(libcrux)

file(GLOB_RECURSE sources *.c *.h)
include_directories(. $ENV{KRML_HOME}/include $ENV{KRML_HOME}/krmllib/dist/minimal)
add_compile_options(
    -Wall -Wextra -Werror -std=c11
    -Wno-unknown-warning-option
    -Wno-infinite-recursion
    -g -fwrapv -D_BSD_SOURCE -D_DEFAULT_SOURCE
)

add_library(crux SHARED ${sources})

#add "#include "krmllib.h"" to the headers
#cmake -DCMAKE_BUILD_TYPE=Debug -G"Ninja" -B build
#ninja -f build.ninja -C build 
