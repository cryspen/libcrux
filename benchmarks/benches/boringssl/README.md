This directory contains programs for benchmarking various algorithms implemented
by BoringSSL, so as to compare their performance with the implementations in
libcrux. As of now, there is only a program to benchmark Kyber768.

In order to build this benchmark, run the following sequence of commands:

1. `mkdir build && cd build`
2. `cmake -DCMAKE_BUILD_TYPE=Release -G"Ninja" ..`
3. `ninja`

To then run the benchmark, in the `build` directory, simply run `./kyber768`
