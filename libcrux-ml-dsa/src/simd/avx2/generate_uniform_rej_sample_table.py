#! /usr/bin/env python3

def trailing_zeros(x):
    return (x & -x).bit_length() - 1

for bit_pattern in range(0, 1 << 8):
    byte_shuffle_indices = [-1] * 16
    counter = 0

    while bit_pattern > 0:
        next_nonzero_index = trailing_zeros(bit_pattern);

        byte_shuffle_indices[counter * 2] = next_nonzero_index * 2;
        byte_shuffle_indices[counter * 2 + 1] = next_nonzero_index * 2 + 1;
        counter = counter + 1;

        bit_pattern = bit_pattern & (bit_pattern - 1)

    print(byte_shuffle_indices)
