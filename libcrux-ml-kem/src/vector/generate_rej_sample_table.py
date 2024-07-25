#! /usr/bin/env python3


def trailing_zeros(num):
    return (num & -num).bit_length() - 1


with open("rej_sample_table.rs", "w+") as f:
    f.write("pub(super) const REJECTION_SAMPLE_SHUFFLE_TABLE: [[u8; 16]; 256] = [\n")

    for bit_pattern in range(0, 1 << 8):
        byte_shuffle_indices = [255] * 16
        counter = 0

        while bit_pattern > 0:
            next_nonzero_index = trailing_zeros(bit_pattern)

            byte_shuffle_indices[counter * 2] = next_nonzero_index * 2
            byte_shuffle_indices[counter * 2 + 1] = next_nonzero_index * 2 + 1
            counter = counter + 1

            bit_pattern = bit_pattern & (bit_pattern - 1)

        f.write(
            "    [" + " ".join(f"0x{x:02x}," for x in byte_shuffle_indices) + "],\n"
        )

    f.write("];")
