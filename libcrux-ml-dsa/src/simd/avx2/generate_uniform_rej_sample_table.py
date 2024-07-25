#! /usr/bin/env python3


def trailing_zeros(num):
    return (num & -num).bit_length() - 1


with open("uniform_rej_sample_table.rs", "w+") as f:
    f.write("pub(super) const UNIFORM_REJECTION_SAMPLE_SHUFFLE_TABLE: [[u8; 16]; {}] = [\n".format(1 << 4))

    for bit_pattern in range(0, 1 << 4):
        byte_shuffle_indices = [255] * 16
        counter = 0

        while bit_pattern > 0:
            next_nonzero_index = trailing_zeros(bit_pattern)

            byte_shuffle_indices[counter] = next_nonzero_index * 4
            counter = counter + 1

            byte_shuffle_indices[counter] = (next_nonzero_index * 4) + 1
            counter = counter + 1

            byte_shuffle_indices[counter] = (next_nonzero_index * 4) + 2
            counter = counter + 1

            byte_shuffle_indices[counter] = (next_nonzero_index * 4) + 3
            counter = counter + 1

            bit_pattern = bit_pattern & (bit_pattern - 1)

        f.write(
            "    [" + " ".join(f"0x{x:02x}," for x in byte_shuffle_indices) + "],\n"
        )

    f.write("];")
