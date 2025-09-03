# -*- coding: utf-8 -*-
"""
A bit-sliced implementation of the AES-256 key schedule in Python.

This implementation is for educational purposes to demonstrate the bit-slicing
technique. It is not intended for production use as it's not optimized for
performance in the same way a C or assembly implementation would be.

The key schedule logic has been refactored to use helper functions that
mimic the style of CPU intrinsics like _mm_aeskeygenassist_si128.
"""

# AES constants
RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36]


def bitslice_word(word):
    """
    Bitslices a 4-byte word into 8 32-bit planes.
    Each byte of the input word corresponds to an 8-bit segment in the output planes.
    """
    planes = [0] * 8
    for p in range(8):
        plane = 0
        for i in range(4):  # byte index
            # If the p-th bit of byte i is set...
            if (word[i] >> p) & 1:
                # ...set all 8 bits corresponding to byte i in the plane.
                plane |= 0xFF << (8 * (3 - i))
        planes[p] = plane
    return planes


def unbitslice_word(planes):
    """Unbitslices 8 32-bit planes back into a 4-byte word."""
    word = [0] * 4
    for i in range(4):  # byte index
        byte = 0
        # Mask to select the 8 bits corresponding to this byte
        mask = 0xFF << (8 * (3 - i))
        for p in range(8):  # plane index (and bit index of result)
            # If the bits for this byte are set in plane p...
            if planes[p] & mask:
                # ...set the p-th bit of the result byte.
                byte |= 1 << p
        word[i] = byte
    return word


def sub_word_planes(x):
    """
    Bit-sliced AES S-box implementation operating on 32-bit planes.
    This applies the S-box to all 4 bytes of a word in parallel.
    """
    x0, x1, x2, x3, x4, x5, x6, x7 = x
    t2 = x6 ^ x1
    t3 = x5 ^ x2
    t4 = x4 ^ x3
    t5 = t2 ^ t3
    t6 = t4 ^ t5
    t7 = x0 ^ t6
    t8 = x7 ^ t6
    t9 = t7 & t2
    t10 = t5 ^ t8
    t11 = t3 ^ t7
    t12 = t11 & t10
    t13 = t12 ^ t9
    t14 = t4 ^ t8
    t15 = t2 ^ t14
    t16 = t7 ^ t15
    t17 = t16 & t10
    t18 = t17 ^ t9
    t19 = x3 ^ x1
    t20 = t19 & t16
    t21 = t20 ^ t18
    t22 = x7 ^ x5
    t23 = x7 ^ x4
    t24 = x7 ^ x2
    t25 = t24 & t22
    t26 = t25 ^ t21
    t27 = x0 & t8
    t28 = t27 ^ t26
    t29 = t23 & t8
    t30 = t29 ^ t28
    y4 = t30
    t32 = x0 ^ x5
    t33 = x0 ^ x4
    t34 = x0 ^ x1
    t35 = t34 & t32
    t36 = t35 ^ t30
    t37 = t33 & t34
    t38 = t37 ^ t36
    y5 = t38
    t40 = t22 ^ t32
    t41 = y5 & t40
    t42 = t41 ^ t36
    y6 = t42
    t44 = y4 & t33
    t45 = t44 ^ t42
    t46 = y5 ^ t23
    t47 = t45 & t46
    t48 = t47 ^ t38
    y7 = t48
    t50 = t13 & t32
    t51 = t50 ^ t48
    t52 = t21 ^ t33
    t53 = t51 & t52
    t54 = t53 ^ t45
    y1 = t54
    t56 = y6 ^ t22
    t57 = y1 & t56
    t58 = t57 ^ t51
    t59 = y4 & t34
    t60 = t59 ^ t58
    y2 = t60
    t62 = y7 ^ y5
    t63 = y2 & t62
    t64 = t63 ^ t58
    t65 = y1 ^ y4
    t66 = t64 & t65
    t67 = t66 ^ t60
    y3 = t67
    t69 = y1 ^ y6
    t70 = y3 & t69
    t71 = t70 ^ t64
    t72 = y2 ^ y7
    t73 = t71 & t72
    t74 = t73 ^ t67
    y0 = t74
    c = 0x63
    c_planes = bitslice_word([c, c, c, c])
    return [
        y0 ^ c_planes[0],
        y1 ^ c_planes[1],
        y2 ^ c_planes[2],
        y3 ^ c_planes[3],
        y4 ^ c_planes[4],
        y5 ^ c_planes[5],
        y6 ^ c_planes[6],
        y7 ^ c_planes[7],
    ]


def rot_word_planes(planes):
    """Rotates the word (represented by planes) by 8 bits to the left."""
    rotated_planes = []
    for p in planes:
        rotated_p = ((p << 8) & 0xFFFFFFFF) | (p >> 24)
        rotated_planes.append(rotated_p)
    return rotated_planes


def aes_key_assist(word_planes, rcon_idx):
    """
    Mimics the _mm_aeskeygenassist_si128 intrinsic.
    Performs RotWord, SubWord, and Rcon XOR for the key schedule.
    """
    rcon_val = RCON[rcon_idx]
    # RotWord
    rotated = rot_word_planes(word_planes)
    # SubWord
    subbed = sub_word_planes(rotated)
    # XOR with RCON (applied only to the first byte)
    rcon_word = [rcon_val, 0, 0, 0]
    rcon_planes = bitslice_word(rcon_word)
    result_planes = [subbed[p] ^ rcon_planes[p] for p in range(8)]
    return result_planes


def aes_256_key_schedule(key):
    """
    Generates the AES-256 key schedule from a 256-bit key.
    The key should be a list of 32 bytes.
    """
    if len(key) != 32:
        raise ValueError("Key must be 32 bytes (256 bits) long.")

    # The key schedule is 60 words, stored in bitsliced form
    w_planes = [None] * 60

    # The first 8 words are the key itself, bitsliced
    for i in range(8):
        w_planes[i] = bitslice_word(key[i * 4 : i * 4 + 4])

    for i in range(8, 60):
        temp_planes = w_planes[i - 1]

        if i % 8 == 0:
            temp_planes = aes_key_assist(temp_planes, (i // 8) - 1)
        elif i % 8 == 4:
            # SubWord on w[i-1] for AES-256
            temp_planes = sub_word_planes(temp_planes)

        # XOR with w[i-8]
        w_i_minus_8_planes = w_planes[i - 8]
        w_planes[i] = [w_i_minus_8_planes[p] ^ temp_planes[p] for p in range(8)]

    # Unslice the schedule for the final output
    w_final = [unbitslice_word(p) for p in w_planes]
    return w_final


def main():
    """Main function to demonstrate the key schedule."""
    # Example 256-bit key (32 bytes)
    key = bytes.fromhex(
        "92ace3e348cd821092cd921aa3546374299ab46209691bc28b8752d17f123c20"
    )
    # [
    #     0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    #     0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    #     0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    #     0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f
    # ]

    print("Original Key:")
    print(" ".join(f"{b:02x}" for b in key))
    print("-" * 40)

    key_schedule = aes_256_key_schedule(key)

    print("Generated Key Schedule (60 words):")
    for i, word in enumerate(key_schedule):
        print(f"w[{i:2d}]: {' '.join(f'{b:02x}' for b in word)}")


if __name__ == "__main__":
    main()
