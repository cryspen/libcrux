p = 3329

def bitreverse(i):
    ret = 0
    for n in range(7):
        bit = i & 1
        ret <<= 1
        ret |= bit
        i >>= 1
    return ret

NTTRoots = [pow(17, bitreverse(i), p) for i in range(128)]
NTTRootsNeg = [x - 3329 if x > 1664 else x for x in NTTRoots ]

ModRoots = [pow(17, 2*bitreverse(i) + 1, p) for i in range(128)]
ModRootsNeg = [x - 3329 if x > 1664 else x for x in ModRoots]

print(NTTRootsNeg)
print(ModRootsNeg)
