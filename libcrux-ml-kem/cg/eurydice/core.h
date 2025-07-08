static KRML_MUSTINLINE void core_num__u64_9__to_le_bytes(uint64_t v,
                                                         uint8_t buf[8]) {
  store64_le(buf, v);
}
static KRML_MUSTINLINE uint64_t core_num__u64_9__from_le_bytes(uint8_t buf[8]) {
  return load64_le(buf);
}

static KRML_MUSTINLINE uint32_t core_num__u32_8__from_le_bytes(uint8_t buf[4]) {
  return load32_le(buf);
}

static KRML_MUSTINLINE uint32_t core_num__u8_6__count_ones(uint8_t x0) {
#ifdef _MSC_VER
  return __popcnt(x0);
#else
  return __builtin_popcount(x0);
#endif
}

// unsigned overflow wraparound semantics in C
static KRML_MUSTINLINE uint16_t core_num__u16_7__wrapping_add(uint16_t x,
                                                              uint16_t y) {
  return x + y;
}
static KRML_MUSTINLINE uint8_t core_num__u8_6__wrapping_sub(uint8_t x,
                                                            uint8_t y) {
  return x - y;
}

static KRML_MUSTINLINE uint64_t core_num__u64_9__rotate_left(uint64_t x0,
                                                             uint32_t x1) {
  return (x0 << x1 | x0 >> (64 - x1));
}
