// Lean compiler output
// Module: extraction.hacspec_sha3
// Imports: public import Init public import Hax public import Stubs public import Std.Tactic.Do public import Std.Do.Triple public import Std.Tactic.Do.Syntax
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
lean_object* lp_Hax_RustM_fail___redArg(uint8_t);
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_BitVec_uaddOverflow(lean_object*, lean_object*, lean_object*);
lean_object* lp_Hax_USize64_add(lean_object*, lean_object*);
uint8_t l_BitVec_umulOverflow(lean_object*, lean_object*, lean_object*);
lean_object* lp_Hax_USize64_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_lt___at___00hacspec__sha3_keccak__f_get_spec_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_lt___at___00hacspec__sha3_keccak__f_get_spec_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get_spec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get_spec___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1___boxed__const__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__21;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__23;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__25;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__26;
lean_object* lp_Hax_RustM_of__isOk___redArg(lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__27;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__26;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__27;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__28;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__1;
static uint8_t lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__2;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lp_Hax_rust__primitives_hax_monomorphized__update__at_update__at__usize___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota_spec___boxed(lean_object*, lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE;
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE;
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE;
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE;
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE256__RATE;
LEAN_EXPORT uint8_t lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__DELIM;
LEAN_EXPORT uint8_t lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE__DELIM;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static uint8_t lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
static lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index(lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index_spec(lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index_spec___boxed(lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
lean_object* lp_libcrux__sha3_core__models_num_Impl__9_from__le__bytes(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__0;
static uint8_t lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__1;
lean_object* lp_Hax_USize64_fold__range___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_ge___at___00hacspec__sha3_sponge_xor__block__into__state_spec_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_ge___at___00hacspec__sha3_sponge_xor__block__into__state_spec_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state_spec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state_spec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extraction"};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__0 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 107, 14, 61, 133, 25, 17, 132)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__1 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__1_value;
static const lean_string_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "hacspec_sha3"};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__2 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__2_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__1_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__2_value),LEAN_SCALAR_PTR_LITERAL(114, 44, 250, 167, 245, 11, 130, 64)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__3 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__3_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__3_value),((lean_object*)(((size_t)(240) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(241, 80, 207, 2, 100, 254, 186, 41)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__4 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__4_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__4_value),((lean_object*)(((size_t)(28) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(156, 250, 148, 229, 219, 93, 134, 38)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__5 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__5_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__5_value),((lean_object*)(((size_t)(240) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(191, 136, 7, 106, 18, 48, 213, 3)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__6 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__6_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__6_value),((lean_object*)(((size_t)(33) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(220, 49, 181, 196, 222, 199, 143, 214)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__7 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__7_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__7_value),((lean_object*)(((size_t)(28) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(149, 137, 212, 181, 99, 229, 73, 38)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__8 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__8_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__8_value),((lean_object*)(((size_t)(33) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(190, 240, 81, 106, 25, 133, 146, 247)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__9 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__9_value;
static const lean_string_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_sorry"};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__10 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__10_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__9_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__10_value),LEAN_SCALAR_PTR_LITERAL(87, 2, 143, 87, 51, 205, 174, 102)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__11 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__11_value;
static const lean_string_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__12 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__12_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__11_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__12_value),LEAN_SCALAR_PTR_LITERAL(18, 44, 3, 234, 168, 28, 40, 193)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__13 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__13_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__13_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 190, 109, 196, 121, 205, 239, 138)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__14 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__14_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__14_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 223, 188, 190, 242, 145, 128, 193)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__15 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__15_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__15_value),((lean_object*)(((size_t)(1327956711) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(143, 136, 68, 6, 102, 100, 127, 24)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__16 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__16_value;
static const lean_string_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__17 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__17_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__16_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__17_value),LEAN_SCALAR_PTR_LITERAL(68, 80, 71, 144, 61, 178, 179, 22)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__18 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__18_value;
static const lean_string_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__19 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__19_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__18_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__19_value),LEAN_SCALAR_PTR_LITERAL(80, 62, 175, 207, 86, 181, 181, 39)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__20 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__20_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__20_value),((lean_object*)(((size_t)(19) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(66, 247, 34, 42, 254, 129, 66, 73)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__21 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__21_value;
lean_object* lean_sorry(uint8_t);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Stubs"};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__0 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__0_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 219, 98, 70, 28, 36, 154, 41)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__1 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__1_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__1_value),((lean_object*)(((size_t)(105) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 119, 155, 255, 226, 213, 109, 166)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__2 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__2_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__2_value),((lean_object*)(((size_t)(39) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(149, 250, 232, 199, 128, 111, 221, 102)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__3 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__3_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__3_value),((lean_object*)(((size_t)(105) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(252, 184, 4, 251, 113, 228, 53, 2)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__4 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__4_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__4_value),((lean_object*)(((size_t)(44) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(220, 118, 162, 144, 218, 225, 118, 137)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__5 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__5_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__5_value),((lean_object*)(((size_t)(39) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(165, 46, 218, 197, 96, 204, 244, 135)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__6 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__6_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__6_value),((lean_object*)(((size_t)(44) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(217, 77, 157, 190, 126, 202, 3, 25)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__7 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__7_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__7_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__10_value),LEAN_SCALAR_PTR_LITERAL(140, 197, 80, 99, 78, 114, 27, 114)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__8 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__8_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__8_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__12_value),LEAN_SCALAR_PTR_LITERAL(101, 201, 134, 122, 138, 234, 17, 88)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__9 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__9_value;
static const lean_ctor_object lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__9_value),((lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 7, 100, 67, 0, 120, 209, 56)}};
static const lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__10 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__10_value;
static lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__11;
static lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__12;
static lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__13;
static lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__14;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__0___boxed(lean_object*, lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__2;
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__3;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_libcrux__sha3_core__models_num_Impl__9_rotate__left(uint64_t, uint32_t);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___closed__0 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___closed__0_value;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta(lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_rho(lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_pi___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_pi___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_pi(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint64_t lean_uint64_complement(uint64_t);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_chi___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_chi___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_chi(lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___closed__0 = (const lean_object*)&lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___closed__0_value;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(lean_object*);
static lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg___closed__0;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_Hax_USize64_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___closed__0;
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0___boxed__const__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0;
static lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1;
static lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__2;
lean_object* lp_Hax_rust__primitives_slice_slice__length___redArg(lean_object*);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
lean_object* lp_Hax_rust__primitives_unsize___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_gt___at___00hacspec__sha3_sponge_keccak_spec_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_gt___at___00hacspec__sha3_sponge_keccak_spec_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak_spec(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak_spec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__224___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__224(lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__256___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__256(lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__384___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__384(lean_object*);
static lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__512___closed__0;
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__512(lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake128(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake128_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake128_spec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake256(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake256_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake256_spec___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 3;
x_2 = lp_Hax_RustM_fail___redArg(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lp_Hax_RustM_fail___redArg(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_12; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(64u);
x_29 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3;
x_30 = l_BitVec_umulOverflow(x_28, x_29, x_2);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lp_Hax_USize64_mul(x_29, x_2);
x_12 = x_31;
goto block_27;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
block_11:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_fget_borrowed(x_1, x_4);
lean_dec(x_4);
lean_inc(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
block_27:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(64u);
x_14 = l_BitVec_uaddOverflow(x_13, x_12, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lp_Hax_USize64_add(x_12, x_3);
lean_dec(x_12);
x_4 = x_15;
goto block_11;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_12);
x_16 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_lt___at___00hacspec__sha3_keccak__f_get_spec_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_nat_dec_lt(x_1, x_2);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_lt___at___00hacspec__sha3_keccak__f_get_spec_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_rust__primitives_cmp_lt___at___00hacspec__sha3_keccak__f_get_spec_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get_spec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_get_spec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get_spec(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(24u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__0;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 32898;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372036854808714ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372039002292224ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 32907;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 2147483649;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372039002292353ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372036854808585ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 138;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 136;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 2147516425;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 2147483658;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 2147516555;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372036854775947ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372036854808713ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372036854808579ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372036854808578ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372036854775936ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 32778;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372039002259466ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372036854808704ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__21;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 9223372039002292232ULL;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__23;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__25;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__26;
x_2 = lp_Hax_RustM_of__isOk___redArg(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS() {
_start:
{
lean_object* x_1; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__27;
return x_1;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__0;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 36;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 3;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 41;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 18;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 44;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 45;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 2;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 62;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 6;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 43;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 15;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 61;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 28;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 55;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 25;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 21;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 56;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 27;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 20;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 8;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 14;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__26;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__27;
x_2 = lp_Hax_RustM_of__isOk___redArg(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS() {
_start:
{
lean_object* x_1; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__28;
return x_1;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(24u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static uint8_t _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_11; uint8_t x_29; 
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
x_4 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_29 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__2;
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_dec_ref(x_1);
x_30 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
lean_object* x_41; uint64_t x_42; 
x_41 = lean_array_fget_borrowed(x_1, x_4);
x_42 = lean_unbox_uint64(x_41);
x_11 = x_42;
goto block_28;
}
block_10:
{
uint64_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_uint64_xor(x_5, x_6);
x_8 = lean_box_uint64(x_7);
x_9 = lp_Hax_rust__primitives_hax_monomorphized__update__at_update__at__usize___redArg(x_3, x_1, x_4, x_8);
return x_9;
}
block_28:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__1;
x_13 = lean_nat_dec_lt(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec_ref(x_1);
x_14 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint64_t x_27; 
x_25 = lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS;
x_26 = lean_array_fget(x_25, x_2);
x_27 = lean_unbox_uint64(x_26);
lean_dec(x_26);
x_5 = x_11;
x_6 = x_27;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota_spec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_iota_spec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota_spec(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(144u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE() {
_start:
{
lean_object* x_1; 
x_1 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE___closed__0;
return x_1;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(136u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE() {
_start:
{
lean_object* x_1; 
x_1 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE___closed__0;
return x_1;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(104u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE() {
_start:
{
lean_object* x_1; 
x_1 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE___closed__0;
return x_1;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(72u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE() {
_start:
{
lean_object* x_1; 
x_1 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE___closed__0;
return x_1;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(168u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE() {
_start:
{
lean_object* x_1; 
x_1 = lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE___closed__0;
return x_1;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE256__RATE() {
_start:
{
lean_object* x_1; 
x_1 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE___closed__0;
return x_1;
}
}
static uint8_t _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__DELIM() {
_start:
{
uint8_t x_1; 
x_1 = 6;
return x_1;
}
}
static uint8_t _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE__DELIM() {
_start:
{
uint8_t x_1; 
x_1 = 31;
return x_1;
}
}
static uint8_t _init_lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 2;
x_2 = lp_Hax_RustM_fail___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_11; lean_object* x_12; lean_object* x_17; uint8_t x_22; 
x_2 = lean_unsigned_to_nat(64u);
x_11 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3;
x_22 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_nat_mod(x_1, x_11);
x_17 = x_23;
goto block_21;
}
else
{
lean_object* x_24; 
x_24 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
return x_24;
}
block_10:
{
uint8_t x_5; 
x_5 = l_BitVec_uaddOverflow(x_2, x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lp_Hax_USize64_add(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
return x_9;
}
}
block_16:
{
uint8_t x_13; 
x_13 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_nat_div(x_1, x_11);
x_3 = x_12;
x_4 = x_14;
goto block_10;
}
else
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
return x_15;
}
}
block_21:
{
uint8_t x_18; 
x_18 = l_BitVec_umulOverflow(x_2, x_11, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lp_Hax_USize64_mul(x_11, x_17);
lean_dec(x_17);
x_12 = x_19;
goto block_16;
}
else
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index_spec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_lane__index_spec___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index_spec(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 3;
x_2 = lp_Hax_RustM_fail___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; lean_object* x_126; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; uint8_t x_150; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; uint8_t x_197; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; lean_object* x_241; uint8_t x_242; uint8_t x_259; uint8_t x_260; uint8_t x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; uint8_t x_281; uint8_t x_282; uint8_t x_283; lean_object* x_284; uint8_t x_285; uint8_t x_302; uint8_t x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; uint8_t x_323; uint8_t x_324; lean_object* x_325; uint8_t x_326; uint8_t x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; uint8_t x_363; lean_object* x_364; uint8_t x_365; uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_401; uint8_t x_402; lean_object* x_419; uint8_t x_436; 
x_436 = l_BitVec_umulOverflow(x_2, x_4, x_6);
if (x_436 == 0)
{
lean_object* x_437; 
x_437 = lp_Hax_USize64_mul(x_4, x_6);
x_419 = x_437;
goto block_435;
}
else
{
lean_object* x_438; uint8_t x_439; 
lean_dec_ref(x_5);
x_438 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_439 = !lean_is_exclusive(x_438);
if (x_439 == 0)
{
lean_object* x_440; uint8_t x_441; 
x_440 = lean_ctor_get(x_438, 0);
x_441 = !lean_is_exclusive(x_440);
if (x_441 == 0)
{
return x_438;
}
else
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_ctor_get(x_440, 0);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_438, 0, x_443);
return x_438;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_444 = lean_ctor_get(x_438, 0);
lean_inc(x_444);
lean_dec(x_438);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_446 = x_444;
} else {
 lean_dec_ref(x_444);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(0, 1, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_445);
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_447);
return x_448;
}
}
block_14:
{
uint64_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_uint64_xor(x_10, x_7);
x_12 = lean_box_uint64(x_11);
x_13 = lp_Hax_rust__primitives_hax_monomorphized__update__at_update__at__usize___redArg(x_8, x_5, x_9, x_12);
lean_dec(x_9);
lean_dec(x_8);
return x_13;
}
block_118:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_mk_empty_array_with_capacity(x_1);
x_24 = lean_box(x_20);
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_box(x_18);
x_27 = lean_array_push(x_25, x_26);
x_28 = lean_box(x_21);
x_29 = lean_array_push(x_27, x_28);
x_30 = lean_box(x_19);
x_31 = lean_array_push(x_29, x_30);
x_32 = lean_box(x_15);
x_33 = lean_array_push(x_31, x_32);
x_34 = lean_box(x_17);
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_box(x_16);
x_37 = lean_array_push(x_35, x_36);
x_38 = lean_box(x_22);
x_39 = lean_array_push(x_37, x_38);
x_40 = lp_libcrux__sha3_core__models_num_Impl__9_from__le__bytes(x_39);
lean_dec_ref(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_5);
x_41 = lean_box(0);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec_ref(x_5);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_free_object(x_40);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec_ref(x_43);
x_48 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index(x_6);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_47);
lean_dec_ref(x_5);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_free_object(x_48);
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec_ref(x_50);
x_55 = lean_unsigned_to_nat(25u);
x_56 = l_BitVec_ofNat(x_2, x_55);
x_57 = lean_nat_dec_lt(x_54, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_47);
lean_dec_ref(x_5);
x_58 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_58, 0, x_63);
return x_58;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
lean_object* x_69; uint64_t x_70; uint64_t x_71; 
x_69 = lean_array_fget_borrowed(x_5, x_54);
x_70 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_71 = lean_unbox_uint64(x_69);
x_7 = x_70;
x_8 = x_56;
x_9 = x_54;
x_10 = x_71;
goto block_14;
}
}
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_48, 0);
lean_inc(x_72);
lean_dec(x_48);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_47);
lean_dec_ref(x_5);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
lean_dec_ref(x_72);
x_78 = lean_unsigned_to_nat(25u);
x_79 = l_BitVec_ofNat(x_2, x_78);
x_80 = lean_nat_dec_lt(x_77, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_47);
lean_dec_ref(x_5);
x_81 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_84);
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_83;
}
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
else
{
lean_object* x_88; uint64_t x_89; uint64_t x_90; 
x_88 = lean_array_fget_borrowed(x_5, x_77);
x_89 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_90 = lean_unbox_uint64(x_88);
x_7 = x_89;
x_8 = x_79;
x_9 = x_77;
x_10 = x_90;
goto block_14;
}
}
}
}
}
else
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_40, 0);
lean_inc(x_91);
lean_dec(x_40);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_5);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec_ref(x_91);
x_97 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index(x_6);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_96);
lean_dec_ref(x_5);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_99;
}
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_99);
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
lean_dec_ref(x_98);
x_105 = lean_unsigned_to_nat(25u);
x_106 = l_BitVec_ofNat(x_2, x_105);
x_107 = lean_nat_dec_lt(x_104, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_96);
lean_dec_ref(x_5);
x_108 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
if (lean_is_scalar(x_110)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_110;
}
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
else
{
lean_object* x_115; uint64_t x_116; uint64_t x_117; 
x_115 = lean_array_fget_borrowed(x_5, x_104);
x_116 = lean_unbox_uint64(x_96);
lean_dec(x_96);
x_117 = lean_unbox_uint64(x_115);
x_7 = x_116;
x_8 = x_106;
x_9 = x_104;
x_10 = x_117;
goto block_14;
}
}
}
}
}
}
block_142:
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_array_get_size(x_3);
x_128 = lean_nat_dec_lt(x_126, x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_126);
lean_dec_ref(x_5);
x_129 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_129, 0, x_134);
return x_129;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_129, 0);
lean_inc(x_135);
lean_dec(x_129);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_array_fget_borrowed(x_3, x_126);
lean_dec(x_126);
x_141 = lean_unbox(x_140);
x_15 = x_119;
x_16 = x_120;
x_17 = x_121;
x_18 = x_122;
x_19 = x_124;
x_20 = x_123;
x_21 = x_125;
x_22 = x_141;
goto block_118;
}
}
block_166:
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_unsigned_to_nat(7u);
x_152 = l_BitVec_ofNat(x_2, x_151);
x_153 = l_BitVec_uaddOverflow(x_2, x_149, x_152);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lp_Hax_USize64_add(x_149, x_152);
lean_dec(x_152);
lean_dec(x_149);
x_119 = x_143;
x_120 = x_150;
x_121 = x_144;
x_122 = x_145;
x_123 = x_146;
x_124 = x_147;
x_125 = x_148;
x_126 = x_154;
goto block_142;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_152);
lean_dec(x_149);
lean_dec_ref(x_5);
x_155 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_155, 0);
lean_inc(x_161);
lean_dec(x_155);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
block_190:
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_array_get_size(x_3);
x_176 = lean_nat_dec_lt(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec_ref(x_5);
x_177 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_177, 0);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
return x_177;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_177, 0, x_182);
return x_177;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_177, 0);
lean_inc(x_183);
lean_dec(x_177);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
else
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_array_fget_borrowed(x_3, x_174);
lean_dec(x_174);
x_189 = lean_unbox(x_188);
x_143 = x_167;
x_144 = x_168;
x_145 = x_169;
x_146 = x_171;
x_147 = x_170;
x_148 = x_172;
x_149 = x_173;
x_150 = x_189;
goto block_166;
}
}
block_213:
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_unsigned_to_nat(6u);
x_199 = l_BitVec_ofNat(x_2, x_198);
x_200 = l_BitVec_uaddOverflow(x_2, x_196, x_199);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lp_Hax_USize64_add(x_196, x_199);
lean_dec(x_199);
x_167 = x_191;
x_168 = x_197;
x_169 = x_192;
x_170 = x_193;
x_171 = x_194;
x_172 = x_195;
x_173 = x_196;
x_174 = x_201;
goto block_190;
}
else
{
lean_object* x_202; uint8_t x_203; 
lean_dec(x_199);
lean_dec(x_196);
lean_dec_ref(x_5);
x_202 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
return x_202;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_202, 0, x_207);
return x_202;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_202, 0);
lean_inc(x_208);
lean_dec(x_202);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_210 = x_208;
} else {
 lean_dec_ref(x_208);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 1, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
block_236:
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_array_get_size(x_3);
x_222 = lean_nat_dec_lt(x_220, x_221);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
lean_dec(x_220);
lean_dec(x_219);
lean_dec_ref(x_5);
x_223 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_223, 0);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
return x_223;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_223, 0, x_228);
return x_223;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_223, 0);
lean_inc(x_229);
lean_dec(x_223);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
else
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_array_fget_borrowed(x_3, x_220);
lean_dec(x_220);
x_235 = lean_unbox(x_234);
x_191 = x_214;
x_192 = x_215;
x_193 = x_217;
x_194 = x_216;
x_195 = x_218;
x_196 = x_219;
x_197 = x_235;
goto block_213;
}
}
block_258:
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_243 = lean_unsigned_to_nat(5u);
x_244 = l_BitVec_ofNat(x_2, x_243);
x_245 = l_BitVec_uaddOverflow(x_2, x_241, x_244);
if (x_245 == 0)
{
lean_object* x_246; 
x_246 = lp_Hax_USize64_add(x_241, x_244);
lean_dec(x_244);
x_214 = x_242;
x_215 = x_237;
x_216 = x_238;
x_217 = x_239;
x_218 = x_240;
x_219 = x_241;
x_220 = x_246;
goto block_236;
}
else
{
lean_object* x_247; uint8_t x_248; 
lean_dec(x_244);
lean_dec(x_241);
lean_dec_ref(x_5);
x_247 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_247, 0);
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
return x_247;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_249, 0);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_247, 0, x_252);
return x_247;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_253 = lean_ctor_get(x_247, 0);
lean_inc(x_253);
lean_dec(x_247);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(0, 1, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_254);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
}
block_280:
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_array_get_size(x_3);
x_266 = lean_nat_dec_lt(x_264, x_265);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
lean_dec(x_264);
lean_dec(x_263);
lean_dec_ref(x_5);
x_267 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
return x_267;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_267, 0, x_272);
return x_267;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_267, 0);
lean_inc(x_273);
lean_dec(x_267);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_275 = x_273;
} else {
 lean_dec_ref(x_273);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_274);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
else
{
lean_object* x_278; uint8_t x_279; 
x_278 = lean_array_fget_borrowed(x_3, x_264);
lean_dec(x_264);
x_279 = lean_unbox(x_278);
x_237 = x_259;
x_238 = x_261;
x_239 = x_260;
x_240 = x_262;
x_241 = x_263;
x_242 = x_279;
goto block_258;
}
}
block_301:
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_286 = lean_unsigned_to_nat(4u);
x_287 = l_BitVec_ofNat(x_2, x_286);
x_288 = l_BitVec_uaddOverflow(x_2, x_284, x_287);
if (x_288 == 0)
{
lean_object* x_289; 
x_289 = lp_Hax_USize64_add(x_284, x_287);
lean_dec(x_287);
x_259 = x_281;
x_260 = x_285;
x_261 = x_282;
x_262 = x_283;
x_263 = x_284;
x_264 = x_289;
goto block_280;
}
else
{
lean_object* x_290; uint8_t x_291; 
lean_dec(x_287);
lean_dec(x_284);
lean_dec_ref(x_5);
x_290 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_290, 0);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
return x_290;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_292, 0);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_290, 0, x_295);
return x_290;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_296 = lean_ctor_get(x_290, 0);
lean_inc(x_296);
lean_dec(x_290);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 x_298 = x_296;
} else {
 lean_dec_ref(x_296);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(0, 1, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
}
}
block_322:
{
lean_object* x_307; uint8_t x_308; 
x_307 = lean_array_get_size(x_3);
x_308 = lean_nat_dec_lt(x_306, x_307);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
lean_dec(x_306);
lean_dec(x_305);
lean_dec_ref(x_5);
x_309 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
return x_309;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_311, 0);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_309, 0, x_314);
return x_309;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_315 = lean_ctor_get(x_309, 0);
lean_inc(x_315);
lean_dec(x_309);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 1, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_316);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
return x_319;
}
}
else
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_array_fget_borrowed(x_3, x_306);
lean_dec(x_306);
x_321 = lean_unbox(x_320);
x_281 = x_302;
x_282 = x_303;
x_283 = x_304;
x_284 = x_305;
x_285 = x_321;
goto block_301;
}
}
block_342:
{
lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_327 = lean_unsigned_to_nat(3u);
x_328 = l_BitVec_ofNat(x_2, x_327);
x_329 = l_BitVec_uaddOverflow(x_2, x_325, x_328);
if (x_329 == 0)
{
lean_object* x_330; 
x_330 = lp_Hax_USize64_add(x_325, x_328);
lean_dec(x_328);
x_302 = x_323;
x_303 = x_324;
x_304 = x_326;
x_305 = x_325;
x_306 = x_330;
goto block_322;
}
else
{
lean_object* x_331; uint8_t x_332; 
lean_dec(x_328);
lean_dec(x_325);
lean_dec_ref(x_5);
x_331 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_332 = !lean_is_exclusive(x_331);
if (x_332 == 0)
{
lean_object* x_333; uint8_t x_334; 
x_333 = lean_ctor_get(x_331, 0);
x_334 = !lean_is_exclusive(x_333);
if (x_334 == 0)
{
return x_331;
}
else
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_331, 0, x_336);
return x_331;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_337 = lean_ctor_get(x_331, 0);
lean_inc(x_337);
lean_dec(x_331);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_339 = x_337;
} else {
 lean_dec_ref(x_337);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(0, 1, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_338);
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_340);
return x_341;
}
}
}
block_362:
{
lean_object* x_347; uint8_t x_348; 
x_347 = lean_array_get_size(x_3);
x_348 = lean_nat_dec_lt(x_346, x_347);
if (x_348 == 0)
{
lean_object* x_349; uint8_t x_350; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec_ref(x_5);
x_349 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = !lean_is_exclusive(x_351);
if (x_352 == 0)
{
return x_349;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_349, 0, x_354);
return x_349;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_355 = lean_ctor_get(x_349, 0);
lean_inc(x_355);
lean_dec(x_349);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 x_357 = x_355;
} else {
 lean_dec_ref(x_355);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(0, 1, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_356);
x_359 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_359, 0, x_358);
return x_359;
}
}
else
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_array_fget_borrowed(x_3, x_346);
lean_dec(x_346);
x_361 = lean_unbox(x_360);
x_323 = x_343;
x_324 = x_344;
x_325 = x_345;
x_326 = x_361;
goto block_342;
}
}
block_381:
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_366 = lean_unsigned_to_nat(2u);
x_367 = l_BitVec_ofNat(x_2, x_366);
x_368 = l_BitVec_uaddOverflow(x_2, x_364, x_367);
if (x_368 == 0)
{
lean_object* x_369; 
x_369 = lp_Hax_USize64_add(x_364, x_367);
lean_dec(x_367);
x_343 = x_365;
x_344 = x_363;
x_345 = x_364;
x_346 = x_369;
goto block_362;
}
else
{
lean_object* x_370; uint8_t x_371; 
lean_dec(x_367);
lean_dec(x_364);
lean_dec_ref(x_5);
x_370 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
lean_object* x_372; uint8_t x_373; 
x_372 = lean_ctor_get(x_370, 0);
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
return x_370;
}
else
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_372, 0);
lean_inc(x_374);
lean_dec(x_372);
x_375 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_370, 0, x_375);
return x_370;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_376 = lean_ctor_get(x_370, 0);
lean_inc(x_376);
lean_dec(x_370);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 1, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_377);
x_380 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_380, 0, x_379);
return x_380;
}
}
}
block_400:
{
lean_object* x_385; uint8_t x_386; 
x_385 = lean_array_get_size(x_3);
x_386 = lean_nat_dec_lt(x_384, x_385);
if (x_386 == 0)
{
lean_object* x_387; uint8_t x_388; 
lean_dec(x_384);
lean_dec(x_383);
lean_dec_ref(x_5);
x_387 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_388 = !lean_is_exclusive(x_387);
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_387, 0);
x_390 = !lean_is_exclusive(x_389);
if (x_390 == 0)
{
return x_387;
}
else
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_389, 0);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_387, 0, x_392);
return x_387;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_393 = lean_ctor_get(x_387, 0);
lean_inc(x_393);
lean_dec(x_387);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 x_395 = x_393;
} else {
 lean_dec_ref(x_393);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(0, 1, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_394);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
return x_397;
}
}
else
{
lean_object* x_398; uint8_t x_399; 
x_398 = lean_array_fget_borrowed(x_3, x_384);
lean_dec(x_384);
x_399 = lean_unbox(x_398);
x_363 = x_382;
x_364 = x_383;
x_365 = x_399;
goto block_381;
}
}
block_418:
{
lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_403 = lean_unsigned_to_nat(1u);
x_404 = l_BitVec_ofNat(x_2, x_403);
x_405 = l_BitVec_uaddOverflow(x_2, x_401, x_404);
if (x_405 == 0)
{
lean_object* x_406; 
x_406 = lp_Hax_USize64_add(x_401, x_404);
lean_dec(x_404);
x_382 = x_402;
x_383 = x_401;
x_384 = x_406;
goto block_400;
}
else
{
lean_object* x_407; uint8_t x_408; 
lean_dec(x_404);
lean_dec(x_401);
lean_dec_ref(x_5);
x_407 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_408 = !lean_is_exclusive(x_407);
if (x_408 == 0)
{
lean_object* x_409; uint8_t x_410; 
x_409 = lean_ctor_get(x_407, 0);
x_410 = !lean_is_exclusive(x_409);
if (x_410 == 0)
{
return x_407;
}
else
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_407, 0, x_412);
return x_407;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_413 = lean_ctor_get(x_407, 0);
lean_inc(x_413);
lean_dec(x_407);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 x_415 = x_413;
} else {
 lean_dec_ref(x_413);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(0, 1, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_414);
x_417 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_417, 0, x_416);
return x_417;
}
}
}
block_435:
{
lean_object* x_420; uint8_t x_421; 
x_420 = lean_array_get_size(x_3);
x_421 = lean_nat_dec_lt(x_419, x_420);
if (x_421 == 0)
{
lean_object* x_422; uint8_t x_423; 
lean_dec(x_419);
lean_dec_ref(x_5);
x_422 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_423 = !lean_is_exclusive(x_422);
if (x_423 == 0)
{
lean_object* x_424; uint8_t x_425; 
x_424 = lean_ctor_get(x_422, 0);
x_425 = !lean_is_exclusive(x_424);
if (x_425 == 0)
{
return x_422;
}
else
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
lean_dec(x_424);
x_427 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_422, 0, x_427);
return x_422;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_428 = lean_ctor_get(x_422, 0);
lean_inc(x_428);
lean_dec(x_422);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 x_430 = x_428;
} else {
 lean_dec_ref(x_428);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(0, 1, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_429);
x_432 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_432, 0, x_431);
return x_432;
}
}
else
{
lean_object* x_433; uint8_t x_434; 
x_433 = lean_array_fget_borrowed(x_3, x_419);
x_434 = lean_unbox(x_433);
x_401 = x_419;
x_402 = x_434;
goto block_418;
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static uint8_t _init_lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_2 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__0;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_12; 
x_4 = lean_unsigned_to_nat(8u);
x_5 = lean_unsigned_to_nat(64u);
x_6 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__0;
x_7 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___boxed), 6, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_6);
x_12 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__1;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_nat_div(x_3, x_6);
x_8 = x_13;
goto block_11;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_14 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_10 = lp_Hax_USize64_fold__range___redArg(x_9, x_8, x_1, x_7);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_ge___at___00hacspec__sha3_sponge_xor__block__into__state_spec_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_nat_dec_le(x_2, x_1);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_ge___at___00hacspec__sha3_sponge_xor__block__into__state_spec_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_rust__primitives_cmp_ge___at___00hacspec__sha3_sponge_xor__block__into__state_spec_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state_spec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state_spec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state_spec(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 0;
x_6 = ((lean_object*)(lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__21));
x_7 = lean_sorry(x_5);
x_8 = lean_apply_1(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3322396896u);
x_2 = ((lean_object*)(lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__10));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__17));
x_2 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__11;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state___closed__19));
x_2 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__12;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__13;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 0;
x_5 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__14;
x_6 = lean_sorry(x_4);
x_7 = lean_apply_1(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_uint64_xor(x_1, x_2);
x_4 = lean_box_uint64(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__0(x_3, x_4);
return x_5;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_5 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0;
x_9 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec_ref(x_2);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc_ref(x_2);
x_12 = lean_apply_2(x_2, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_dec_ref(x_2);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_2);
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__1;
x_16 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_14);
lean_dec_ref(x_2);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
lean_dec(x_14);
lean_dec_ref(x_2);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc_ref(x_2);
x_19 = lean_apply_2(x_2, x_14, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_2);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_2);
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__2;
x_23 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_21);
lean_dec_ref(x_2);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
lean_dec(x_21);
lean_dec_ref(x_2);
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc_ref(x_2);
x_26 = lean_apply_2(x_2, x_21, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_2);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_2);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__3;
x_30 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_28);
lean_dec_ref(x_2);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_dec_ref(x_31);
lean_dec(x_28);
lean_dec_ref(x_2);
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_apply_2(x_2, x_28, x_32);
return x_33;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint64_t x_6; uint64_t x_30; lean_object* x_31; uint64_t x_37; lean_object* x_38; uint64_t x_55; lean_object* x_72; lean_object* x_78; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_unsigned_to_nat(4u);
x_96 = l_BitVec_ofNat(x_3, x_95);
x_97 = l_BitVec_uaddOverflow(x_3, x_4, x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lp_Hax_USize64_add(x_4, x_96);
lean_dec(x_96);
x_78 = x_98;
goto block_94;
}
else
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_96);
x_99 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_99, 0, x_104);
return x_99;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
lean_dec(x_99);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
block_29:
{
uint32_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = lp_libcrux__sha3_core__models_num_Impl__9_rotate__left(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_9);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_15 = lean_uint64_xor(x_5, x_14);
x_16 = lean_box_uint64(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_uint64_xor(x_5, x_18);
x_20 = lean_box_uint64(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_23 = x_9;
} else {
 lean_dec_ref(x_9);
 x_23 = lean_box(0);
}
x_24 = lean_unbox_uint64(x_22);
lean_dec(x_22);
x_25 = lean_uint64_xor(x_5, x_24);
x_26 = lean_box_uint64(x_25);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
block_36:
{
uint8_t x_32; 
x_32 = lean_nat_dec_lt(x_31, x_1);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
x_33 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
return x_33;
}
else
{
lean_object* x_34; uint64_t x_35; 
x_34 = lean_array_fget_borrowed(x_2, x_31);
lean_dec(x_31);
x_35 = lean_unbox_uint64(x_34);
x_5 = x_30;
x_6 = x_35;
goto block_29;
}
}
block_54:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_BitVec_ofNat(x_3, x_39);
x_41 = lean_nat_dec_eq(x_1, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_nat_mod(x_38, x_1);
lean_dec(x_38);
x_30 = x_37;
x_31 = x_42;
goto block_36;
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_38);
x_43 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_43, 0, x_48);
return x_43;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
block_71:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_unsigned_to_nat(1u);
x_57 = l_BitVec_ofNat(x_3, x_56);
x_58 = l_BitVec_uaddOverflow(x_3, x_4, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lp_Hax_USize64_add(x_4, x_57);
lean_dec(x_57);
x_37 = x_55;
x_38 = x_59;
goto block_54;
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_57);
x_60 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_60, 0, x_65);
return x_60;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
block_77:
{
uint8_t x_73; 
x_73 = lean_nat_dec_lt(x_72, x_1);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_72);
x_74 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
return x_74;
}
else
{
lean_object* x_75; uint64_t x_76; 
x_75 = lean_array_fget_borrowed(x_2, x_72);
lean_dec(x_72);
x_76 = lean_unbox_uint64(x_75);
x_55 = x_76;
goto block_71;
}
}
block_94:
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_BitVec_ofNat(x_3, x_79);
x_81 = lean_nat_dec_eq(x_1, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_nat_mod(x_78, x_1);
lean_dec(x_78);
x_72 = x_82;
goto block_77;
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_78);
x_83 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_83, 0, x_88);
return x_83;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; uint64_t x_8; uint64_t x_14; lean_object* x_15; uint64_t x_21; uint8_t x_38; 
x_38 = lean_nat_dec_lt(x_6, x_4);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
return x_39;
}
else
{
lean_object* x_40; uint64_t x_41; 
x_40 = lean_array_fget_borrowed(x_5, x_6);
x_41 = lean_unbox_uint64(x_40);
x_21 = x_41;
goto block_37;
}
block_13:
{
uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_uint64_xor(x_7, x_8);
x_10 = lean_box_uint64(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_20:
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
x_17 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
return x_17;
}
else
{
lean_object* x_18; uint64_t x_19; 
x_18 = lean_array_fget_borrowed(x_2, x_15);
lean_dec(x_15);
x_19 = lean_unbox_uint64(x_18);
x_7 = x_14;
x_8 = x_19;
goto block_13;
}
}
block_37:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_BitVec_ofNat(x_3, x_22);
x_24 = lean_nat_dec_eq(x_1, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_nat_div(x_6, x_1);
x_14 = x_21;
x_15 = x_25;
goto block_20;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_theta(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = ((lean_object*)(lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___closed__0));
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_unsigned_to_nat(64u);
x_5 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3;
x_6 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(lean_box(0), x_5, x_3);
lean_dec_ref(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__2___boxed), 4, 3);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_4);
x_10 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(lean_box(0), x_5, x_9);
lean_dec_ref(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
x_14 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__3___boxed), 6, 5);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_1);
x_15 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(lean_box(0), x_13, x_14);
lean_dec_ref(x_14);
return x_15;
}
}
}
}
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 3;
x_2 = lp_Hax_RustM_fail___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_22; 
x_22 = lean_nat_dec_lt(x_3, x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1;
return x_23;
}
else
{
lean_object* x_24; uint64_t x_25; 
x_24 = lean_array_fget_borrowed(x_2, x_3);
x_25 = lean_unbox_uint64(x_24);
x_4 = x_25;
goto block_21;
}
block_21:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___closed__0;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; 
x_17 = lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS;
x_18 = lean_array_fget(x_17, x_3);
x_19 = lean_unbox_uint32(x_18);
lean_dec(x_18);
x_20 = lp_libcrux__sha3_core__models_num_Impl__9_rotate__left(x_4, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_rho(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
x_3 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(lean_box(0), x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_pi___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_22; lean_object* x_23; lean_object* x_38; lean_object* x_39; lean_object* x_55; uint8_t x_70; 
x_3 = lean_unsigned_to_nat(64u);
x_4 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3;
x_70 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_nat_div(x_2, x_4);
x_55 = x_71;
goto block_69;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
block_21:
{
uint8_t x_7; 
x_7 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_nat_mod(x_6, x_4);
lean_dec(x_6);
x_9 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_8, x_5);
lean_dec(x_5);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_10 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
block_37:
{
uint8_t x_24; 
x_24 = l_BitVec_uaddOverflow(x_3, x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lp_Hax_USize64_add(x_22, x_23);
lean_dec(x_23);
x_5 = x_22;
x_6 = x_25;
goto block_21;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_22);
x_26 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
block_54:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__2;
x_41 = l_BitVec_umulOverflow(x_3, x_40, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lp_Hax_USize64_mul(x_40, x_39);
lean_dec(x_39);
x_22 = x_38;
x_23 = x_42;
goto block_37;
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_39);
lean_dec(x_38);
x_43 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_43, 0, x_48);
return x_43;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
block_69:
{
uint8_t x_56; 
x_56 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_nat_mod(x_2, x_4);
x_38 = x_55;
x_39 = x_57;
goto block_54;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_55);
x_58 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_58, 0, x_63);
return x_58;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_pi___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_pi___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_pi(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_keccak__f_pi___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
x_4 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(lean_box(0), x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_chi___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_76; lean_object* x_77; uint64_t x_78; lean_object* x_79; lean_object* x_94; lean_object* x_95; lean_object* x_115; uint8_t x_130; 
x_32 = lean_unsigned_to_nat(64u);
x_33 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3;
x_130 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_nat_div(x_2, x_33);
x_115 = x_131;
goto block_129;
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
return x_132;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_132, 0, x_137);
return x_132;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
lean_dec(x_132);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 1, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_139);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
block_31:
{
lean_object* x_7; 
x_7 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_dec_ref(x_8);
return x_7;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_unbox_uint64(x_12);
lean_dec(x_12);
x_14 = lean_uint64_land(x_3, x_13);
x_15 = lean_uint64_xor(x_5, x_14);
x_16 = lean_box_uint64(x_15);
lean_ctor_set(x_8, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_uint64_land(x_3, x_18);
x_20 = lean_uint64_xor(x_5, x_19);
x_21 = lean_box_uint64(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_24 = x_8;
} else {
 lean_dec_ref(x_8);
 x_24 = lean_box(0);
}
x_25 = lean_unbox_uint64(x_23);
lean_dec(x_23);
x_26 = lean_uint64_land(x_3, x_25);
x_27 = lean_uint64_xor(x_5, x_26);
x_28 = lean_box_uint64(x_27);
if (lean_is_scalar(x_24)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_24;
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
block_51:
{
uint8_t x_38; 
x_38 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_nat_mod(x_37, x_33);
lean_dec(x_37);
x_3 = x_34;
x_4 = x_35;
x_5 = x_36;
x_6 = x_39;
goto block_31;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_35);
x_40 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
block_75:
{
lean_object* x_56; 
x_56 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_55, x_53);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_dec(x_53);
lean_dec(x_52);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
lean_dec(x_53);
lean_dec(x_52);
return x_56;
}
else
{
lean_object* x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; uint8_t x_62; 
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_unbox_uint64(x_58);
lean_dec(x_58);
x_60 = lean_uint64_complement(x_59);
x_61 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__1;
x_62 = l_BitVec_uaddOverflow(x_32, x_52, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lp_Hax_USize64_add(x_52, x_61);
lean_dec(x_52);
x_34 = x_60;
x_35 = x_53;
x_36 = x_54;
x_37 = x_63;
goto block_51;
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_53);
lean_dec(x_52);
x_64 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_64, 0, x_69);
return x_64;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
}
block_93:
{
uint8_t x_80; 
x_80 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_nat_mod(x_79, x_33);
lean_dec(x_79);
x_52 = x_76;
x_53 = x_77;
x_54 = x_78;
x_55 = x_81;
goto block_75;
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
x_82 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_82, 0, x_87);
return x_82;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
block_114:
{
lean_object* x_96; 
x_96 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get(x_1, x_94, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_dec(x_95);
lean_dec(x_94);
return x_96;
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_dec_ref(x_97);
lean_dec(x_95);
lean_dec(x_94);
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec_ref(x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0;
x_100 = l_BitVec_uaddOverflow(x_32, x_94, x_99);
if (x_100 == 0)
{
lean_object* x_101; uint64_t x_102; 
x_101 = lp_Hax_USize64_add(x_94, x_99);
x_102 = lean_unbox_uint64(x_98);
lean_dec(x_98);
x_76 = x_94;
x_77 = x_95;
x_78 = x_102;
x_79 = x_101;
goto block_93;
}
else
{
lean_object* x_103; uint8_t x_104; 
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_94);
x_103 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_103, 0, x_108);
return x_103;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_103, 0);
lean_inc(x_109);
lean_dec(x_103);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
block_129:
{
uint8_t x_116; 
x_116 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0;
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_nat_mod(x_2, x_33);
x_94 = x_115;
x_95 = x_117;
goto block_114;
}
else
{
lean_object* x_118; uint8_t x_119; 
lean_dec(x_115);
x_118 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_118;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_118, 0, x_123);
return x_118;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
lean_dec(x_118);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_chi___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_chi___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_chi(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_keccak__f_chi___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
x_4 = lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0(lean_box(0), x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_4);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lp_libcrux__sha3_hacspec__sha3_keccak__f_rho(x_5);
if (lean_obj_tag(x_6) == 0)
{
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_dec_ref(x_7);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lp_libcrux__sha3_hacspec__sha3_keccak__f_pi(x_8);
if (lean_obj_tag(x_9) == 0)
{
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_10);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lp_libcrux__sha3_hacspec__sha3_keccak__f_chi(x_11);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_dec_ref(x_13);
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota(x_14, x_2);
return x_15;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f___closed__0));
x_3 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_4 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__1;
x_5 = lp_Hax_USize64_fold__range___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
static lean_object* _init_lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 3;
x_2 = lp_Hax_RustM_fail___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_array(x_1, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_79; lean_object* x_119; uint8_t x_125; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_8 = x_3;
} else {
 lean_dec_ref(x_3);
 x_8 = lean_box(0);
}
x_125 = lean_nat_dec_lt(x_1, x_5);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lp_Hax_USize64_sub(x_1, x_5);
x_119 = x_126;
goto block_124;
}
else
{
lean_object* x_127; uint8_t x_128; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_127 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_127, 0, x_132);
return x_127;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
lean_dec(x_127);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
block_78:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lp_libcrux__sha3_rust__primitives_cmp_lt___at___00hacspec__sha3_keccak__f_get_spec_spec__0(x_10, x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
if (lean_is_scalar(x_8)) {
 x_17 = lean_alloc_ctor(0, 3, 0);
} else {
 x_17 = x_8;
}
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_13, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
lean_free_object(x_11);
x_18 = lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_19 = lean_box(0);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 0);
if (lean_is_scalar(x_8)) {
 x_27 = lean_alloc_ctor(0, 3, 0);
} else {
 x_27 = x_8;
}
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
if (lean_is_scalar(x_8)) {
 x_29 = lean_alloc_ctor(0, 3, 0);
} else {
 x_29 = x_8;
}
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_18, 0, x_30);
return x_18;
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_37 = x_31;
} else {
 lean_dec_ref(x_31);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_8)) {
 x_38 = lean_alloc_ctor(0, 3, 0);
} else {
 x_38 = x_8;
}
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set(x_38, 2, x_36);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
if (lean_is_scalar(x_8)) {
 x_43 = lean_alloc_ctor(0, 3, 0);
} else {
 x_43 = x_8;
}
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_7);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_11, 0, x_44);
return x_11;
}
else
{
lean_object* x_45; 
lean_free_object(x_11);
x_45 = lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(x_7);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_46 = lean_box(0);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_8)) {
 x_55 = lean_alloc_ctor(0, 3, 0);
} else {
 x_55 = x_8;
}
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_9);
lean_ctor_set(x_55, 2, x_53);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_48)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_48;
}
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_11, 0);
lean_inc(x_58);
lean_dec(x_11);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_unbox(x_59);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
if (lean_is_scalar(x_8)) {
 x_62 = lean_alloc_ctor(0, 3, 0);
} else {
 x_62 = x_8;
}
lean_ctor_set(x_62, 0, x_10);
lean_ctor_set(x_62, 1, x_9);
lean_ctor_set(x_62, 2, x_7);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; 
lean_dec(x_60);
x_65 = lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(x_7);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_66 = lean_box(0);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_8)) {
 x_75 = lean_alloc_ctor(0, 3, 0);
} else {
 x_75 = x_8;
}
lean_ctor_set(x_75, 0, x_10);
lean_ctor_set(x_75, 1, x_9);
lean_ctor_set(x_75, 2, x_73);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
if (lean_is_scalar(x_68)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_68;
}
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
}
}
block_118:
{
lean_object* x_80; 
x_80 = lp_libcrux__sha3_hacspec__sha3_sponge_squeeze__state(x_7, x_6, x_5, x_79);
lean_dec(x_6);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_81 = lean_box(0);
return x_81;
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_80, 0);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_80, 0, x_86);
return x_80;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_free_object(x_80);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec_ref(x_83);
x_88 = lean_unsigned_to_nat(64u);
x_89 = l_BitVec_uaddOverflow(x_88, x_5, x_79);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lp_Hax_USize64_add(x_5, x_79);
lean_dec(x_79);
lean_dec(x_5);
x_9 = x_87;
x_10 = x_90;
goto block_78;
}
else
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_87);
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_91 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_91, 0, x_96);
return x_91;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_91, 0);
lean_inc(x_97);
lean_dec(x_91);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_80, 0);
lean_inc(x_102);
lean_dec(x_80);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
lean_dec_ref(x_102);
x_108 = lean_unsigned_to_nat(64u);
x_109 = l_BitVec_uaddOverflow(x_108, x_5, x_79);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lp_Hax_USize64_add(x_5, x_79);
lean_dec(x_79);
lean_dec(x_5);
x_9 = x_107;
x_10 = x_110;
goto block_78;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_107);
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_111 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
if (lean_is_scalar(x_113)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_113;
}
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
}
block_124:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lp_libcrux__sha3_rust__primitives_cmp_lt___at___00hacspec__sha3_keccak__f_get_spec_spec__0(x_119, x_2);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_dec(x_119);
x_79 = x_2;
goto block_118;
}
else
{
lean_dec(x_2);
x_79 = x_119;
goto block_118;
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 3;
x_2 = lp_Hax_RustM_fail___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_27; lean_object* x_28; lean_object* x_33; lean_object* x_49; uint8_t x_50; 
x_49 = lean_unsigned_to_nat(64u);
x_50 = l_BitVec_umulOverflow(x_49, x_4, x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lp_Hax_USize64_mul(x_4, x_1);
x_33 = x_51;
goto block_48;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec_ref(x_3);
x_52 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
block_10:
{
lean_object* x_6; 
x_6 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state(x_3, x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_dec_ref(x_7);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(x_8);
return x_9;
}
}
}
block_26:
{
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_3);
x_14 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___closed__0;
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = l_Array_extract___redArg(x_2, x_12, x_11);
x_5 = x_25;
goto block_10;
}
}
block_32:
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_28);
if (x_29 == 0)
{
x_11 = x_28;
x_12 = x_27;
x_13 = x_29;
goto block_26;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_array_get_size(x_2);
x_31 = lean_nat_dec_le(x_28, x_30);
x_11 = x_28;
x_12 = x_27;
x_13 = x_31;
goto block_26;
}
}
block_48:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_unsigned_to_nat(64u);
x_35 = l_BitVec_uaddOverflow(x_34, x_33, x_1);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lp_Hax_USize64_add(x_33, x_1);
x_27 = x_33;
x_28 = x_36;
goto block_32;
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_dec(x_33);
lean_dec_ref(x_3);
x_37 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_24; 
x_24 = l_BitVec_uaddOverflow(x_3, x_4, x_6);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lp_Hax_USize64_add(x_4, x_6);
x_7 = x_25;
goto block_23;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec_ref(x_5);
x_26 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
block_23:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_7);
lean_dec_ref(x_5);
x_10 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_fget_borrowed(x_1, x_7);
lean_dec(x_7);
lean_inc(x_21);
x_22 = lp_Hax_rust__primitives_hax_monomorphized__update__at_update__at__usize___redArg(x_2, x_5, x_6, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0;
x_2 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0___boxed__const__1;
x_3 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(200u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1;
x_3 = lean_box(x_1);
x_4 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(x_2, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(64u);
x_6 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_255; lean_object* x_256; lean_object* x_309; uint8_t x_310; 
lean_free_object(x_6);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec_ref(x_8);
x_13 = lp_Hax_rust__primitives_slice_slice__length___redArg(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__0___boxed), 4, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_inc_ref(x_4);
lean_inc(x_2);
x_255 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___boxed), 4, 2);
lean_closure_set(x_255, 0, x_2);
lean_closure_set(x_255, 1, x_4);
x_309 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_310 = lean_nat_dec_eq(x_2, x_309);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_nat_div(x_15, x_2);
lean_dec(x_15);
x_256 = x_311;
goto block_308;
}
else
{
lean_object* x_312; uint8_t x_313; 
lean_dec_ref(x_255);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_312 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_312, 0);
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
return x_312;
}
else
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_314, 0);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_312, 0, x_317);
return x_312;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_318 = lean_ctor_get(x_312, 0);
lean_inc(x_318);
lean_dec(x_312);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_320 = x_318;
} else {
 lean_dec_ref(x_318);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 1, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_321);
return x_322;
}
}
block_45:
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_19);
x_22 = lp_Hax_USize64_fold__range___redArg(x_18, x_20, x_21, x_16);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_ctor_set(x_25, 0, x_31);
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
block_63:
{
uint8_t x_50; 
x_50 = lean_nat_dec_eq(x_2, x_47);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_nat_div(x_49, x_2);
lean_dec(x_2);
lean_dec(x_49);
x_17 = x_46;
x_18 = x_47;
x_19 = x_48;
x_20 = x_51;
goto block_45;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_16);
lean_dec(x_2);
x_52 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
block_82:
{
uint8_t x_69; 
x_69 = lean_nat_dec_lt(x_68, x_64);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lp_Hax_USize64_sub(x_68, x_64);
lean_dec(x_64);
lean_dec(x_68);
x_46 = x_65;
x_47 = x_66;
x_48 = x_67;
x_49 = x_70;
goto block_63;
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_16);
lean_dec(x_2);
x_71 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_71, 0, x_76);
return x_71;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
lean_dec(x_71);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
block_180:
{
uint8_t x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = 128;
x_92 = lean_uint8_lor(x_90, x_91);
x_93 = lean_box(x_92);
x_94 = lp_Hax_rust__primitives_hax_monomorphized__update__at_update__at__usize___redArg(x_85, x_89, x_84, x_93);
lean_dec(x_84);
lean_dec(x_85);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_dec_ref(x_95);
lean_dec(x_88);
lean_dec_ref(x_86);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = lp_Hax_rust__primitives_unsize___redArg(x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state(x_86, x_99, x_2);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_box(0);
return x_101;
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_100);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_100, 0);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_100, 0, x_106);
return x_100;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_free_object(x_100);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
lean_dec_ref(x_103);
x_108 = lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_box(0);
return x_109;
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_108, 0);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_108, 0, x_114);
return x_108;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_free_object(x_108);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
lean_dec_ref(x_111);
x_116 = lean_box(x_87);
lean_inc(x_1);
x_117 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(x_1, x_116, x_1);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_dec_ref(x_118);
lean_dec(x_115);
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_117;
}
else
{
lean_object* x_119; uint8_t x_120; 
lean_dec(x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = l_BitVec_uaddOverflow(x_5, x_1, x_2);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lp_Hax_USize64_add(x_1, x_2);
lean_dec(x_1);
x_64 = x_83;
x_65 = x_119;
x_66 = x_88;
x_67 = x_115;
x_68 = x_121;
goto block_82;
}
else
{
lean_object* x_122; uint8_t x_123; 
lean_dec(x_119);
lean_dec(x_115);
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
return x_122;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_122, 0, x_127);
return x_122;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_122, 0);
lean_inc(x_128);
lean_dec(x_122);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_129);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
}
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_108, 0);
lean_inc(x_133);
lean_dec(x_108);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
lean_dec_ref(x_133);
x_139 = lean_box(x_87);
lean_inc(x_1);
x_140 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(x_1, x_139, x_1);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_dec_ref(x_141);
lean_dec(x_138);
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_140;
}
else
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = l_BitVec_uaddOverflow(x_5, x_1, x_2);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lp_Hax_USize64_add(x_1, x_2);
lean_dec(x_1);
x_64 = x_83;
x_65 = x_142;
x_66 = x_88;
x_67 = x_138;
x_68 = x_144;
goto block_82;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_142);
lean_dec(x_138);
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
else
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_100, 0);
lean_inc(x_152);
lean_dec(x_100);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_152, 0);
lean_inc(x_157);
lean_dec_ref(x_152);
x_158 = lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_box(0);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
if (lean_is_scalar(x_161)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_161;
}
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
x_166 = lean_ctor_get(x_160, 0);
lean_inc(x_166);
lean_dec_ref(x_160);
x_167 = lean_box(x_87);
lean_inc(x_1);
x_168 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(x_1, x_167, x_1);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_dec_ref(x_169);
lean_dec(x_166);
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_168;
}
else
{
lean_object* x_170; uint8_t x_171; 
lean_dec(x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
x_171 = l_BitVec_uaddOverflow(x_5, x_1, x_2);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lp_Hax_USize64_add(x_1, x_2);
lean_dec(x_1);
x_64 = x_83;
x_65 = x_170;
x_66 = x_88;
x_67 = x_166;
x_68 = x_172;
goto block_82;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_88);
lean_dec(x_83);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 1, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
if (lean_is_scalar(x_175)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_175;
}
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
}
}
}
}
}
}
block_202:
{
uint8_t x_188; 
x_188 = lean_nat_dec_lt(x_187, x_182);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; 
lean_dec(x_187);
lean_dec_ref(x_186);
lean_dec(x_185);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
return x_189;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_189, 0, x_194);
return x_189;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_189, 0);
lean_inc(x_195);
lean_dec(x_189);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
return x_199;
}
}
else
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_array_fget_borrowed(x_186, x_187);
x_201 = lean_unbox(x_200);
x_83 = x_181;
x_84 = x_187;
x_85 = x_182;
x_86 = x_183;
x_87 = x_184;
x_88 = x_185;
x_89 = x_186;
x_90 = x_201;
goto block_180;
}
}
block_231:
{
lean_object* x_210; 
lean_inc(x_207);
x_210 = lp_Hax_USize64_fold__range___redArg(x_207, x_209, x_208, x_206);
if (lean_obj_tag(x_210) == 0)
{
lean_dec(x_209);
lean_dec(x_207);
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_210;
}
else
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
lean_dec_ref(x_211);
lean_dec(x_209);
lean_dec(x_207);
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_210;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec_ref(x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
x_213 = lean_box(x_3);
x_214 = lp_Hax_rust__primitives_hax_monomorphized__update__at_update__at__usize___redArg(x_203, x_212, x_209, x_213);
lean_dec(x_209);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_dec_ref(x_215);
lean_dec(x_207);
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_214;
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
lean_dec(x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0;
x_218 = lean_nat_dec_lt(x_2, x_217);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lp_Hax_USize64_sub(x_2, x_217);
x_181 = x_217;
x_182 = x_203;
x_183 = x_204;
x_184 = x_205;
x_185 = x_207;
x_186 = x_216;
x_187 = x_219;
goto block_202;
}
else
{
lean_object* x_220; uint8_t x_221; 
lean_dec(x_216);
lean_dec(x_207);
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
return x_220;
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_220, 0, x_225);
return x_220;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_220, 0);
lean_inc(x_226);
lean_dec(x_220);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(0, 1, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_227);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
}
}
}
}
}
block_254:
{
lean_object* x_240; uint8_t x_241; 
lean_inc(x_239);
x_240 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__2___boxed), 6, 4);
lean_closure_set(x_240, 0, x_4);
lean_closure_set(x_240, 1, x_233);
lean_closure_set(x_240, 2, x_5);
lean_closure_set(x_240, 3, x_239);
x_241 = lean_nat_dec_lt(x_232, x_239);
if (x_241 == 0)
{
lean_object* x_242; 
x_242 = lp_Hax_USize64_sub(x_232, x_239);
lean_dec(x_239);
lean_dec(x_232);
x_203 = x_234;
x_204 = x_235;
x_205 = x_236;
x_206 = x_240;
x_207 = x_237;
x_208 = x_238;
x_209 = x_242;
goto block_231;
}
else
{
lean_object* x_243; uint8_t x_244; 
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_235);
lean_dec(x_234);
lean_dec(x_232);
lean_dec_ref(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_243 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
return x_243;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_243, 0, x_248);
return x_243;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_249 = lean_ctor_get(x_243, 0);
lean_inc(x_249);
lean_dec(x_243);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(0, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
return x_253;
}
}
}
block_308:
{
lean_object* x_257; lean_object* x_258; 
x_257 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_258 = lp_Hax_USize64_fold__range___redArg(x_257, x_256, x_12, x_255);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
lean_dec(x_256);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_259 = lean_box(0);
return x_259;
}
else
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_258);
if (x_260 == 0)
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_258, 0);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
lean_dec(x_256);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
return x_258;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_258, 0, x_264);
return x_258;
}
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; 
lean_free_object(x_258);
x_265 = lean_ctor_get(x_261, 0);
lean_inc(x_265);
lean_dec_ref(x_261);
x_266 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1;
x_267 = 0;
x_268 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__2;
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
if (lean_obj_tag(x_269) == 0)
{
lean_dec_ref(x_269);
lean_dec(x_265);
lean_dec(x_256);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_268;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_270 = lean_ctor_get(x_13, 0);
lean_inc(x_270);
lean_dec(x_13);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec_ref(x_269);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l_BitVec_umulOverflow(x_5, x_256, x_2);
if (x_273 == 0)
{
lean_object* x_274; 
x_274 = lp_Hax_USize64_mul(x_256, x_2);
lean_dec(x_256);
x_232 = x_272;
x_233 = x_266;
x_234 = x_266;
x_235 = x_265;
x_236 = x_267;
x_237 = x_257;
x_238 = x_271;
x_239 = x_274;
goto block_254;
}
else
{
lean_object* x_275; uint8_t x_276; 
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_265);
lean_dec(x_256);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_275 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_276 = !lean_is_exclusive(x_275);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_275, 0);
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
return x_275;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_275, 0, x_280);
return x_275;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
lean_dec(x_275);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 1, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
}
}
}
else
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_258, 0);
lean_inc(x_286);
lean_dec(x_258);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_256);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_288 = x_286;
} else {
 lean_dec_ref(x_286);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; 
x_291 = lean_ctor_get(x_286, 0);
lean_inc(x_291);
lean_dec_ref(x_286);
x_292 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1;
x_293 = 0;
x_294 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__2;
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_obj_tag(x_295) == 0)
{
lean_dec_ref(x_295);
lean_dec(x_291);
lean_dec(x_256);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_294;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_ctor_get(x_13, 0);
lean_inc(x_296);
lean_dec(x_13);
x_297 = lean_ctor_get(x_295, 0);
lean_inc(x_297);
lean_dec_ref(x_295);
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
lean_dec(x_296);
x_299 = l_BitVec_umulOverflow(x_5, x_256, x_2);
if (x_299 == 0)
{
lean_object* x_300; 
x_300 = lp_Hax_USize64_mul(x_256, x_2);
lean_dec(x_256);
x_232 = x_298;
x_233 = x_292;
x_234 = x_292;
x_235 = x_291;
x_236 = x_293;
x_237 = x_257;
x_238 = x_297;
x_239 = x_300;
goto block_254;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_291);
lean_dec(x_256);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_301 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_302, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 1, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_304);
if (lean_is_scalar(x_303)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_303;
}
lean_ctor_set(x_307, 0, x_306);
return x_307;
}
}
}
}
}
}
}
}
else
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_6, 0);
lean_inc(x_323);
lean_dec(x_6);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 1, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_324);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_326);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_492; lean_object* x_493; lean_object* x_521; uint8_t x_522; 
x_328 = lean_ctor_get(x_323, 0);
lean_inc(x_328);
lean_dec_ref(x_323);
x_329 = lp_Hax_rust__primitives_slice_slice__length___redArg(x_4);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
lean_dec(x_330);
lean_inc(x_2);
lean_inc(x_1);
x_332 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__0___boxed), 4, 2);
lean_closure_set(x_332, 0, x_1);
lean_closure_set(x_332, 1, x_2);
lean_inc_ref(x_4);
lean_inc(x_2);
x_492 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___boxed), 4, 2);
lean_closure_set(x_492, 0, x_2);
lean_closure_set(x_492, 1, x_4);
x_521 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_522 = lean_nat_dec_eq(x_2, x_521);
if (x_522 == 0)
{
lean_object* x_523; 
x_523 = lean_nat_div(x_331, x_2);
lean_dec(x_331);
x_493 = x_523;
goto block_520;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec_ref(x_492);
lean_dec_ref(x_332);
lean_dec(x_331);
lean_dec(x_329);
lean_dec(x_328);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_524 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 x_526 = x_524;
} else {
 lean_dec_ref(x_524);
 x_526 = lean_box(0);
}
x_527 = lean_ctor_get(x_525, 0);
lean_inc(x_527);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_528 = x_525;
} else {
 lean_dec_ref(x_525);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(0, 1, 0);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_527);
if (lean_is_scalar(x_526)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_526;
}
lean_ctor_set(x_530, 0, x_529);
return x_530;
}
block_351:
{
lean_object* x_337; lean_object* x_338; 
lean_inc(x_334);
x_337 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_333);
lean_ctor_set(x_337, 2, x_335);
x_338 = lp_Hax_USize64_fold__range___redArg(x_334, x_336, x_337, x_332);
lean_dec(x_336);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; 
x_339 = lean_box(0);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(0, 1, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_342);
if (lean_is_scalar(x_341)) {
 x_345 = lean_alloc_ctor(1, 1, 0);
} else {
 x_345 = x_341;
}
lean_ctor_set(x_345, 0, x_344);
return x_345;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_346 = lean_ctor_get(x_340, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_347 = x_340;
} else {
 lean_dec_ref(x_340);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(1, 1, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_348);
if (lean_is_scalar(x_341)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_341;
}
lean_ctor_set(x_350, 0, x_349);
return x_350;
}
}
}
block_365:
{
uint8_t x_356; 
x_356 = lean_nat_dec_eq(x_2, x_353);
if (x_356 == 0)
{
lean_object* x_357; 
x_357 = lean_nat_div(x_355, x_2);
lean_dec(x_2);
lean_dec(x_355);
x_333 = x_352;
x_334 = x_353;
x_335 = x_354;
x_336 = x_357;
goto block_351;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec_ref(x_332);
lean_dec(x_2);
x_358 = lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1;
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_360 = x_358;
} else {
 lean_dec_ref(x_358);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_359, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 x_362 = x_359;
} else {
 lean_dec_ref(x_359);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 1, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_361);
if (lean_is_scalar(x_360)) {
 x_364 = lean_alloc_ctor(1, 1, 0);
} else {
 x_364 = x_360;
}
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
}
block_380:
{
uint8_t x_371; 
x_371 = lean_nat_dec_lt(x_370, x_366);
if (x_371 == 0)
{
lean_object* x_372; 
x_372 = lp_Hax_USize64_sub(x_370, x_366);
lean_dec(x_366);
lean_dec(x_370);
x_352 = x_367;
x_353 = x_368;
x_354 = x_369;
x_355 = x_372;
goto block_365;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec(x_366);
lean_dec_ref(x_332);
lean_dec(x_2);
x_373 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_375 = x_373;
} else {
 lean_dec_ref(x_373);
 x_375 = lean_box(0);
}
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_377 = x_374;
} else {
 lean_dec_ref(x_374);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(0, 1, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_376);
if (lean_is_scalar(x_375)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_375;
}
lean_ctor_set(x_379, 0, x_378);
return x_379;
}
}
block_429:
{
uint8_t x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_389 = 128;
x_390 = lean_uint8_lor(x_388, x_389);
x_391 = lean_box(x_390);
x_392 = lp_Hax_rust__primitives_hax_monomorphized__update__at_update__at__usize___redArg(x_383, x_387, x_382, x_391);
lean_dec(x_382);
lean_dec(x_383);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
if (lean_obj_tag(x_393) == 0)
{
lean_dec_ref(x_393);
lean_dec(x_386);
lean_dec_ref(x_384);
lean_dec(x_381);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
return x_392;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_392);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
lean_dec_ref(x_393);
x_395 = lp_Hax_rust__primitives_unsize___redArg(x_394);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec(x_395);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
lean_dec(x_396);
x_398 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state(x_384, x_397, x_2);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
lean_dec(x_386);
lean_dec(x_381);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
x_399 = lean_box(0);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_398, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_401 = x_398;
} else {
 lean_dec_ref(x_398);
 x_401 = lean_box(0);
}
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_386);
lean_dec(x_381);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
x_402 = lean_ctor_get(x_400, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 x_403 = x_400;
} else {
 lean_dec_ref(x_400);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(0, 1, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_402);
if (lean_is_scalar(x_401)) {
 x_405 = lean_alloc_ctor(1, 1, 0);
} else {
 x_405 = x_401;
}
lean_ctor_set(x_405, 0, x_404);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; 
lean_dec(x_401);
x_406 = lean_ctor_get(x_400, 0);
lean_inc(x_406);
lean_dec_ref(x_400);
x_407 = lp_libcrux__sha3_hacspec__sha3_keccak__f_keccak__f(x_406);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; 
lean_dec(x_386);
lean_dec(x_381);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_box(0);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_407, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_410 = x_407;
} else {
 lean_dec_ref(x_407);
 x_410 = lean_box(0);
}
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_386);
lean_dec(x_381);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(0, 1, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_411);
if (lean_is_scalar(x_410)) {
 x_414 = lean_alloc_ctor(1, 1, 0);
} else {
 x_414 = x_410;
}
lean_ctor_set(x_414, 0, x_413);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_410);
x_415 = lean_ctor_get(x_409, 0);
lean_inc(x_415);
lean_dec_ref(x_409);
x_416 = lean_box(x_385);
lean_inc(x_1);
x_417 = lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg(x_1, x_416, x_1);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
if (lean_obj_tag(x_418) == 0)
{
lean_dec_ref(x_418);
lean_dec(x_415);
lean_dec(x_386);
lean_dec(x_381);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
return x_417;
}
else
{
lean_object* x_419; uint8_t x_420; 
lean_dec(x_417);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_dec_ref(x_418);
x_420 = l_BitVec_uaddOverflow(x_5, x_1, x_2);
if (x_420 == 0)
{
lean_object* x_421; 
x_421 = lp_Hax_USize64_add(x_1, x_2);
lean_dec(x_1);
x_366 = x_381;
x_367 = x_419;
x_368 = x_386;
x_369 = x_415;
x_370 = x_421;
goto block_380;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_419);
lean_dec(x_415);
lean_dec(x_386);
lean_dec(x_381);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
x_422 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 x_424 = x_422;
} else {
 lean_dec_ref(x_422);
 x_424 = lean_box(0);
}
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_426 = x_423;
} else {
 lean_dec_ref(x_423);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(0, 1, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_425);
if (lean_is_scalar(x_424)) {
 x_428 = lean_alloc_ctor(1, 1, 0);
} else {
 x_428 = x_424;
}
lean_ctor_set(x_428, 0, x_427);
return x_428;
}
}
}
}
}
}
}
}
block_447:
{
uint8_t x_437; 
x_437 = lean_nat_dec_lt(x_436, x_431);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_436);
lean_dec_ref(x_435);
lean_dec(x_434);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
x_438 = lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0;
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 x_440 = x_438;
} else {
 lean_dec_ref(x_438);
 x_440 = lean_box(0);
}
x_441 = lean_ctor_get(x_439, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 x_442 = x_439;
} else {
 lean_dec_ref(x_439);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(0, 1, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_441);
if (lean_is_scalar(x_440)) {
 x_444 = lean_alloc_ctor(1, 1, 0);
} else {
 x_444 = x_440;
}
lean_ctor_set(x_444, 0, x_443);
return x_444;
}
else
{
lean_object* x_445; uint8_t x_446; 
x_445 = lean_array_fget_borrowed(x_435, x_436);
x_446 = lean_unbox(x_445);
x_381 = x_430;
x_382 = x_436;
x_383 = x_431;
x_384 = x_432;
x_385 = x_433;
x_386 = x_434;
x_387 = x_435;
x_388 = x_446;
goto block_429;
}
}
block_472:
{
lean_object* x_455; 
lean_inc(x_452);
x_455 = lp_Hax_USize64_fold__range___redArg(x_452, x_454, x_453, x_451);
if (lean_obj_tag(x_455) == 0)
{
lean_dec(x_454);
lean_dec(x_452);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
return x_455;
}
else
{
lean_object* x_456; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
if (lean_obj_tag(x_456) == 0)
{
lean_dec_ref(x_456);
lean_dec(x_454);
lean_dec(x_452);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
return x_455;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec_ref(x_455);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
lean_dec_ref(x_456);
x_458 = lean_box(x_3);
x_459 = lp_Hax_rust__primitives_hax_monomorphized__update__at_update__at__usize___redArg(x_448, x_457, x_454, x_458);
lean_dec(x_454);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_dec_ref(x_460);
lean_dec(x_452);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
return x_459;
}
else
{
lean_object* x_461; lean_object* x_462; uint8_t x_463; 
lean_dec(x_459);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec_ref(x_460);
x_462 = lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0;
x_463 = lean_nat_dec_lt(x_2, x_462);
if (x_463 == 0)
{
lean_object* x_464; 
x_464 = lp_Hax_USize64_sub(x_2, x_462);
x_430 = x_462;
x_431 = x_448;
x_432 = x_449;
x_433 = x_450;
x_434 = x_452;
x_435 = x_461;
x_436 = x_464;
goto block_447;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_461);
lean_dec(x_452);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
x_465 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_467 = x_465;
} else {
 lean_dec_ref(x_465);
 x_467 = lean_box(0);
}
x_468 = lean_ctor_get(x_466, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 x_469 = x_466;
} else {
 lean_dec_ref(x_466);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(0, 1, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_468);
if (lean_is_scalar(x_467)) {
 x_471 = lean_alloc_ctor(1, 1, 0);
} else {
 x_471 = x_467;
}
lean_ctor_set(x_471, 0, x_470);
return x_471;
}
}
}
}
}
block_491:
{
lean_object* x_481; uint8_t x_482; 
lean_inc(x_480);
x_481 = lean_alloc_closure((void*)(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__2___boxed), 6, 4);
lean_closure_set(x_481, 0, x_4);
lean_closure_set(x_481, 1, x_474);
lean_closure_set(x_481, 2, x_5);
lean_closure_set(x_481, 3, x_480);
x_482 = lean_nat_dec_lt(x_473, x_480);
if (x_482 == 0)
{
lean_object* x_483; 
x_483 = lp_Hax_USize64_sub(x_473, x_480);
lean_dec(x_480);
lean_dec(x_473);
x_448 = x_475;
x_449 = x_476;
x_450 = x_477;
x_451 = x_481;
x_452 = x_478;
x_453 = x_479;
x_454 = x_483;
goto block_472;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec_ref(x_481);
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec_ref(x_476);
lean_dec(x_475);
lean_dec(x_473);
lean_dec_ref(x_332);
lean_dec(x_2);
lean_dec(x_1);
x_484 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 x_486 = x_484;
} else {
 lean_dec_ref(x_484);
 x_486 = lean_box(0);
}
x_487 = lean_ctor_get(x_485, 0);
lean_inc(x_487);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 x_488 = x_485;
} else {
 lean_dec_ref(x_485);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 1, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_487);
if (lean_is_scalar(x_486)) {
 x_490 = lean_alloc_ctor(1, 1, 0);
} else {
 x_490 = x_486;
}
lean_ctor_set(x_490, 0, x_489);
return x_490;
}
}
block_520:
{
lean_object* x_494; lean_object* x_495; 
x_494 = lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0;
x_495 = lp_Hax_USize64_fold__range___redArg(x_494, x_493, x_328, x_492);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; 
lean_dec(x_493);
lean_dec_ref(x_332);
lean_dec(x_329);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_496 = lean_box(0);
return x_496;
}
else
{
lean_object* x_497; lean_object* x_498; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_498 = x_495;
} else {
 lean_dec_ref(x_495);
 x_498 = lean_box(0);
}
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_493);
lean_dec_ref(x_332);
lean_dec(x_329);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_499 = lean_ctor_get(x_497, 0);
lean_inc(x_499);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 x_500 = x_497;
} else {
 lean_dec_ref(x_497);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(0, 1, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_499);
if (lean_is_scalar(x_498)) {
 x_502 = lean_alloc_ctor(1, 1, 0);
} else {
 x_502 = x_498;
}
lean_ctor_set(x_502, 0, x_501);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_498);
x_503 = lean_ctor_get(x_497, 0);
lean_inc(x_503);
lean_dec_ref(x_497);
x_504 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1;
x_505 = 0;
x_506 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__2;
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
if (lean_obj_tag(x_507) == 0)
{
lean_dec_ref(x_507);
lean_dec(x_503);
lean_dec(x_493);
lean_dec_ref(x_332);
lean_dec(x_329);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_506;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; 
x_508 = lean_ctor_get(x_329, 0);
lean_inc(x_508);
lean_dec(x_329);
x_509 = lean_ctor_get(x_507, 0);
lean_inc(x_509);
lean_dec_ref(x_507);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
lean_dec(x_508);
x_511 = l_BitVec_umulOverflow(x_5, x_493, x_2);
if (x_511 == 0)
{
lean_object* x_512; 
x_512 = lp_Hax_USize64_mul(x_493, x_2);
lean_dec(x_493);
x_473 = x_510;
x_474 = x_504;
x_475 = x_504;
x_476 = x_503;
x_477 = x_505;
x_478 = x_494;
x_479 = x_509;
x_480 = x_512;
goto block_491;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_503);
lean_dec(x_493);
lean_dec_ref(x_332);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_513 = lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2;
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_515 = x_513;
} else {
 lean_dec_ref(x_513);
 x_515 = lean_box(0);
}
x_516 = lean_ctor_get(x_514, 0);
lean_inc(x_516);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 x_517 = x_514;
} else {
 lean_dec_ref(x_514);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(0, 1, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_516);
if (lean_is_scalar(x_515)) {
 x_519 = lean_alloc_ctor(1, 1, 0);
} else {
 x_519 = x_515;
}
lean_ctor_set(x_519, 0, x_518);
return x_519;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_gt___at___00hacspec__sha3_sponge_keccak_spec_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_nat_dec_lt(x_2, x_1);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_rust__primitives_cmp_gt___at___00hacspec__sha3_sponge_keccak_spec_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_rust__primitives_cmp_gt___at___00hacspec__sha3_sponge_keccak_spec_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak_spec(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sponge_keccak_spec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak_spec(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_sha3__224___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__224(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lp_libcrux__sha3_hacspec__sha3_sha3_sha3__224___closed__0;
x_3 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE;
x_4 = 6;
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_sha3__256___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__256(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lp_libcrux__sha3_hacspec__sha3_sha3_sha3__256___closed__0;
x_3 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE;
x_4 = 6;
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_sha3__384___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__384(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lp_libcrux__sha3_hacspec__sha3_sha3_sha3__384___closed__0;
x_3 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE;
x_4 = 6;
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_libcrux__sha3_hacspec__sha3_sha3_sha3__512___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_BitVec_ofNat(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_sha3__512(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lp_libcrux__sha3_hacspec__sha3_sha3_sha3__512___closed__0;
x_3 = lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE;
x_4 = 6;
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake128(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE;
x_4 = 31;
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake128_spec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake128_spec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_hacspec__sha3_sha3_shake128_spec(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake256(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE256__RATE;
x_4 = 31;
x_5 = lp_libcrux__sha3_hacspec__sha3_sponge_keccak(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake256_spec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_libcrux__sha3_hacspec__sha3_sha3_shake256_spec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_libcrux__sha3_hacspec__sha3_sha3_shake256_spec(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Hax_Hax(uint8_t builtin);
lean_object* initialize_libcrux__sha3_Stubs(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do(uint8_t builtin);
lean_object* initialize_Std_Do_Triple(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_libcrux__sha3_extraction_hacspec__sha3(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Hax_Hax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_libcrux__sha3_Stubs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_Triple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__0);
lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__2);
lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_get___closed__3);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__0);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__2);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__3);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__4);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__5);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__6);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__7);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__8);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__9);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__10);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__11);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__12);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__13);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__14);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__15);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__16);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__17);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__18);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__19);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__20);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__21 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__21();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__21);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__22);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__23 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__23();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__23);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__24);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__25 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__25();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__25);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__26 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__26();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__26);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__27 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__27();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS___closed__27);
lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__0);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__2);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__3);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__4);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__5);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__6);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__7);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__8);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__9);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__10);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__11);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__12);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__13);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__14);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__15);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__16);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__17);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__18);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__19);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__20);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__21);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__22);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__23);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__24);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__25);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__26 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__26();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__26);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__27 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__27();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__27);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__28 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__28();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS___closed__28);
lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS);
lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__0);
lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__2 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_iota___closed__2();
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE___closed__0);
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__224__RATE);
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE___closed__0);
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__256__RATE);
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE___closed__0);
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__384__RATE);
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE___closed__0);
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__512__RATE);
lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE___closed__0);
lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE128__RATE);
lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE256__RATE = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE256__RATE();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE256__RATE);
lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__DELIM = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHA3__DELIM();
lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE__DELIM = _init_lp_libcrux__sha3_hacspec__sha3_sha3_SHAKE__DELIM();
lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__0();
lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sponge_lane__index___closed__1);
lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___lam__0___closed__0);
lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__0);
lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__1 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_xor__block__into__state___closed__1();
lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__11 = _init_lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__11();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__11);
lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__12 = _init_lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__12();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__12);
lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__13 = _init_lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__13();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__13);
lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__14 = _init_lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__14();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_createi___at___00hacspec__sha3_keccak__f_theta_spec__0___closed__14);
lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__0);
lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__1 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__1);
lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__2 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__2();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__2);
lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__3 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__3();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_theta___lam__1___closed__3);
lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_keccak__f_rho___lam__0___closed__0);
lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg___closed__0 = _init_lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg___closed__0();
lean_mark_persistent(lp_libcrux__sha3_rust__primitives_hax_repeat___at___00hacspec__sha3_sponge_keccak_spec__0___redArg___closed__0);
lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___lam__1___closed__0);
lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0___boxed__const__1 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0___boxed__const__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0___boxed__const__1);
lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__0);
lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__1);
lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__2 = _init_lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__2();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sponge_keccak___closed__2);
lp_libcrux__sha3_hacspec__sha3_sha3_sha3__224___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_sha3__224___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_sha3__224___closed__0);
lp_libcrux__sha3_hacspec__sha3_sha3_sha3__256___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_sha3__256___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_sha3__256___closed__0);
lp_libcrux__sha3_hacspec__sha3_sha3_sha3__384___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_sha3__384___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_sha3__384___closed__0);
lp_libcrux__sha3_hacspec__sha3_sha3_sha3__512___closed__0 = _init_lp_libcrux__sha3_hacspec__sha3_sha3_sha3__512___closed__0();
lean_mark_persistent(lp_libcrux__sha3_hacspec__sha3_sha3_sha3__512___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
