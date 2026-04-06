// Lean compiler output
// Module: equivalence.Spec_Pure_Defs
// Imports: public import Init public import Hax public import Stubs public import extraction.hacspec_sha3
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_get__pure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_get__pure___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_hacspec__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS;
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_ROUND__CONSTANTS__pure;
extern lean_object* lp_hacspec__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS;
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_RHO__OFFSETS__pure;
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat_mk(lean_object*);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_rotate__left__pure(uint64_t, uint32_t);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_rotate__left__pure___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_theta__pure___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_theta__pure___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_theta__pure___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_theta__pure___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_theta__pure___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_theta__pure___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_theta__pure(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_rho__pure___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_rho__pure___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_rho__pure(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_pi__pure___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_pi__pure___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_pi__pure(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint64_t lean_uint64_complement(uint64_t);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_chi__pure___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_chi__pure___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_chi__pure(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_iota__pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_iota__pure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_round__pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_round__pure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___at___00Spec_Pure_keccak__f__pure_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___at___00Spec_Pure_keccak__f__pure_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_keccak__f__pure(lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_lane__index__pure(lean_object*);
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_lane__index__pure___boxed(lean_object*);
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_get__pure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; 
x_4 = lean_unsigned_to_nat(5u);
x_5 = lean_nat_mul(x_4, x_2);
x_6 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_7 = lean_array_fget_borrowed(x_1, x_6);
lean_dec(x_6);
x_8 = lean_unbox_uint64(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_get__pure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lp_hacspec__sha3_Spec_Pure_get__pure(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
static lean_object* _init_lp_hacspec__sha3_Spec_Pure_ROUND__CONSTANTS__pure() {
_start:
{
lean_object* x_1; 
x_1 = lp_hacspec__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS;
return x_1;
}
}
static lean_object* _init_lp_hacspec__sha3_Spec_Pure_RHO__OFFSETS__pure() {
_start:
{
lean_object* x_1; 
x_1 = lp_hacspec__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS;
return x_1;
}
}
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_rotate__left__pure(uint64_t x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; 
x_3 = lean_unsigned_to_nat(64u);
x_4 = lean_uint64_to_nat(x_1);
x_5 = lean_uint32_to_nat(x_2);
x_6 = l_BitVec_rotateLeft(x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_uint64_of_nat_mk(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_rotate__left__pure___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint32_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lp_hacspec__sha3_Spec_Pure_rotate__left__pure(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_theta__pure___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_mod(x_4, x_1);
x_6 = lp_hacspec__sha3_Spec_Pure_get__pure(x_2, x_3, x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_mod(x_7, x_1);
x_9 = lp_hacspec__sha3_Spec_Pure_get__pure(x_2, x_3, x_8);
lean_dec(x_8);
x_10 = lean_uint64_xor(x_6, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_mod(x_11, x_1);
x_13 = lp_hacspec__sha3_Spec_Pure_get__pure(x_2, x_3, x_12);
lean_dec(x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_mod(x_15, x_1);
x_17 = lp_hacspec__sha3_Spec_Pure_get__pure(x_2, x_3, x_16);
lean_dec(x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_unsigned_to_nat(4u);
x_20 = lean_nat_mod(x_19, x_1);
x_21 = lp_hacspec__sha3_Spec_Pure_get__pure(x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_uint64_xor(x_18, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_theta__pure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lp_hacspec__sha3_Spec_Pure_theta__pure___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_theta__pure___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; 
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_nat_mod(x_5, x_1);
lean_dec(x_5);
x_7 = lean_array_fget_borrowed(x_2, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
x_10 = lean_nat_mod(x_9, x_1);
lean_dec(x_9);
x_11 = lean_array_fget_borrowed(x_2, x_10);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_unbox_uint64(x_11);
x_14 = lp_hacspec__sha3_Spec_Pure_rotate__left__pure(x_13, x_12);
x_15 = lean_unbox_uint64(x_7);
x_16 = lean_uint64_xor(x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_theta__pure___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lp_hacspec__sha3_Spec_Pure_theta__pure___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_theta__pure___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_5 = lean_array_fget_borrowed(x_1, x_4);
x_6 = lean_nat_div(x_4, x_2);
x_7 = lean_array_fget_borrowed(x_3, x_6);
lean_dec(x_6);
x_8 = lean_unbox_uint64(x_5);
x_9 = lean_unbox_uint64(x_7);
x_10 = lean_uint64_xor(x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_theta__pure___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lp_hacspec__sha3_Spec_Pure_theta__pure___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_theta__pure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(5u);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(lp_hacspec__sha3_Spec_Pure_theta__pure___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_Array_ofFn___redArg(x_2, x_3);
x_5 = lean_alloc_closure((void*)(lp_hacspec__sha3_Spec_Pure_theta__pure___lam__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Array_ofFn___redArg(x_2, x_5);
x_7 = lean_alloc_closure((void*)(lp_hacspec__sha3_Spec_Pure_theta__pure___lam__2___boxed), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_unsigned_to_nat(25u);
x_9 = l_Array_ofFn___redArg(x_8, x_7);
return x_9;
}
}
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_rho__pure___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint32_t x_7; uint64_t x_8; 
x_3 = lean_array_fget_borrowed(x_1, x_2);
x_4 = lp_hacspec__sha3_hacspec__sha3_keccak__f_RHO__OFFSETS;
x_5 = lean_array_fget(x_4, x_2);
x_6 = lean_unbox_uint64(x_3);
x_7 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_8 = lp_hacspec__sha3_Spec_Pure_rotate__left__pure(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_rho__pure___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lp_hacspec__sha3_Spec_Pure_rho__pure___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_rho__pure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_hacspec__sha3_Spec_Pure_rho__pure___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_unsigned_to_nat(25u);
x_4 = l_Array_ofFn___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_pi__pure___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_nat_div(x_2, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_mod(x_2, x_3);
x_7 = lean_nat_mul(x_5, x_6);
lean_dec(x_6);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
x_9 = lean_nat_mod(x_8, x_3);
lean_dec(x_8);
x_10 = lean_nat_mul(x_3, x_9);
lean_dec(x_9);
x_11 = lean_nat_add(x_10, x_4);
lean_dec(x_4);
lean_dec(x_10);
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
uint64_t x_14; 
lean_dec(x_11);
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; uint64_t x_16; 
x_15 = lean_array_fget_borrowed(x_1, x_11);
lean_dec(x_11);
x_16 = lean_unbox_uint64(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_pi__pure___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lp_hacspec__sha3_Spec_Pure_pi__pure___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_pi__pure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_hacspec__sha3_Spec_Pure_pi__pure___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_unsigned_to_nat(25u);
x_4 = l_Array_ofFn___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint64_t lp_hacspec__sha3_Spec_Pure_chi__pure___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_28; lean_object* x_39; uint8_t x_40; 
x_9 = lean_unsigned_to_nat(5u);
x_10 = lean_nat_div(x_2, x_9);
x_11 = lean_nat_mod(x_2, x_9);
x_12 = lean_nat_mul(x_9, x_10);
x_13 = lean_nat_add(x_12, x_11);
lean_dec(x_12);
x_14 = 0;
x_39 = lean_array_get_size(x_1);
x_40 = lean_nat_dec_lt(x_13, x_39);
if (x_40 == 0)
{
lean_dec(x_13);
x_28 = x_14;
goto block_38;
}
else
{
lean_object* x_41; uint64_t x_42; 
x_41 = lean_array_fget_borrowed(x_1, x_13);
lean_dec(x_13);
x_42 = lean_unbox_uint64(x_41);
x_28 = x_42;
goto block_38;
}
block_8:
{
uint64_t x_6; uint64_t x_7; 
x_6 = lean_uint64_land(x_4, x_5);
x_7 = lean_uint64_xor(x_3, x_6);
return x_7;
}
block_27:
{
uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_uint64_complement(x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_add(x_10, x_18);
lean_dec(x_10);
x_20 = lean_nat_mod(x_19, x_9);
lean_dec(x_19);
x_21 = lean_nat_mul(x_9, x_20);
lean_dec(x_20);
x_22 = lean_nat_add(x_21, x_11);
lean_dec(x_11);
lean_dec(x_21);
x_23 = lean_array_get_size(x_1);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_22);
x_3 = x_15;
x_4 = x_17;
x_5 = x_14;
goto block_8;
}
else
{
lean_object* x_25; uint64_t x_26; 
x_25 = lean_array_fget_borrowed(x_1, x_22);
lean_dec(x_22);
x_26 = lean_unbox_uint64(x_25);
x_3 = x_15;
x_4 = x_17;
x_5 = x_26;
goto block_8;
}
}
block_38:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_10, x_29);
x_31 = lean_nat_mod(x_30, x_9);
lean_dec(x_30);
x_32 = lean_nat_mul(x_9, x_31);
lean_dec(x_31);
x_33 = lean_nat_add(x_32, x_11);
lean_dec(x_32);
x_34 = lean_array_get_size(x_1);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_dec(x_33);
x_15 = x_28;
x_16 = x_14;
goto block_27;
}
else
{
lean_object* x_36; uint64_t x_37; 
x_36 = lean_array_fget_borrowed(x_1, x_33);
lean_dec(x_33);
x_37 = lean_unbox_uint64(x_36);
x_15 = x_28;
x_16 = x_37;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_chi__pure___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lp_hacspec__sha3_Spec_Pure_chi__pure___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_chi__pure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_hacspec__sha3_Spec_Pure_chi__pure___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_unsigned_to_nat(25u);
x_4 = l_Array_ofFn___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_iota__pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_fget_borrowed(x_1, x_3);
x_5 = lp_hacspec__sha3_hacspec__sha3_keccak__f_ROUND__CONSTANTS;
x_6 = lean_array_fget(x_5, x_2);
x_7 = lean_unbox_uint64(x_4);
x_8 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_9 = lean_uint64_xor(x_7, x_8);
x_10 = lean_box_uint64(x_9);
x_11 = lean_array_fset(x_1, x_3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_iota__pure___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_hacspec__sha3_Spec_Pure_iota__pure(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_round__pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lp_hacspec__sha3_Spec_Pure_theta__pure(x_1);
x_4 = lp_hacspec__sha3_Spec_Pure_rho__pure(x_3);
x_5 = lp_hacspec__sha3_Spec_Pure_pi__pure(x_4);
x_6 = lp_hacspec__sha3_Spec_Pure_chi__pure(x_5);
x_7 = lp_hacspec__sha3_Spec_Pure_iota__pure(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_round__pure___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_hacspec__sha3_Spec_Pure_round__pure(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___at___00Spec_Pure_keccak__f__pure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lp_hacspec__sha3_Spec_Pure_round__pure(x_2, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_2 = x_5;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___at___00Spec_Pure_keccak__f__pure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_hacspec__sha3___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___at___00Spec_Pure_keccak__f__pure_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_keccak__f__pure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(24u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lp_hacspec__sha3___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___at___00Spec_Pure_keccak__f__pure_spec__0(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_lane__index__pure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(5u);
x_3 = lean_nat_mod(x_1, x_2);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_3);
x_5 = lean_nat_div(x_1, x_2);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_hacspec__sha3_Spec_Pure_lane__index__pure___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_hacspec__sha3_Spec_Pure_lane__index__pure(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Hax_Hax(uint8_t builtin);
lean_object* initialize_hacspec__sha3_Stubs(uint8_t builtin);
lean_object* initialize_hacspec__sha3_extraction_hacspec__sha3(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_hacspec__sha3_equivalence_Spec__Pure__Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Hax_Hax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_hacspec__sha3_Stubs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_hacspec__sha3_extraction_hacspec__sha3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_hacspec__sha3_Spec_Pure_ROUND__CONSTANTS__pure = _init_lp_hacspec__sha3_Spec_Pure_ROUND__CONSTANTS__pure();
lean_mark_persistent(lp_hacspec__sha3_Spec_Pure_ROUND__CONSTANTS__pure);
lp_hacspec__sha3_Spec_Pure_RHO__OFFSETS__pure = _init_lp_hacspec__sha3_Spec_Pure_RHO__OFFSETS__pure();
lean_mark_persistent(lp_hacspec__sha3_Spec_Pure_RHO__OFFSETS__pure);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
