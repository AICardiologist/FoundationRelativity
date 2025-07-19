// Lean compiler output
// Module: Found.InterpCore
// Imports: Init Mathlib.CategoryTheory.Category.Basic
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
LEAN_EXPORT lean_object* l_Foundation_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Foundation_toCtorIdx(uint8_t);
static lean_object* l_instSmallCategoryFoundation___closed__1;
LEAN_EXPORT lean_object* l_Foundation_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqInterp___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqInterp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqFoundation(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqInterp(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSmallCategoryFoundation___lambda__2(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSmallCategoryFoundation___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Foundation_ofNat___boxed(lean_object*);
static lean_object* l_instSmallCategoryFoundation___closed__3;
static lean_object* l_instSmallCategoryFoundation___closed__2;
LEAN_EXPORT lean_object* l_Foundation_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqFoundation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Foundation_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_instSmallCategoryFoundation___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqInterp___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133_(uint8_t, uint8_t);
static lean_object* l_Foundation_noConfusion___rarg___closed__1;
LEAN_EXPORT uint8_t l_Foundation_ofNat(lean_object*);
LEAN_EXPORT uint8_t l_instSmallCategoryFoundation___lambda__1(uint8_t);
LEAN_EXPORT lean_object* l_Foundation_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSmallCategoryFoundation;
LEAN_EXPORT lean_object* l_Foundation_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Foundation_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Foundation_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Foundation_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Foundation_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Foundation_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Foundation_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Foundation_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Foundation_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Foundation_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Foundation_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Foundation_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Foundation_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Foundation_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Foundation_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Foundation_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Foundation_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Foundation_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqFoundation(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Foundation_toCtorIdx(x_1);
x_4 = l_Foundation_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqFoundation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instDecidableEqFoundation(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133_(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInterp___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Found_InterpCore_0__decEqInterp____x40_Found_InterpCore___hyg_133____rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInterp(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instDecidableEqInterp___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInterp___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instDecidableEqInterp___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInterp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instDecidableEqInterp(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_instSmallCategoryFoundation___lambda__1(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_instSmallCategoryFoundation___lambda__2(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 2)
{
return x_4;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
static lean_object* _init_l_instSmallCategoryFoundation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instSmallCategoryFoundation___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instSmallCategoryFoundation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instSmallCategoryFoundation___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_instSmallCategoryFoundation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_instSmallCategoryFoundation___closed__1;
x_3 = l_instSmallCategoryFoundation___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_instSmallCategoryFoundation() {
_start:
{
lean_object* x_1; 
x_1 = l_instSmallCategoryFoundation___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_instSmallCategoryFoundation___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instSmallCategoryFoundation___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instSmallCategoryFoundation___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_instSmallCategoryFoundation___lambda__2(x_6, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Category_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Found_InterpCore(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Category_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Foundation_noConfusion___rarg___closed__1 = _init_l_Foundation_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Foundation_noConfusion___rarg___closed__1);
l_instSmallCategoryFoundation___closed__1 = _init_l_instSmallCategoryFoundation___closed__1();
lean_mark_persistent(l_instSmallCategoryFoundation___closed__1);
l_instSmallCategoryFoundation___closed__2 = _init_l_instSmallCategoryFoundation___closed__2();
lean_mark_persistent(l_instSmallCategoryFoundation___closed__2);
l_instSmallCategoryFoundation___closed__3 = _init_l_instSmallCategoryFoundation___closed__3();
lean_mark_persistent(l_instSmallCategoryFoundation___closed__3);
l_instSmallCategoryFoundation = _init_l_instSmallCategoryFoundation();
lean_mark_persistent(l_instSmallCategoryFoundation);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
