// Lean compiler output
// Module: RNPFunctor.Witness
// Imports: Init Mathlib.CategoryTheory.Category.Cat Mathlib.CategoryTheory.DiscreteCategory Mathlib.CategoryTheory.Functor.Basic Found.InterpCore
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
LEAN_EXPORT lean_object* l_RNPFail_Groupoid___boxed(lean_object*);
lean_object* l_CategoryTheory_discreteCategory(lean_object*);
LEAN_EXPORT lean_object* l_RNPFail_Groupoid(uint8_t);
static lean_object* l_RNPFail_Groupoid___closed__1;
LEAN_EXPORT lean_object* l_RNPFail_instInhabitedWitnessZfc;
static lean_object* _init_l_RNPFail_instInhabitedWitnessZfc() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_RNPFail_Groupoid___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_CategoryTheory_discreteCategory(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_RNPFail_Groupoid(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RNPFail_Groupoid___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_RNPFail_Groupoid___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_RNPFail_Groupoid(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Category_Cat(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_DiscreteCategory(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Functor_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Found_InterpCore(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RNPFunctor_Witness(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Category_Cat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_DiscreteCategory(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Functor_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Found_InterpCore(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RNPFail_instInhabitedWitnessZfc = _init_l_RNPFail_instInhabitedWitnessZfc();
lean_mark_persistent(l_RNPFail_instInhabitedWitnessZfc);
l_RNPFail_Groupoid___closed__1 = _init_l_RNPFail_Groupoid___closed__1();
lean_mark_persistent(l_RNPFail_Groupoid___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
