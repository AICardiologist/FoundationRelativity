// Lean compiler output
// Module: APFunctor.Functor
// Imports: Init Found.WitnessCore
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
lean_object* l_Found_pathologyFunctor(lean_object*);
static lean_object* l_APFail_AP__Fail_u2082___closed__1;
LEAN_EXPORT lean_object* l_APFail_AP__Fail_u2082;
static lean_object* _init_l_APFail_AP__Fail_u2082___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Found_pathologyFunctor(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_APFail_AP__Fail_u2082() {
_start:
{
lean_object* x_1; 
x_1 = l_APFail_AP__Fail_u2082___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Found_WitnessCore(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_APFunctor_Functor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Found_WitnessCore(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_APFail_AP__Fail_u2082___closed__1 = _init_l_APFail_AP__Fail_u2082___closed__1();
lean_mark_persistent(l_APFail_AP__Fail_u2082___closed__1);
l_APFail_AP__Fail_u2082 = _init_l_APFail_AP__Fail_u2082();
lean_mark_persistent(l_APFail_AP__Fail_u2082);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
