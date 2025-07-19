// Lean compiler output
// Module: test.AllPathologiesTest
// Imports: Init Gap2.Functor APFunctor.Functor RNPFunctor.Functor Found.WitnessCore
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
LEAN_EXPORT lean_object* _lean_main(lean_object*);
static lean_object* l_main___closed__3;
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
static lean_object* l_main___closed__1;
static lean_object* l_main___closed__4;
static lean_object* l_main___closed__2;
static lean_object* _init_l_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("✓ All pathology functors successfully migrated to WitnessCore API", 67);
return x_1;
}
}
static lean_object* _init_l_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  - Gap₂: ✓", 15);
return x_1;
}
}
static lean_object* _init_l_main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  - AP_Fail₂: ✓", 19);
return x_1;
}
}
static lean_object* _init_l_main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  - RNP_Fail₂: ✓", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_main___closed__1;
x_3 = l_IO_println___at_Lean_instEval___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_main___closed__2;
x_6 = l_IO_println___at_Lean_instEval___spec__1(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_main___closed__3;
x_9 = l_IO_println___at_Lean_instEval___spec__1(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_main___closed__4;
x_12 = l_IO_println___at_Lean_instEval___spec__1(x_11, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gap2_Functor(uint8_t builtin, lean_object*);
lean_object* initialize_APFunctor_Functor(uint8_t builtin, lean_object*);
lean_object* initialize_RNPFunctor_Functor(uint8_t builtin, lean_object*);
lean_object* initialize_Found_WitnessCore(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_test_AllPathologiesTest(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gap2_Functor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_APFunctor_Functor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RNPFunctor_Functor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Found_WitnessCore(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_main___closed__1 = _init_l_main___closed__1();
lean_mark_persistent(l_main___closed__1);
l_main___closed__2 = _init_l_main___closed__2();
lean_mark_persistent(l_main___closed__2);
l_main___closed__3 = _init_l_main___closed__3();
lean_mark_persistent(l_main___closed__3);
l_main___closed__4 = _init_l_main___closed__4();
lean_mark_persistent(l_main___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
void lean_initialize();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  #endif
  lean_object* in; lean_object* res;
lean_initialize();
lean_set_panic_messages(false);
res = initialize_test_AllPathologiesTest(1 /* builtin */, lean_io_mk_world());
lean_set_panic_messages(true);
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
res = _lean_main(lean_io_mk_world());
}
lean_finalize_task_manager();
if (lean_io_result_is_ok(res)) {
  int ret = 0;
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
