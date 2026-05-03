// Lean compiler output
// Module: LeanCbcl.Agent
// Imports: public import Init public import LeanCbcl.Dialect public import LeanCbcl.Message
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
static lean_object* lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__1;
static lean_object* lp_lean_x2dcbcl_CBCL_Agent_new___closed__0;
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Agent_new(lean_object*);
static lean_object* lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__0;
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
uint8_t lp_lean_x2dcbcl_CBCL_Dialect_definesPerformative(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Agent_installDialect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default;
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* lp_lean_x2dcbcl_CBCL_baseDialect;
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Agent_findPerformativeDialect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Agent_findPerformativeDialect___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_Agent_findPerformativeDialect___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_instInhabitedAgent;
static lean_object* _init_lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default() {
_start:
{
lean_object* x_1; 
x_1 = lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__1;
return x_1;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_instInhabitedAgent() {
_start:
{
lean_object* x_1; 
x_1 = lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default;
return x_1;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_Agent_new___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lp_lean_x2dcbcl_CBCL_baseDialect;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Agent_new(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_lean_x2dcbcl_CBCL_Agent_new___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_Agent_findPerformativeDialect___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lp_lean_x2dcbcl_CBCL_Dialect_definesPerformative(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Agent_findPerformativeDialect___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_lean_x2dcbcl_CBCL_Agent_findPerformativeDialect___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Agent_findPerformativeDialect(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(lp_lean_x2dcbcl_CBCL_Agent_findPerformativeDialect___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_List_reverse___redArg(x_3);
x_6 = l_List_find_x3f___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Agent_installDialect(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_List_appendTR___redArg(x_4, x_6);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_List_appendTR___redArg(x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Dialect(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Message(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dcbcl_LeanCbcl_Agent(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Dialect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__0 = _init_lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__0();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__0);
lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__1 = _init_lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__1();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default___closed__1);
lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default = _init_lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_instInhabitedAgent_default);
lp_lean_x2dcbcl_CBCL_instInhabitedAgent = _init_lp_lean_x2dcbcl_CBCL_instInhabitedAgent();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_instInhabitedAgent);
lp_lean_x2dcbcl_CBCL_Agent_new___closed__0 = _init_lp_lean_x2dcbcl_CBCL_Agent_new___closed__0();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_Agent_new___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
