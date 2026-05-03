// Lean compiler output
// Module: LeanCbcl.R3CorePreservation
// Imports: public import Init public import LeanCbcl.SExpr public import LeanCbcl.Message public import LeanCbcl.Dialect public import LeanCbcl.Agent
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
static lean_object* lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__5;
static lean_object* lp_lean_x2dcbcl_CBCL_verifyR3___closed__0;
static uint8_t lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1___closed__0;
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lp_lean_x2dcbcl_CBCL_isCorePerformativeName(lean_object*);
static lean_object* lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__2;
extern lean_object* lp_lean_x2dcbcl_CBCL_baseResourceBounds;
uint8_t l_List_all___redArg(lean_object*, lean_object*);
static lean_object* lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__6;
static lean_object* lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__0;
static uint8_t lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2___closed__0;
static lean_object* lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__4;
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_verifyR3(lean_object*);
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_verifyR3___lam__0(uint8_t, lean_object*);
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1;
lean_object* lp_lean_x2dcbcl_CBCL_SExpr_sym(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_verifyR3___lam__0___boxed(lean_object*, lean_object*);
static lean_object* lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__1;
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_spoofedBaseDialect;
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_verifyR3___boxed(lean_object*);
static lean_object* lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__3;
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_verifyR3___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lp_lean_x2dcbcl_CBCL_isCorePerformativeName(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
return x_1;
}
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_verifyR3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cbcl-base", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_verifyR3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lp_lean_x2dcbcl_CBCL_verifyR3___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_verifyR3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lp_lean_x2dcbcl_CBCL_verifyR3___closed__0;
x_5 = lean_string_dec_eq(x_2, x_4);
lean_dec_ref(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(lp_lean_x2dcbcl_CBCL_verifyR3___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_List_all___redArg(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_verifyR3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_lean_x2dcbcl_CBCL_verifyR3(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@attacker", 9, 9);
return x_1;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tell", 4, 4);
return x_1;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("spoofed", 7, 7);
return x_1;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__2;
x_2 = lp_lean_x2dcbcl_CBCL_SExpr_sym(x_1);
return x_2;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__3;
x_2 = lean_box(0);
x_3 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lp_lean_x2dcbcl_CBCL_baseResourceBounds;
x_3 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__5;
x_4 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__0;
x_5 = lean_box(0);
x_6 = lp_lean_x2dcbcl_CBCL_verifyR3___closed__0;
x_7 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_5);
lean_ctor_set(x_7, 6, x_1);
lean_ctor_set(x_7, 7, x_1);
lean_ctor_set(x_7, 8, x_1);
return x_7;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect() {
_start:
{
lean_object* x_1; 
x_1 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__6;
return x_1;
}
}
static uint8_t _init_lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect;
x_2 = lp_lean_x2dcbcl_CBCL_verifyR3(x_1);
return x_2;
}
}
static uint8_t _init_lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1___closed__0;
return x_1;
}
}
static uint8_t _init_lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__1;
x_2 = lp_lean_x2dcbcl_CBCL_isCorePerformativeName(x_1);
return x_2;
}
}
static uint8_t _init_lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2() {
_start:
{
uint8_t x_1; 
x_1 = lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_SExpr(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Message(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Dialect(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Agent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dcbcl_LeanCbcl_R3CorePreservation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_SExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Dialect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Agent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_lean_x2dcbcl_CBCL_verifyR3___closed__0 = _init_lp_lean_x2dcbcl_CBCL_verifyR3___closed__0();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_verifyR3___closed__0);
lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__0 = _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__0();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__0);
lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__1 = _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__1();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__1);
lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__2 = _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__2();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__2);
lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__3 = _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__3();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__3);
lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__4 = _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__4();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__4);
lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__5 = _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__5();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__5);
lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__6 = _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__6();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_spoofedBaseDialect___closed__6);
lp_lean_x2dcbcl_CBCL_spoofedBaseDialect = _init_lp_lean_x2dcbcl_CBCL_spoofedBaseDialect();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_spoofedBaseDialect);
lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1___closed__0 = _init_lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1___closed__0();
lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1 = _init_lp_lean_x2dcbcl_CBCL_spoofed__passes__verifyR3___nativeDecide__1__1();
lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2___closed__0 = _init_lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2___closed__0();
lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2 = _init_lp_lean_x2dcbcl_CBCL_spoofed__fails__noCoreRedefinition___nativeDecide__1__2();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
