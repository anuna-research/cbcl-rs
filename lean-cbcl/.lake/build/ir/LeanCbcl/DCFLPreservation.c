// Lean compiler output
// Module: LeanCbcl.DCFLPreservation
// Imports: public import Init public import LeanCbcl.SExpr public import LeanCbcl.Parser public import LeanCbcl.DialectParser
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
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause(lean_object*);
static lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__1;
static lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__0;
static lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__2;
static lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__1;
static lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__2;
static lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__0;
static lean_object* _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("protocol", 8, 8);
return x_1;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shape", 5, 5);
return x_1;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_SExpr(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Parser(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_DialectParser(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dcbcl_LeanCbcl_DCFLPreservation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_SExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_DialectParser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__0 = _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__0();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__0);
lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__1 = _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__1();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__1);
lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__2 = _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__2();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_DCFLPreservation_protocolClause___closed__2);
lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__0 = _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__0();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__0);
lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__1 = _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__1();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__1);
lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__2 = _init_lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__2();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_DCFLPreservation_shapeClause___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
