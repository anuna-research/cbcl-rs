// Lean compiler output
// Module: LeanCbcl
// Imports: public import Init public import LeanCbcl.SExpr public import LeanCbcl.Message public import LeanCbcl.Dialect public import LeanCbcl.Agent public import LeanCbcl.Parser public import LeanCbcl.Serializer public import LeanCbcl.MessageParser public import LeanCbcl.PatternMatch public import LeanCbcl.DialectParser public import LeanCbcl.R1NoRecursion public import LeanCbcl.R2ResourceBounds public import LeanCbcl.R3CorePreservation public import LeanCbcl.Pipeline public import LeanCbcl.TemplateExpansion public import LeanCbcl.DetParser public import LeanCbcl.DeterministicUnion public import LeanCbcl.Lattice.Store public import LeanCbcl.Lattice.Result public import LeanCbcl.DCFLPreservation public import LeanCbcl.Verify
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_SExpr(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Message(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Dialect(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Agent(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Parser(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Serializer(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_MessageParser(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_PatternMatch(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_DialectParser(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_R1NoRecursion(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_R2ResourceBounds(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_R3CorePreservation(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Pipeline(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_TemplateExpansion(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_DetParser(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_DeterministicUnion(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Lattice_Store(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Lattice_Result(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_DCFLPreservation(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Verify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dcbcl_LeanCbcl(uint8_t builtin) {
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
res = initialize_lean_x2dcbcl_LeanCbcl_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Serializer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_MessageParser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_PatternMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_DialectParser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_R1NoRecursion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_R2ResourceBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_R3CorePreservation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Pipeline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_TemplateExpansion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_DetParser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_DeterministicUnion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Lattice_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Lattice_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_DCFLPreservation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dcbcl_LeanCbcl_Verify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
