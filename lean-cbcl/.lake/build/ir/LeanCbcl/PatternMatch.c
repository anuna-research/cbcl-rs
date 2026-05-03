// Lean compiler output
// Module: LeanCbcl.PatternMatch
// Imports: public import Init public import LeanCbcl.SExpr public import LeanCbcl.Message
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
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_substituteBindings_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_List_mapTR_loop___at___00CBCL_substituteBindings_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* lp_lean_x2dcbcl_CBCL_matchPattern___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lp_lean_x2dcbcl_CBCL_isCorePerformativeName(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Bindings_lookup___lam__0___boxed(lean_object*, lean_object*);
uint8_t lp_lean_x2dcbcl_CBCL_instBEqSExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__List_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__List_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_substituteBindings(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lp_lean_x2dcbcl_CBCL_instBEqAtom_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_substituteBindings_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_matchPattern(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___closed__0;
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_Bindings_lookup___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Bindings_lookup(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_lean_x2dcbcl_CBCL_Bindings_lookup___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_string_dec_eq(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Bindings_lookup___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_lean_x2dcbcl_CBCL_Bindings_lookup___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_Bindings_lookup(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(lp_lean_x2dcbcl_CBCL_Bindings_lookup___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_find_x3f___redArg(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
static lean_object* _init_lp_lean_x2dcbcl_CBCL_matchPattern___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_matchPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lp_lean_x2dcbcl_CBCL_matchPattern___closed__0;
x_14 = lean_string_dec_eq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lp_lean_x2dcbcl_CBCL_isCorePerformativeName(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc_ref(x_12);
lean_inc(x_3);
x_16 = lp_lean_x2dcbcl_CBCL_Bindings_lookup(x_3, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
uint8_t x_19; 
lean_free_object(x_4);
lean_dec_ref(x_12);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lp_lean_x2dcbcl_CBCL_instBEqSExpr_beq(x_20, x_2);
lean_dec_ref(x_2);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_16);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lp_lean_x2dcbcl_CBCL_instBEqSExpr_beq(x_23, x_2);
lean_dec_ref(x_2);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_3);
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_3);
return x_26;
}
}
}
}
else
{
lean_free_object(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_2);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_string_dec_eq(x_12, x_29);
lean_dec_ref(x_29);
lean_dec_ref(x_12);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_27);
lean_dec(x_3);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_3);
return x_27;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_string_dec_eq(x_12, x_32);
lean_dec_ref(x_32);
lean_dec_ref(x_12);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_3);
x_34 = lean_box(0);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_3);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec_ref(x_27);
lean_dec_ref(x_12);
lean_dec(x_3);
x_36 = lean_box(0);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec_ref(x_12);
lean_dec(x_3);
lean_dec_ref(x_2);
x_37 = lean_box(0);
return x_37;
}
}
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_2);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = lp_lean_x2dcbcl_CBCL_matchPattern___closed__0;
x_40 = lean_string_dec_eq(x_38, x_39);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = lp_lean_x2dcbcl_CBCL_isCorePerformativeName(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc_ref(x_38);
lean_inc(x_3);
x_42 = lp_lean_x2dcbcl_CBCL_Bindings_lookup(x_3, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_2);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec_ref(x_38);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_48 = lp_lean_x2dcbcl_CBCL_instBEqSExpr_beq(x_46, x_2);
lean_dec_ref(x_2);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_3);
x_49 = lean_box(0);
return x_49;
}
else
{
lean_object* x_50; 
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_3);
return x_50;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_51);
lean_dec_ref(x_2);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_string_dec_eq(x_38, x_52);
lean_dec_ref(x_52);
lean_dec_ref(x_38);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_3);
x_55 = lean_box(0);
return x_55;
}
else
{
lean_object* x_56; 
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_53;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_3);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec_ref(x_51);
lean_dec_ref(x_38);
lean_dec(x_3);
x_57 = lean_box(0);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_38);
lean_dec(x_3);
lean_dec_ref(x_2);
x_58 = lean_box(0);
return x_58;
}
}
}
else
{
lean_object* x_59; 
lean_dec_ref(x_38);
lean_dec_ref(x_2);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_3);
return x_59;
}
}
}
case 4:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_2);
if (lean_obj_tag(x_60) == 4)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_61);
lean_dec_ref(x_4);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_string_dec_eq(x_61, x_63);
lean_dec_ref(x_63);
lean_dec_ref(x_61);
if (x_64 == 0)
{
lean_object* x_65; 
lean_free_object(x_60);
lean_dec(x_3);
x_65 = lean_box(0);
return x_65;
}
else
{
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_3);
return x_60;
}
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_string_dec_eq(x_61, x_66);
lean_dec_ref(x_66);
lean_dec_ref(x_61);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_3);
x_68 = lean_box(0);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_3);
return x_69;
}
}
}
else
{
x_5 = x_60;
x_6 = x_3;
goto block_10;
}
}
else
{
lean_object* x_70; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_70 = lean_box(0);
return x_70;
}
}
default: 
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_71);
lean_dec_ref(x_2);
x_5 = x_71;
x_6 = x_3;
goto block_10;
}
else
{
lean_object* x_72; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = lean_box(0);
return x_72;
}
}
}
block_10:
{
uint8_t x_7; 
x_7 = lp_lean_x2dcbcl_CBCL_instBEqAtom_beq(x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_74) == 0)
{
lean_free_object(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_2, 0);
lean_inc(x_75);
lean_dec_ref(x_2);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_3);
return x_76;
}
else
{
lean_object* x_77; 
lean_dec(x_75);
lean_dec(x_3);
x_77 = lean_box(0);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_box(0);
return x_78;
}
}
else
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_2);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
lean_dec_ref(x_74);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec_ref(x_80);
x_85 = lp_lean_x2dcbcl_CBCL_matchPattern(x_81, x_83, x_3);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_84);
lean_dec(x_82);
lean_free_object(x_2);
lean_free_object(x_1);
return x_85;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
lean_ctor_set(x_2, 0, x_82);
lean_ctor_set(x_1, 0, x_84);
{
lean_object* _tmp_0 = x_2;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_86;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_88; 
lean_free_object(x_2);
lean_dec(x_80);
lean_free_object(x_1);
lean_dec_ref(x_74);
lean_dec(x_3);
x_88 = lean_box(0);
return x_88;
}
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_2, 0);
lean_inc(x_89);
lean_dec(x_2);
if (lean_obj_tag(x_89) == 1)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_74, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_74, 1);
lean_inc(x_91);
lean_dec_ref(x_74);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec_ref(x_89);
x_94 = lp_lean_x2dcbcl_CBCL_matchPattern(x_90, x_92, x_3);
if (lean_obj_tag(x_94) == 0)
{
lean_dec(x_93);
lean_dec(x_91);
lean_free_object(x_1);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_1, 0, x_93);
{
lean_object* _tmp_0 = x_96;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_95;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_98; 
lean_dec(x_89);
lean_free_object(x_1);
lean_dec_ref(x_74);
lean_dec(x_3);
x_98 = lean_box(0);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_free_object(x_1);
lean_dec_ref(x_74);
lean_dec(x_3);
lean_dec_ref(x_2);
x_99 = lean_box(0);
return x_99;
}
}
}
else
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
lean_dec(x_1);
if (lean_obj_tag(x_100) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_2, 0);
lean_inc(x_101);
lean_dec_ref(x_2);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_3);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_101);
lean_dec(x_3);
x_103 = lean_box(0);
return x_103;
}
}
else
{
lean_object* x_104; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_104 = lean_box(0);
return x_104;
}
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_2, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_106 = x_2;
} else {
 lean_dec_ref(x_2);
 x_106 = lean_box(0);
}
if (lean_obj_tag(x_105) == 1)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_100, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_100, 1);
lean_inc(x_108);
lean_dec_ref(x_100);
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec_ref(x_105);
x_111 = lp_lean_x2dcbcl_CBCL_matchPattern(x_107, x_109, x_3);
if (lean_obj_tag(x_111) == 0)
{
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_106);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
if (lean_is_scalar(x_106)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_106;
}
lean_ctor_set(x_113, 0, x_108);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_110);
x_1 = x_113;
x_2 = x_114;
x_3 = x_112;
goto _start;
}
}
else
{
lean_object* x_116; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_100);
lean_dec(x_3);
x_116 = lean_box(0);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec_ref(x_100);
lean_dec(x_3);
lean_dec_ref(x_2);
x_117 = lean_box(0);
return x_117;
}
}
}
}
}
}
static lean_object* _init_lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_ctor_get(x_2, 0);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___closed__0;
x_16 = lean_string_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = lean_apply_4(x_6, x_14, x_3, x_4, lean_box(0));
return x_17;
}
else
{
lean_object* x_18; 
lean_dec_ref(x_14);
lean_dec(x_6);
x_18 = lean_apply_2(x_5, x_3, x_4);
return x_18;
}
}
case 4:
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_19; 
lean_inc_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_3);
if (lean_obj_tag(x_19) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_13);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_19);
x_22 = lean_apply_3(x_7, x_20, x_21, x_4);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_7);
x_23 = lean_apply_6(x_11, x_13, x_19, x_4, lean_box(0), lean_box(0), lean_box(0));
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_7);
x_24 = lean_apply_10(x_12, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_24;
}
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_2);
x_25 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_3);
x_26 = lean_apply_6(x_11, x_13, x_25, x_4, lean_box(0), lean_box(0), lean_box(0));
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_11);
x_27 = lean_apply_10(x_12, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_27;
}
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_29; 
lean_inc(x_28);
lean_dec(x_12);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec_ref(x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_10);
x_30 = lean_apply_1(x_8, x_4);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_8);
x_31 = lean_apply_5(x_10, x_28, x_29, x_4, lean_box(0), lean_box(0));
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_8);
x_32 = lean_apply_10(x_12, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_32;
}
}
else
{
lean_dec(x_8);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_33; 
lean_inc_ref(x_28);
lean_dec(x_12);
lean_dec_ref(x_2);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
lean_dec_ref(x_3);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec_ref(x_28);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec_ref(x_33);
x_38 = lean_apply_5(x_9, x_34, x_35, x_36, x_37, x_4);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_9);
x_39 = lean_apply_5(x_10, x_28, x_33, x_4, lean_box(0), lean_box(0));
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
x_40 = lean_apply_10(x_12, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_ctor_get(x_1, 0);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___closed__0;
x_15 = lean_string_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_apply_4(x_5, x_13, x_2, x_3, lean_box(0));
return x_16;
}
else
{
lean_object* x_17; 
lean_dec_ref(x_13);
lean_dec(x_5);
x_17 = lean_apply_2(x_4, x_2, x_3);
return x_17;
}
}
case 4:
{
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_18; 
lean_inc_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_2);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_12);
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_18);
x_21 = lean_apply_3(x_6, x_19, x_20, x_3);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_6);
x_22 = lean_apply_6(x_10, x_12, x_18, x_3, lean_box(0), lean_box(0), lean_box(0));
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_6);
x_23 = lean_apply_10(x_11, x_1, x_2, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_23;
}
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_2);
x_25 = lean_apply_6(x_10, x_12, x_24, x_3, lean_box(0), lean_box(0), lean_box(0));
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_10);
x_26 = lean_apply_10(x_11, x_1, x_2, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_26;
}
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_8);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_28; 
lean_inc(x_27);
lean_dec(x_11);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec_ref(x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec(x_9);
x_29 = lean_apply_1(x_7, x_3);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_7);
x_30 = lean_apply_5(x_9, x_27, x_28, x_3, lean_box(0), lean_box(0));
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_7);
x_31 = lean_apply_10(x_11, x_1, x_2, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_31;
}
}
else
{
lean_dec(x_7);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_32; 
lean_inc_ref(x_27);
lean_dec(x_11);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_dec_ref(x_2);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec_ref(x_27);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec_ref(x_32);
x_37 = lean_apply_5(x_8, x_33, x_34, x_35, x_36, x_3);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_8);
x_38 = lean_apply_5(x_9, x_27, x_32, x_3, lean_box(0), lean_box(0));
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_8);
x_39 = lean_apply_10(x_11, x_1, x_2, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_apply_2(x_4, x_2, lean_box(0));
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_2(x_4, x_2, lean_box(0));
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_2(x_3, x_1, lean_box(0));
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_2(x_3, x_1, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__5_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_CBCL_substituteBindings(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lp_lean_x2dcbcl_CBCL_Bindings_lookup(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_1;
}
else
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_box(0);
x_10 = lp_lean_x2dcbcl_List_mapTR_loop___at___00CBCL_substituteBindings_spec__0(x_2, x_8, x_9);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lp_lean_x2dcbcl_List_mapTR_loop___at___00CBCL_substituteBindings_spec__0(x_2, x_11, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl_List_mapTR_loop___at___00CBCL_substituteBindings_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lp_lean_x2dcbcl_CBCL_substituteBindings(x_6, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lp_lean_x2dcbcl_CBCL_substituteBindings(x_10, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_substituteBindings_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_2(x_4, x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_4(x_6, x_2, x_3, lean_box(0), lean_box(0));
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_4);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_apply_2(x_5, x_11, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_substituteBindings_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_2(x_3, x_7, x_2);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_2(x_4, x_10, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__List_map__unattach_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_5, x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__List_map__unattach_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_SExpr(uint8_t builtin);
lean_object* initialize_lean_x2dcbcl_LeanCbcl_Message(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dcbcl_LeanCbcl_PatternMatch(uint8_t builtin) {
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
lp_lean_x2dcbcl_CBCL_matchPattern___closed__0 = _init_lp_lean_x2dcbcl_CBCL_matchPattern___closed__0();
lean_mark_persistent(lp_lean_x2dcbcl_CBCL_matchPattern___closed__0);
lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___closed__0 = _init_lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___closed__0();
lean_mark_persistent(lp_lean_x2dcbcl___private_LeanCbcl_PatternMatch_0__CBCL_matchPattern_match__7_splitter___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
