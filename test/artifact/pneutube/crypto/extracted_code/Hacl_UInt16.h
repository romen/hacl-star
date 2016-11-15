/* This file auto-generated by KreMLin! */
#ifndef __Hacl_UInt16_H
#define __Hacl_UInt16_H


#include "Prims.h"
#include "FStar_Mul.h"
#include "FStar_Squash.h"
#include "FStar_StrongExcludedMiddle.h"
#include "FStar_List_Tot.h"
#include "FStar_Classical.h"
#include "FStar_ListProperties.h"
#include "FStar_SeqProperties.h"
#include "FStar_Math_Lemmas.h"
#include "FStar_BitVector.h"
#include "FStar_UInt.h"
#include "FStar_Int.h"
#include "FStar_FunctionalExtensionality.h"
#include "FStar_PropositionalExtensionality.h"
#include "FStar_PredicateExtensionality.h"
#include "FStar_TSet.h"
#include "FStar_Set.h"
#include "FStar_Map.h"
#include "FStar_Ghost.h"
#include "FStar_All.h"
#include "Hacl_UInt64.h"
#include "Hacl_UInt128.h"
#include "Hacl_UInt32.h"
#include "Hacl_UInt8.h"
#include "Hacl_Cast.h"
#include "FStar_Buffer.h"
#include "FStar_Buffer_Quantifiers.h"
#include "Hacl_EC_Curve25519_Parameters.h"
#include "Hacl_EC_Curve25519_Bigint.h"
#include "Hacl_EC_Curve25519_Utils.h"
#include "Hacl_EC_Curve25519_Bignum_Fproduct.h"
#include "Hacl_EC_Curve25519_Bignum_Fscalar.h"
#include "Hacl_EC_Curve25519_Bignum_Fdifference.h"
#include "Hacl_EC_Curve25519_Bignum_Fsum.h"
#include "Hacl_EC_Curve25519_Bignum_Modulo.h"
#include "Hacl_EC_Curve25519_Bignum.h"
#include "Hacl_EC_Curve25519_PPoint.h"
#include "Hacl_EC_Curve25519_AddAndDouble.h"
#include "kremlib.h"

extern Prims_int Hacl_UInt16_n;

typedef uint16_t Hacl_UInt16_t;

Prims_int Hacl_UInt16_v(uint16_t x);

uint16_t Hacl_UInt16_add(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_add_mod(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_sub(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_sub_mod(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_mul(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_mul_mod(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_logand(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_logxor(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_logor(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_lognot(uint16_t a);

uint16_t Hacl_UInt16_shift_right(uint16_t a, uint32_t s);

uint16_t Hacl_UInt16_shift_left(uint16_t a, uint32_t s);

uint16_t Hacl_UInt16_eq_mask(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_gte_mask(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_gt_mask(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_lt_mask(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_lte_mask(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Plus_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Plus_Percent_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Subtraction_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Subtraction_Percent_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Star_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Star_Percent_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Amp_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Hat_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Bar_Hat(uint16_t a, uint16_t b);

uint16_t Hacl_UInt16_op_Greater_Greater_Hat(uint16_t a, uint32_t s);

uint16_t Hacl_UInt16_op_Less_Less_Hat(uint16_t a, uint32_t s);

extern uint16_t Hacl_UInt16_of_string(Prims_string x0);
#endif
