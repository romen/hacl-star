/* This file auto-generated by KreMLin! */
#ifndef __Hacl_EC_Curve25519_Parameters_H
#define __Hacl_EC_Curve25519_Parameters_H


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
#include "kremlib.h"

void Hacl_EC_Curve25519_Parameters_lemma_max_uint8(Prims_nat n);

void Hacl_EC_Curve25519_Parameters_lemma_max_uint32(Prims_nat n);

void Hacl_EC_Curve25519_Parameters_lemma_max_uint64(Prims_nat n);

void Hacl_EC_Curve25519_Parameters_lemma_max_uint128(Prims_nat n);

extern void *Hacl_EC_Curve25519_Parameters_prime;

extern Prims_pos Hacl_EC_Curve25519_Parameters_platform_size;

extern Prims_pos Hacl_EC_Curve25519_Parameters_platform_wide;

extern Prims_pos Hacl_EC_Curve25519_Parameters_norm_length;

extern uint32_t Hacl_EC_Curve25519_Parameters_nlength;

extern Prims_pos Hacl_EC_Curve25519_Parameters_bytes_length;

extern uint32_t Hacl_EC_Curve25519_Parameters_blength;

Prims_pos Hacl_EC_Curve25519_Parameters_templ(Prims_nat i);

extern Prims_int Hacl_EC_Curve25519_Parameters_a24_;

extern uint64_t Hacl_EC_Curve25519_Parameters_a24;

void Hacl_EC_Curve25519_Parameters_parameters_lemma_0();

void Hacl_EC_Curve25519_Parameters_parameters_lemma_1();
#endif
