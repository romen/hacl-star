/* This file was auto-generated by KreMLin! */
#include "kremlib.h"
#ifndef __Poly1305_32_H
#define __Poly1305_32_H


#include "FStar.h"
#include "testlib.h"

typedef uint32_t Hacl_Bignum_Constants_limb;

typedef uint64_t Hacl_Bignum_Constants_wide;

typedef uint64_t Hacl_Bignum_Wide_t;

typedef uint32_t Hacl_Bignum_Limb_t;

typedef void *Hacl_Impl_Poly1305_32_State_log_t;

typedef uint8_t *Hacl_Impl_Poly1305_32_State_uint8_p;

typedef uint32_t *Hacl_Impl_Poly1305_32_State_bigint;

typedef void *Hacl_Impl_Poly1305_32_State_seqelem;

typedef uint32_t *Hacl_Impl_Poly1305_32_State_elemB;

typedef uint8_t *Hacl_Impl_Poly1305_32_State_wordB;

typedef uint8_t *Hacl_Impl_Poly1305_32_State_wordB_16;

typedef struct 
{
  uint32_t *r;
  uint32_t *h;
}
Hacl_Impl_Poly1305_32_State_poly1305_state;

typedef void *Hacl_Impl_Poly1305_32_log_t;

typedef uint32_t *Hacl_Impl_Poly1305_32_bigint;

typedef uint8_t *Hacl_Impl_Poly1305_32_uint8_p;

typedef uint32_t *Hacl_Impl_Poly1305_32_elemB;

typedef uint8_t *Hacl_Impl_Poly1305_32_wordB;

typedef uint8_t *Hacl_Impl_Poly1305_32_wordB_16;

typedef uint8_t *Poly1305_32_uint8_p;

typedef uint64_t Poly1305_32_uint64_t;

void *Poly1305_32_op_String_Access(FStar_Monotonic_HyperStack_mem h, uint8_t *b);

typedef uint8_t *Poly1305_32_key;

typedef Hacl_Impl_Poly1305_32_State_poly1305_state Poly1305_32_state;

Hacl_Impl_Poly1305_32_State_poly1305_state Poly1305_32_mk_state(uint32_t *r, uint32_t *acc);

void Poly1305_32_init(Hacl_Impl_Poly1305_32_State_poly1305_state st, uint8_t *k1);

extern void *Poly1305_32_empty_log;

void Poly1305_32_update_block(Hacl_Impl_Poly1305_32_State_poly1305_state st, uint8_t *m);

void
Poly1305_32_update(Hacl_Impl_Poly1305_32_State_poly1305_state st, uint8_t *m, uint32_t len1);

void
Poly1305_32_update_last(
  Hacl_Impl_Poly1305_32_State_poly1305_state st,
  uint8_t *m,
  uint32_t len1
);

void
Poly1305_32_finish(Hacl_Impl_Poly1305_32_State_poly1305_state st, uint8_t *mac, uint8_t *k1);

void
Poly1305_32_crypto_onetimeauth(uint8_t *output, uint8_t *input, uint64_t len1, uint8_t *k1);
#endif