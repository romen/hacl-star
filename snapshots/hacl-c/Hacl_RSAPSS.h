/* This file was auto-generated by KreMLin! */
#include "kremlib.h"
#ifndef __Hacl_RSAPSS_H
#define __Hacl_RSAPSS_H

bool Hacl_Impl_Lib_eq_b(Prims_nat len, uint32_t clen, uint8_t *b1, uint8_t *b2);

void
Hacl_Impl_Convert_text_to_nat(Prims_nat len, uint32_t clen, uint8_t *input, uint64_t *res);

typedef struct 
{
  uint64_t fst;
  uint64_t snd;
}
K___uint64_t_uint64_t;

extern void Hacl_Impl_MGF_hash_sha256(Prims_nat x0, uint8_t *x1, uint32_t x2, uint8_t *x3);

typedef enum { Hacl_Impl_Multiplication_Positive, Hacl_Impl_Multiplication_Negative }
Hacl_Impl_Multiplication_sign;

void
Hacl_RSAPSS_rsa_pss_sign(
  Prims_nat sLen,
  Prims_nat msgLen,
  uint32_t pow2_i,
  uint32_t iLen,
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint64_t *skey,
  uint32_t ssLen,
  uint8_t *salt,
  uint32_t mmsgLen,
  uint8_t *msg,
  uint8_t *sgnt
);

bool
Hacl_RSAPSS_rsa_pss_verify(
  Prims_nat sLen,
  Prims_nat msgLen,
  uint32_t pow2_i,
  uint32_t iLen,
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t ssLen,
  uint8_t *sgnt,
  uint32_t mmsgLen,
  uint8_t *msg
);

void
Hacl_Impl_Exponentiation_mod_exp(
  Prims_nat nLen,
  uint32_t pow2_i,
  uint32_t iLen,
  uint32_t modBits,
  uint32_t nnLen,
  uint64_t *n1,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);
#endif