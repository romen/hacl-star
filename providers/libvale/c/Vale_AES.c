#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#include "Vale_AES.h"

#ifdef _WIN32
#define STDCALL __attribute__((stdcall))
#else
#define STDCALL
#endif

void Vale_AES_keyExpansion(uint8_t *k, uint8_t *w, uint8_t *sb)
{
  KeyExpansionStdcall(k, w, sb);
}

void Vale_AES_cipher(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb)
{
  AES128EncryptOneBlockStdcall(out, in, w, sb);
}
