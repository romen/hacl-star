#include <stdio.h>
#include "Everest_Crypto.h"

int main() {
  uint8_t input[32] = {0};
  uint8_t output[32] = {0};
  uint8_t basepoint[32] = {0x09};

  /* printf("Input     = "); */
  /* for (int i = 0; i < 32; i++) { */
  /*   printf("%02x ", input[i]); */
  /* } */
  /* printf("\n"); */

  /* printf("Basepoint = "); */
  /* for (int i = 0; i < 32; i++) { */
  /*   printf("%02x ", basepoint[i]); */
  /* } */
  /* printf("\n"); */

  //
  // OpenSSL / BoringSSL
  //
  everestcrypto_openssl_curve25519_scalarmult(output, input, basepoint);

  printf("Test X25519 BoringSSL = ");
  for (int i = 0; i < 32; i++) {
    printf("%02x ", output[i]);
  }
  printf("\n");

  //
  // HACL*
  //
  everestcrypto_hacl_curve25519_scalarmult(output, input, basepoint);

  printf("Test X25519 HACL*     = ");
  for (int i = 0; i < 32; i++) {
    printf("%02x ", output[i]);
  }
  printf("\n");

  //
  // Vale
  //

  const uint8_t  key[] = { 0xE8, 0xE9, 0xEA, 0xEB, 0xED, 0xEE, 0xEF, 0xF0, 0xF2, 0xF3, 0xF4, 0xF5, 0xF7, 0xF8, 0xF9, 0xFA };
  const uint8_t in[]  =  { 0x01, 0x4B, 0xAF, 0x22, 0x78, 0xA6, 0x9D, 0x33, 0x1D, 0x51, 0x80, 0x10, 0x36, 0x43, 0xE9, 0x9A };
  const uint8_t out[] =  { 0x67, 0x43, 0xC3, 0xD1, 0x51, 0x9A, 0xB4, 0xF2, 0xCD, 0x9A, 0x78, 0xAB, 0x09, 0xA5, 0x11, 0xBD};

  uint8_t sb[1024] = {0};
  uint8_t buffer[16];
  uint8_t expanded_key[176];

  everestcrypto_vale_aes_keyExpansion(key, expanded_key, sb);
  everestcrypto_vale_aes_cipher(buffer, in, expanded_key, sb);

  printf("Test AES Vale         = ");
  for (int i = 0; i < 16; i++) {
    printf("%02x ", buffer[i]);
  }
  printf("\n");

  return 0;
}
