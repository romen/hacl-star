#include <stdio.h>
#include "Everest_Crypto.h"

int main() {
  uint8_t input[32] = {0};
  uint8_t output[32] = {0};
  uint8_t basepoint[32] = {0x09};

  printf("Input     = ");
  for (int i = 0; i < 32; i++) {
    printf("%02x ", input[i]);
  }
  printf("\n");

  printf("Basepoint = ");
  for (int i = 0; i < 32; i++) {
    printf("%02x ", basepoint[i]);
  }
  printf("\n");

  everestcrypto_openssl_curve25519_scalarmult(output, input, basepoint);

  printf("Result    = ");
  for (int i = 0; i < 32; i++) {
    printf("%02x ", output[i]);
  }
  printf("\n");
  return 0;
}
