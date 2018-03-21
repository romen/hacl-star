/* MIT License
 *
 * Copyright (c) 2016-2018 INRIA and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include "stdint.h"
#include "stdbool.h"
#ifndef __Everest_Crypto_Agile_H
#define __Everest_Crypto_Agile_H


struct config_t {
  bool hacl;
  bool vale;
  bool openssl;
  void* fun_everestcrypto_curve25519_scalarmult;
  void* fun_everestcrypto_aes_keyExpansion;
  void* fun_everestcrypto_aes_cipher;
  /* void* fun_everestcrypto_chacha20_setup; */
  /* void* fun_everestcrypto_chacha20_stream; */
  /* void* fun_everestcrypto_chacha20_stream_finish; */
  void* fun_everestcrypto_chacha20;
  void* fun_everestcrypto_poly1305_64;
  void* fun_everestcrypto_sha2_256_init;
  void* fun_everestcrypto_sha2_256_update;
  void* fun_everestcrypto_sha2_256_update_last;
  void* fun_everestcrypto_sha2_256_finish;
};

//
// Top-level Everest Initialization
//

struct config_t* everestcrypto_init();

//
// Curve25519
//

void everestcrypto_curve25519_scalarmult(struct config_t* c, uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint);

//
// AES
//

void everestcrypto_aes_keyExpansion(struct config_t* c, uint8_t *k, uint8_t *w, uint8_t *sb);
void everestcrypto_aes_cipher(struct config_t* c, uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb);

//
// Chacha20
//

void everestcrypto_chacha20(struct config_t* c, uint8_t* output, uint8_t* plain, uint32_t len, uint8_t* key, uint8_t* nonce, uint32_t ctr);

//
// Poly1305
//

void everestcrypto_poly1305_64(struct config_t* c, uint8_t *output, uint8_t *input, uint64_t len, uint8_t *key);

//
// SHA2_256
//

void everestcrypto_sha2_256_init(struct config_t* c, uint32_t *state);
void everestcrypto_sha2_256_update(struct config_t* c, uint32_t *state, uint8_t *data);
void everestcrypto_sha2_256_update_last(struct config_t* c, uint32_t *state, uint8_t *data, uint32_t *len);
void everestcrypto_sha2_256_finish(struct config_t* c, uint32_t *state, uint8_t *dst);

#endif
