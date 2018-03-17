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
#ifndef __Everest_Crypto_Full_H
#define __Everest_Crypto_Full_H


typedef uint8_t* hacl_chacha20_state;



//
// Curve25519
//

void crypto_hacl_curve25519_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint);

//
// Chacha20
//

typedef uint8_t* hacl_chacha20_state;

void crypto_hacl_chacha20_setup(hacl_chacha20_state st, uint8_t* k, uint8_t* n, uint32_t c);

void crypto_hacl_chacha20_stream(uint8_t* stream_block, hacl_chacha20_state st);

void crypto_hacl_chacha20_stream_finish(uint8_t* stream_block, uint32_t len, hacl_chacha20_state st);

void crypto_hacl_chacha20(uint8_t* output, uint8_t* plain, uint32_t len, uint8_t* key, uint8_t* nonce, uint32_t ctr);

//
// Poly1305
//

void crypto_hacl_poly1305_64(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *key);

void crypto_vale_poly1305_64(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *key);

//
// SHA2_256
//

void crypto_vale_sha2_256_init(uint32_t *state);

void crypto_vale_sha2_256_update(uint32_t *state, uint8_t *data);

void crypto_vale_sha2_256_update_last(uint32_t *state, uint8_t *data, uint32_t *len);

void crypto_vale_sha2_256_finish(uint32_t *state, uint8_t *dst);

//
// AES
//

void crypto_vale_aes_keyExpansion(uint8_t *k, uint8_t *w, uint8_t *sb);

void crypto_vale_aes_cipher(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb);

#endif
