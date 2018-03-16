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
#include "Everest_Crypto.h"
#include "Hacl_Curve25519.h"
#include "Hacl_Chacha20.h"
#include "Hacl_Poly1305_64.h"

//
// Curve25519
//

void hacl_curve25519_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint) {
  Hacl_Curve25519_crypto_scalarmult(mypublic, secret, basepoint);
}

//
// Chacha20
//

typedef uint8_t* hacl_chacha20_state;

void hacl_chacha20_setup(hacl_chacha20_state st, uint8_t* k, uint8_t* n, uint32_t c) {
  Hacl_SecureAPI_Chacha20_setup(st, k, n, c);
}

void hacl_chacha20_stream(uint8_t* stream_block, hacl_chacha20_state st) {
  Hacl_SecureAPI_stream(stream_block, st);
}

void hacl_chacha20_stream_finish(uint8_t* stream_block, uint32_t len, hacl_chacha20_state st) {
  Hacl_SecureAPI_stream(stream_block, st);
}

void hacl_chacha20(uint8_t* output, uint8_t* plain, uint32_t len, uint8_t* key, uint8_t* nonce, uint32_t ctr) {
  Hacl_Chacha20_chacha20(output, plain, len, key, nonce, ctr);
}

//
// Poly1305
//

void hacl_poly1305_64(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *key)
  Hacl_Poly1305_64_crypto_onetimeauth(output, input, len, key);
)

void vale_poly1305_64(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *key)
  Hacl_Poly1305_64_crypto_onetimeauth(output, input, len, key);
)