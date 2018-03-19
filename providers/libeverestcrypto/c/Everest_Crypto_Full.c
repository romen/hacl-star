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
#include "Everest_Crypto_Full.h"
#include "Hacl_Curve25519.h"
#include "Hacl_Chacha20.h"
#include "Hacl_Poly1305_64.h"
#include "Vale_AES.h"
#include "Vale_Hash_SHA2_256.h"
#include "openssl/curve25519.h"

//
// Curve25519
//

void everestcrypto_hacl_curve25519_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint) {
  Hacl_Curve25519_crypto_scalarmult(mypublic, secret, basepoint);
}

void everestcrypto_openssl_curve25519_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint) {
  X25519(mypublic, secret, basepoint);
}

//
// AES
//

void everestcrypto_vale_aes_keyExpansion(uint8_t *k, uint8_t *w, uint8_t *sb)
{
  Vale_AES_keyExpansion(k, w, sb);
}

void everestcrypto_vale_aes_cipher(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb)
{
  Vale_AES_cipher(out, in, w, sb);
}

//
// Chacha20
//

typedef uint8_t* hacl_chacha20_state;

void everestcrypto_hacl_chacha20_setup(everestcrypto_hacl_chacha20_state st, uint8_t* k, uint8_t* n, uint32_t c) {
  Hacl_SecureAPI_Chacha20_setup(st, k, n, c);
}

void everestcrypto_hacl_chacha20_stream(uint8_t* stream_block, everestcrypto_hacl_chacha20_state st) {
  Hacl_SecureAPI_stream(stream_block, st);
}

void everestcrypto_hacl_chacha20_stream_finish(uint8_t* stream_block, uint32_t len, everestcrypto_hacl_chacha20_state st) {
  Hacl_SecureAPI_stream(stream_block, st);
}

void everestcrypto_hacl_chacha20(uint8_t* output, uint8_t* plain, uint32_t len, uint8_t* key, uint8_t* nonce, uint32_t ctr) {
  Hacl_Chacha20_chacha20(output, plain, len, key, nonce, ctr);
}

//
// Poly1305
//

void everestcrypto_hacl_poly1305_64(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *key) {
  Hacl_Poly1305_64_crypto_onetimeauth(output, input, len, key);
}

void everestcrypto_vale_poly1305_64(uint8_t *output, uint8_t *input, uint64_t len, uint8_t *key) {
  Hacl_Poly1305_64_crypto_onetimeauth(output, input, len, key);
}

//
// SHA2_256
//

void everestcrypto_vale_sha2_256_init(uint32_t *state) {
  Vale_Hash_SHA2_256_init(state);
}

void everestcrypto_vale_sha2_256_update(uint32_t *state, uint8_t *data) {
  Vale_Hash_SHA2_256_update(state, data);
}

void everestcrypto_vale_sha2_256_update_last(uint32_t *state, uint8_t *data, uint32_t *len) {
  Vale_Hash_SHA2_256_update_last(state, data, len);
}

void everestcrypto_vale_sha2_256_finish(uint32_t *state, uint8_t *dst) {
  Vale_Hash_SHA2_256_finish(state, dst);
}
