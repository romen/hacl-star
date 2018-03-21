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
#include "Everest_Crypto_Agile.h"


/* struct Config { */
/*   bool hacl; */
/*   bool vale; */
/*   bool openssl; */
/*   void* fun_everestcrypto_curve25519_scalarmult; */
/*   void* fun_everestcrypto_aes_keyExpansion; */
/*   void* fun_everestcrypto_aes_cipher; */
/*   /\* void* fun_everestcrypto_chacha20_setup; *\/ */
/*   /\* void* fun_everestcrypto_chacha20_stream; *\/ */
/*   /\* void* fun_everestcrypto_chacha20_stream_finish; *\/ */
/*   void* fun_everestcrypto_chacha20; */
/*   void* fun_everestcrypto_poly1305_64; */
/*   void* fun_everestcrypto_sha2_256_init; */
/*   void* fun_everestcrypto_sha2_256_update; */
/*   void* fun_everestcrypto_sha2_256_update_last; */
/*   void* fun_everestcrypto_sha2_256_finish; */
/* } config_t; */

// Curve25519
void (*pointer_everestcrypto_curve25519_scalarmult)(uint8_t *, uint8_t *, uint8_t *);

// AES
void (*pointer_everestcrypto_aes_keyExpansion)(uint8_t *, uint8_t *, uint8_t *);
void (*pointer_everestcrypto_aes_cipher)(uint8_t *, uint8_t *, uint8_t *, uint8_t *);

// Chacha20
/* void (*pointer_everestcrypto_chacha20_setup)(uint8_t*, uint8_t* , uint8_t* , uint32_t); */
/* void (*pointer_everestcrypto_chacha20_stream)(uint8_t* , uint8_t*); */
/* void (*pointer_everestcrypto_chacha20_stream_finish)(uint8_t* , uint32_t , uint8_t *); */
void (*pointer_everestcrypto_chacha20)(uint8_t * , uint8_t * , uint32_t, uint8_t *, uint8_t *, uint32_t);

// Poly1305
void (*pointer_everestcrypto_poly1305_64)(uint8_t *, uint8_t *, uint64_t, uint8_t *);

// SHA2
void (*pointer_everestcrypto_sha2_256_init)(uint32_t *);
void (*pointer_everestcrypto_sha2_256_update)(uint32_t *, uint8_t *);
void (*pointer_everestcrypto_sha2_256_update_last)(uint32_t *, uint8_t *, uint32_t *);
void (*pointer_everestcrypto_sha2_256_finish)(uint32_t *, uint8_t *);


struct config_t* everestcrypto_init() {
  struct config_t *c = (struct config_t *)malloc(sizeof(struct config_t));
  if (c) {
    if (c->vale) {
      pointer_everestcrypto_curve25519_scalarmult = (void*)&everestcrypto_hacl_curve25519_scalarmult;
      pointer_everestcrypto_aes_keyExpansion = (void*)&everestcrypto_vale_aes_keyExpansion;
      pointer_everestcrypto_aes_cipher = (void*)&everestcrypto_vale_aes_cipher;
      /* pointer_everestcrypto_chacha20_setup = (void*)&everestcrypto_hacl_chacha20_setup; */
      /* pointer_everestcrypto_chacha20_stream = (void*)&everestcrypto_hacl_chacha20_stream; */
      /* pointer_everestcrypto_chacha20_stream_finish = (void*)&everestcrypto_hacl_chacha20_stream_finish; */
      pointer_everestcrypto_chacha20 = (void*)&everestcrypto_chacha20;
      pointer_everestcrypto_poly1305_64 = (void*)&everestcrypto_vale_poly1305_64;
      pointer_everestcrypto_sha2_256_init = (void*)&everestcrypto_vale_sha2_256_init;
      pointer_everestcrypto_sha2_256_update = (void*)&everestcrypto_vale_sha2_256_update;
      pointer_everestcrypto_sha2_256_update_last = (void*)&everestcrypto_vale_sha2_256_update_last;
      pointer_everestcrypto_sha2_256_finish = (void*)&everestcrypto_vale_sha2_256_finish;
    } else if (c->hacl) {
      pointer_everestcrypto_curve25519_scalarmult = (void*)&everestcrypto_hacl_curve25519_scalarmult;
      pointer_everestcrypto_aes_keyExpansion = (void*)&everestcrypto_vale_aes_keyExpansion;
      pointer_everestcrypto_aes_cipher = (void*)&everestcrypto_vale_aes_cipher;
      /* pointer_everestcrypto_chacha20_setup = (void*)&everestcrypto_hacl_chacha20_setup; */
      /* pointer_everestcrypto_chacha20_stream = (void*)&everestcrypto_hacl_chacha20_stream; */
      /* pointer_everestcrypto_chacha20_stream_finish = (void*)&everestcrypto_hacl_chacha20_stream_finish; */
      pointer_everestcrypto_chacha20 = (void*)&everestcrypto_chacha20;
      pointer_everestcrypto_poly1305_64 = (void*)&everestcrypto_vale_poly1305_64;
      pointer_everestcrypto_sha2_256_init = (void*)&everestcrypto_vale_sha2_256_init;
      pointer_everestcrypto_sha2_256_update = (void*)&everestcrypto_vale_sha2_256_update;
      pointer_everestcrypto_sha2_256_update_last = (void*)&everestcrypto_vale_sha2_256_update_last;
      pointer_everestcrypto_sha2_256_finish = (void*)&everestcrypto_vale_sha2_256_finish;
    } else {
      pointer_everestcrypto_curve25519_scalarmult = (void*)&everestcrypto_hacl_curve25519_scalarmult;
      pointer_everestcrypto_aes_keyExpansion = (void*)&everestcrypto_vale_aes_keyExpansion;
      pointer_everestcrypto_aes_cipher = (void*)&everestcrypto_vale_aes_cipher;
      /* pointer_everestcrypto_chacha20_setup = (void*)&everestcrypto_hacl_chacha20_setup; */
      /* pointer_everestcrypto_chacha20_stream = (void*)&everestcrypto_hacl_chacha20_stream; */
      /* pointer_everestcrypto_chacha20_stream_finish = (void*)&everestcrypto_hacl_chacha20_stream_finish; */
      pointer_everestcrypto_chacha20 = (void*)&everestcrypto_chacha20;
      pointer_everestcrypto_poly1305_64 = (void*)&everestcrypto_vale_poly1305_64;
      pointer_everestcrypto_sha2_256_init = (void*)&everestcrypto_vale_sha2_256_init;
      pointer_everestcrypto_sha2_256_update = (void*)&everestcrypto_vale_sha2_256_update;
      pointer_everestcrypto_sha2_256_update_last = (void*)&everestcrypto_vale_sha2_256_update_last;
      pointer_everestcrypto_sha2_256_finish = (void*)&everestcrypto_vale_sha2_256_finish;
    }
  }
  return c;
}


//
// Curve25519
//

void everestcrypto_curve25519_scalarmult(struct config_t* c, uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint) {
  (*c->fun_everestcrypto_curve25519_scalarmult)(mypublic, secret, basepoint);
}

//
// AES
//

void everestcrypto_aes_keyExpansion(struct config_t* c, uint8_t *k, uint8_t *w, uint8_t *sb) {
  (*c->fun_everestcrypto_aes_keyExpansion)(k, w, sb);
}

void everestcrypto_aes_cipher(struct config_t* c, uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb) {
  (*c->fun_everestcrypto_aes_cipher)(out, in, w, sb)
}

//
// Chacha20
//

typedef uint8_t* hacl_chacha20_state;

/* void everestcrypto_hacl_chacha20_setup(struct everestcrypto_hacl_chacha20_state st, uint8_t* k, uint8_t* n, uint32_t c) { */
/*   Hacl_SecureAPI_Chacha20_setup(st, k, n, c); */
/* } */

/* void everestcrypto_hacl_chacha20_stream(uint8_t* stream_block, everestcrypto_hacl_chacha20_state st) { */
/*   Hacl_SecureAPI_stream(stream_block, st); */
/* } */

/* void everestcrypto_hacl_chacha20_stream_finish(struct uint8_t* stream_block, uint32_t len, everestcrypto_hacl_chacha20_state st) { */
/*   Hacl_SecureAPI_stream(stream_block, st); */
/* } */

void everestcrypto_chacha20(struct config_t* c, uint8_t* output, uint8_t* plain, uint32_t len, uint8_t* key, uint8_t* nonce, uint32_t ctr) {
  (*c->fun_everestcrypto_chacha20)(output, plain, len, key, nonce, ctr);
}

//
// Poly1305
//

void everestcrypto_poly1305_64(struct config_t* c, uint8_t *output, uint8_t *input, uint64_t len, uint8_t *key) {
  (*c->everestcrypto_poly1305_64)(output, input, len, key);
}

//
// SHA2_256
//

void everestcrypto_sha2_256_init(struct config_t* c, uint32_t *state) {
  (*c->everestcrypto_sha2_256_init)(state);
}

void everestcrypto_sha2_256_update(struct config_t* c, uint32_t *state, uint8_t *data) {
  (*c->everestcrypto_sha2_256_update)(state, data);
}

void everestcrypto_sha2_256_update_last(struct config_t* c, uint32_t *state, uint8_t *data, uint32_t *len) {
  (*c->everestcrypto_sha2_256_update_last)(state, data, len);
}

void everestcrypto_sha2_256_finish(struct config_t* c, uint32_t *state, uint8_t *dst) {
  (*c->everestcrypto_sha2_256_finish)(state, dst);
}
