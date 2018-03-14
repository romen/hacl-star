#include "stdint.h"


void hacl_curve25519_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint) {
  Hacl_Curve25519_crypto_scalarmult(mypublic, secret, basepoint);
}


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
  Hacle
}


val hacl_chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:uint32{UInt32.v len = length output /\ UInt32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:uint32{UInt32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1 /\
         h1.(output) == spec_chacha20_chacha20_encrypt_bytes h0.(key) h0.(nonce) (UInt32.v ctr) h0.(plain)))
