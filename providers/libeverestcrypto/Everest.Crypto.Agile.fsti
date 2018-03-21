(* MIT License
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
 *)

module Everest.Crypto.Agile

open FStar.HyperStack.All
open FStar.Buffer

(* Definition: module aliases *)
module B = FStar.Buffer
module S = FStar.Seq

(* Definition: base integer types *)
let uint8 = FStar.UInt8.t
let uint32 = FStar.UInt32.t
let uint64 = FStar.UInt64.t

let uint8_p = FStar.Buffer.buffer uint8
let uint32_p = FStar.Buffer.buffer uint32
let uint64_p = FStar.Buffer.buffer uint64

let lbytes (len:nat) = s:S.seq uint8{S.length s = len}

(* Definition: operator for Buffer/Seq convertions *)
let op_Array_Access m b = as_seq m b


///
/// Everest Configuration
///

val config_p : Type0
///
/// Everest Crypto Provider Initialization
///

val everestcrypto_init: config_p ->
  StackInline unit
    (requires (fun h -> live h config_p))
    (ensures  (fun h0 _ h1 -> live h1 config_p))

///
/// Curve25519
///

val agile_speccurve25519_scalarmult: s:lbytes 32 -> b:lbytes 32 -> o:lbytes 32

val everestcrypto_curve25519_scalarmult:
  config :config_t ->
  mypublic :uint8_p{B.length mypublic = 32} ->
  secret   :uint8_p{B.length secret = 32} ->
  basepoint:uint8_p{B.length basepoint = 32} ->
  Stack unit
    (requires (fun h ->
              B.live h mypublic /\ B.live h secret /\ B.live h basepoint))
    (ensures  (fun h0 _ h1 ->
              B.live h1 mypublic /\ B.modifies_1 mypublic h0 h1
              /\ B.live h0 mypublic /\ B.live h0 secret /\ B.live h0 basepoint
              /\ h1.(mypublic) == agile_speccurve25519_scalarmult h0.(secret) h0.(basepoint)))

///
/// AES
///

val everestcrypto_vale_keyExpansion:
  config :config_t ->
  key:uint8_p ->
  w:uint8_p ->
  sb:uint8_p -> Stack unit
  (requires (fun h -> live h key /\ live h w /\ live h sb))
  (ensures (fun h0 _ h1 -> modifies_1 w h0 h1))

val everestcrypto_vale_cipher:
  config :config_t ->
  out:uint8_p ->
  input:uint8_p ->
  w:uint8_p ->
  sb:uint8_p -> Stack unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ live h sb))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))

///
/// Chacha20
///

let everestcrypto_hacl_chacha20_state = b:B.buffer uint32{B.length b = 16}

val everestcrypto_hacl_chacha20_setup:
  config :config_t ->
  st:everestcrypto_hacl_chacha20_state ->
  k:uint8_p{length k = 32 /\ B.disjoint st k} ->
  n:uint8_p{length n = 12 /\ B.disjoint st n} ->
  c:UInt32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1))

val everestcrypto_chacha20_stream:
  config :config_t ->
  stream_block:uint8_p{length stream_block = 64} ->
  st          :everestcrypto_hacl_chacha20_state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block /\ live h st))
    (ensures  (fun h0 _ h1 -> live h1 stream_block /\ live h0 st
      /\ live h1 st /\ live h0 stream_block /\ modifies_1 stream_block h0 h1))

val everestcrypto_chacha20_stream_finish:
  config :config_t ->
  stream_block:uint8_p ->
  len:uint32{UInt32.v len <= 64 /\ length stream_block = UInt32.v len} ->
  st:everestcrypto_hacl_chacha20_state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block /\ live h st))
    (ensures  (fun h0 _ h1 -> live h1 stream_block /\ live h0 st
      /\ live h1 st /\ live h0 stream_block /\ modifies_1 stream_block h0 h1))

val agile_specchacha20_chacha20_encrypt_bytes : k:lbytes 32 -> n:lbytes 12 -> nat -> p:S.seq uint8 -> c:S.seq uint8{S.length p = S.length c}

val everestcrypto_hacl_chacha20:
  config :config_t ->
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
         h1.(output) == agile_specchacha20_chacha20_encrypt_bytes h0.(key) h0.(nonce) (UInt32.v ctr) h0.(plain)))

///
/// Poly1305_64
///

val agile_spec_poly1305_poly1305: i:S.seq uint8 -> k:S.seq uint8{S.length k = 32} -> m:S.seq uint8{S.length m = 16}

val everestcrypto_hacl_poly1305_64:
  config :config_t ->
  mac:uint8_p{length mac = 16} ->
  input:uint8_p{disjoint input mac} ->
  len:uint64{UInt64.v len < pow2 32 /\ UInt64.v len = length input} ->
  key:uint8_p{disjoint mac key /\ length key = 32} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1 /\ live h0 input /\ live h0 key
      /\ h1.(mac) == agile_spec_poly1305_poly1305 h0.(input) h0.(key)))

val everestcrypto_vale_poly1305_64:
  config :config_t ->
  mac:uint8_p{length mac = 16} ->
  input:uint8_p{disjoint input mac} ->
  len:uint64{UInt64.v len < pow2 32 /\ UInt64.v len = length input} ->
  key:uint8_p{disjoint mac key /\ length key = 32} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1 /\ live h0 input /\ live h0 key))
     // /\ h1.(mac) == agile_specpoly1305_poly1305 h0.(input) h0.(key)))

