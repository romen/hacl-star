module Vale.Crypto.Full

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
/// AES
///

val vale_keyExpansion:
  key:uint8_p ->
  w:uint8_p ->
  sb:uint8_p -> Stack unit
  (requires (fun h -> live h key /\ live h w /\ live h sb))
  (ensures (fun h0 _ h1 -> modifies_1 w h0 h1))

val vale_cipher:
  out:uint8_p ->
  input:uint8_p ->
  w:uint8_p ->
  sb:uint8_p -> Stack unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ live h sb))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))
