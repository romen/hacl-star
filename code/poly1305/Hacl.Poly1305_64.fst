module Hacl.Poly1305_64

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer
open Hacl.Cast

module ST = FStar.HyperStack.ST
module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module I = Hacl.Impl.Poly1305_64
module S = Hacl.Spec.Poly1305_64
module Poly = Hacl.Standalone.Poly1305_64


(* Type Aliases *)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let alloc () =
  I.alloc()

let mk_state r acc = I.mk_state r acc

let init st k =
  let _ = I.poly1305_init_ st (Buffer.sub k 0ul 16ul) in ()

private
let empty_log : I.log_t = Ghost.hide (Seq.createEmpty #Spec.Poly1305.word)

let update_block st m =
  let _ = I.poly1305_update empty_log st m in ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let rec update st m num_blocks =
  if FStar.UInt32.(num_blocks =^ 0ul) then ()
  else
    let block = Buffer.sub m 0ul 16ul in
    let m'    = Buffer.offset m 16ul  in
    let n     = FStar.UInt32.(num_blocks -^ 1ul) in
    let h0    = ST.get () in
    let _ = update_block st block in
    let h1    = ST.get () in
    Buffer.lemma_reveal_modifies_1 (get_accumulator st) h0 h1;
    update st m' n

let update_last st m len =
  I.poly1305_update_last empty_log st (Buffer.sub m 0ul len) (Int.Cast.uint32_to_uint64 len)

let finish st mac k =
  I.poly1305_finish st mac k

let crypto_onetimeauth output input len k = Hacl.Standalone.Poly1305_64.crypto_onetimeauth output input len k
