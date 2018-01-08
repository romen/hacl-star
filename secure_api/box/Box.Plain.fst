(**
  This module contains the plaintext type of AE and functions to access it.
*)
module Box.Plain

open FStar.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Flags
open Box.Index

module Buffer = FStar.Buffer
module Bytes = Crypto.Symmetric.Bytes

(**
  The protected plaintext type of AE. It is associated with an id and acts as a wrapper around a protected pkae plaintext.
  The ids associated with both plaintexts must be equal.
*)

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
#set-options "--__temp_no_proj Box.Plain"
abstract noeq type plain_module =
  | PM:
    valid_length: (n:nat -> GTot (b:bool{n = 0 ==> false})) ->
    plain_module

let plain (pm:plain_module) = buf:Buffer.buffer UInt8.t{pm.valid_length (Buffer.length buf)}
let plain_bytes (pm:plain_module) = b:Bytes.bytes{pm.valid_length (Seq.length b)}

val valid_length: pm:plain_module -> vl:(n:nat -> GTot (b:bool{n = 0 ==> false})){vl == pm.valid_length}
let valid_length pm =
  pm.valid_length

val valid_plain_length: #pm:plain_module -> p:plain pm -> GTot (b:bool{b <==> pm.valid_length (Buffer.length p)})
let valid_plain_length #pm p =
  pm.valid_length (Buffer.length p)

abstract type protected_plain_t (im:index_module) (pt:Type0) (id:id im) = pt

(**
  Allows changing from one protected type to another without breaking abstraction.
*)
val transmute_protected_plain_t: (#im:index_module) ->
                               (#i:id im) ->
                               (#pt1:Type0) ->
                               (#pt2:Type0) ->
                               (transmute:(pt1 -> pt2)) ->
                               protected_plain_t im pt1 i ->
                               protected_plain_t im pt2 i
let transmute_protected_plain_t #im #i #pt1 #pt2 transmute p1 =
  transmute p1

(**
  The same as transmute_protected_plain_t, just for stateful transmutation functions.
*)
val transmute_protected_plain_tST: (#im:index_module) ->
                               (#i:id im) ->
                               (#pt1:Type0) ->
                               (#pt2:Type0) ->
                               (transmute:(pt1 -> St (pt2))) ->
                               protected_plain_t im pt1 i ->
                               St (protected_plain_t im pt2 i)
let transmute_protected_plain_tST #im #i #pt1 #pt2 transmute p1 =
  transmute p1

val live: #pm:plain_module -> p:plain pm -> h:mem -> t:Type0{t <==> Buffer.live h p}
let live #pm p h = Buffer.live h p

val plain_live: #im:index_module -> #pm:plain_module -> #id:id im -> p:protected_plain_t im (plain pm) id -> h:mem -> t:Type0{t <==> Buffer.live #UInt8.t h p}
let plain_live #im #pm #id p h = Buffer.live #UInt8.t h p

private val cast: #im:index_module -> #i:id im -> #a:Type0 -> p:(protected_plain_t im a i) -> a
let cast #im #i #a p =
  p

#set-options "--z3rlimit 1000 --max_ifuel 2 --max_fuel 1"
val lemma_index_module: im:index_module -> i:id im -> ST unit
  (requires (fun h0 -> registered im i))
  (ensures (fun h0 _ h1 ->
    (honest im i ==> (~(dishonest im i)))
    /\ (dishonest im i ==> (~(honest im i)))
  ))

let lemma_index_module im i =
  lemma_index_module im i

val make_plain_tGT: #im:index_module -> #pm:plain_module -> #i:id im -> protected_plain_t im (plain pm) i -> GTot (p:plain pm)
let make_plain_tGT #im #pm #i p =
  p

val protected_plain_length: #im:index_module -> #pm:plain_module -> #i:id im -> (p:protected_plain_t im (plain pm) i) -> GTot (n:nat{n==Buffer.length (cast p)})
let protected_plain_length #im #pm #i p =
  Buffer.length (cast p)

val plain_length: #pm:plain_module -> len:(plain pm -> GTot nat){len == Buffer.length}
let plain_length #pm = Buffer.length

#set-options "--z3rlimit 1000 --max_ifuel 0 --max_fuel 0"
val plain_to_bytesGT: #pm:plain_module -> wtb:(h:mem -> p:plain pm -> GTot (b:Bytes.bytes{Seq.length b == plain_length p}))
let plain_to_bytesGT #pm =
  FStar.Buffer.as_seq

val plain_to_bytesST: #pm:plain_module -> p:plain pm -> STL (Seq.seq UInt8.t)
  (requires (fun h0 -> Buffer.live h0 p))
  (ensures (fun h0 b h1 ->
    h0 == h1
    /\ Buffer.live h1 p
    /\ Seq.length b = plain_length p
    /\ b == plain_to_bytesGT h1 p
  ))
let plain_to_bytesST #pm p =
  FStar.Buffer.to_seq_full p

#set-options "--z3rlimit 1000 --max_ifuel 1 --max_fuel 1"
val bytes_to_plainST: pm:plain_module -> b:plain_bytes pm -> StackInline (p:plain pm)
  (requires (fun h ->
    0 < normalize_term (Seq.length b)
    /\ normalize_term (Seq.length b) <= UInt.max_int 32
  ))
  (ensures (fun (h0:mem) p h1 ->
     let len = plain_length p in
     len > 0
     /\ ~(Buffer.contains h0 p)
     /\ Buffer.live h1 p /\ Buffer.idx p = 0 /\ plain_length p = len
     /\ Buffer.frameOf p = h0.tip
     /\ Map.domain h1.h == Map.domain h0.h
     /\ Buffer.modifies_0 h0 h1
     /\ plain_to_bytesGT h1 p == b
   ))
let bytes_to_plainST pm b =
  let b_list = FStar.Seq.seq_to_list b in
  let buf:plain pm = FStar.Buffer.createL b_list in
  let b' = Seq.seq_of_list b_list in
  Seq.lemma_seq_list_bij b;
  buf

// Not sure we can prove this with buffers...
//val plain_t_to_bytes_inj_lemma: pm:plain_module -> w:pm.plain_t -> w':pm.plain_t -> Lemma
//  (requires True)
//  (ensures plain_t_to_bytesGT w == plain_t_to_bytesGT w' <==> w == w')
//let plain_t_to_bytes_inj_lemma pm w w' =
//  pm.plain_t_to_bytes_inj_lemma w w'

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
val prot_length_lemma: #im:index_module -> #pm:plain_module -> #i:id im -> p:plain pm -> Lemma
  (requires True)
  (ensures
    (let pp:protected_plain_t im (plain pm) i = p in
    protected_plain_length pp  = plain_length p))
  [SMTPat (protected_plain_length #im #pm #i p)]
let prot_length_lemma #im #pm #i p = ()

val repr: #im:index_module -> #pm:plain_module -> #i:id im{dishonest im i \/ not ae_ind_cpa} -> pp:protected_plain_t im (plain pm) i -> (p:plain pm{protected_plain_length pp = plain_length p})
let repr #im #pm #i p =
  p

val make_prot_plain_tGT: #im:index_module -> #pm:plain_module -> #i:id im -> p:plain pm -> GTot (pp:protected_plain_t im (plain pm) i{protected_plain_length pp = plain_length p})
let make_prot_plain_tGT #im #pm #i p =
  p

val coerce: #im:index_module -> #pm:plain_module -> #i:id im{dishonest im i \/ not ae_int_ctxt} -> p:plain pm -> (pp:protected_plain_t im (plain pm) i{protected_plain_length pp = plain_length p})
let coerce #im #pm #i p =
  p

//val lemma_valid_cipher_length: pm:plain_module -> Lemma (requires True) (ensures pm.valid_cipher_length == valid_cipher_length #pm) [SMTPat (valid_cipher_length #pm)]
//let lemma_valid_cipher_length pm =
//  assert (FStar.FunctionalExtensionality.feq (pm.valid_cipher_length) (valid_cipher_length #pm));
//  ()
//
//val lemma_valid_plain_length: pm:plain_module -> Lemma (requires True) (ensures pm.valid_plain_length == valid_plain_length #pm) [SMTPat (valid_plain_length #pm)]
//let lemma_valid_plain_length pm =
//  assert (FStar.FunctionalExtensionality.feq (pm.valid_plain_length) (valid_plain_length #pm));
//  ()

#set-options "--z3rlimit 1000 --max_ifuel 2 --max_fuel 1"
val create: pm_valid_length: (n:nat -> GTot (b:bool{n = 0 ==> false})) ->
            pm:plain_module{
              pm.valid_length == pm_valid_length
              }

let create valid_length =
  PM valid_length

// We probably don't need this anymore, as plain modules are much simpler now.
//val rec_repr: #im:index_module ->
//              #inner_pm:plain_module ->
//              #pm:plain_module ->
//              #i:id im{dishonest im i \/ not ae_ind_cpa} ->
//              p:protected_plain_t im (plain pm) i
//              -> Tot (plain inner_pm)
//let rec_repr #im #inner_pm #pm #i p =
//  assume(protected_plain_t im (plain pm) i == protected_plain_t im (plain inner_pm) i);
//  repr #im #inner_pm #i p

val message_wrap: #im:index_module -> #inner_pm:plain_module -> #pm:plain_module -> #i:id im -> p:plain inner_pm{protected_plain_t im (plain pm) i === protected_plain_t im (plain inner_pm) i} -> protected_plain_t im (plain pm) i
let message_wrap #im #inner_pm #pm #i p =
  p

val message_unwrap: #im:index_module -> #inner_pm:plain_module -> #pm:plain_module -> #i:id im -> p:(plain pm){protected_plain_t im (plain pm) i === protected_plain_t im (plain inner_pm) i} -> protected_plain_t im (plain inner_pm) i
let message_unwrap #im #inner_pm #pm #i p =
  p
