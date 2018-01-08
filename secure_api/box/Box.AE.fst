(**
   Box.AE provides cryptographically verified authenticated encryption for use by Box.PKAE. Plaintext types and functions
   to create new plaintext or break the plaintext down to bytes are provided in PlainAE. Some functions and variables are
   only present for purposes of modelling the cryptographic AE game. Of interest for other modules that are not concerned
   with cryptographic verification are coerce_key, leak_key, keygen, encrypt and decrpyt.
*)
module Box.AE

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Monotonic.RRef

open Crypto.Symmetric.Bytes

open Box.Flags
open Box.Plain
open Box.Index
open Box.Key

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap
module SPEC = Spec.SecretBox
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Index


abstract noeq type key_t (pm:plain_module) (im:index_module) (i:id im) =
  | Key: raw:Plain.plain_bytes pm -> key_t pm im i

let create_zero_bytes n =
  Seq.create n (UInt8.uint_to_t 0)

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal KEY module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

(**
  Similar to the leak_key function, get_keyGT provides access to the raw representation of an AE key.
  However, note that the GTot effect only allows use in type refinements and is erased upon extraction.
*)
let get_rawGT #im #am i k =
  k.raw

val raw_key_lemma: #im:index_module -> #am:ae_module im -> i:id im -> k:key #im #am i -> Lemma
  (requires True)
  (ensures (get_rawGT #im #am i k == k.raw))
  [SMTPat (get_rawGT #im #am i k)]
let raw_key_lemma #im #am i k = ()

let recall_logs #im am =
  MR.m_recall am.key_log;
  MR.m_recall am.message_log

let get_message_log_region #im am =
  am.message_log_region

let get_message_logGT #im am =
  am.message_log

let get_ppm #im am = am.ppm
let get_cpm #im am = am.cpm
let get_npm #im am = am.npm
let get_kpm #im am = am.kpm

let compute_cipher_length #im am =
  am.compute_cipher_length
let compute_plain_length #im am =
  am.compute_plain_length

let nonce_is_fresh #im am i n h =
  let _ = () in
  MR.m_contains am.message_log h
  /\ MM.fresh am.message_log (n,i) h

val log_freshness_framing_lemma: #im:index_module -> am:ae_module im -> h0:mem -> h1:mem -> Lemma
  (requires log_freshness_invariant am h0)
  (ensures ((modifies_one h0.tip h0 h1) /\ h0.tip <> root ==> (log_freshness_invariant am h1)))
let log_freshness_framing_lemma #im am h0 h1 =
  //Buffer.lemma_reveal_modifies_0 h0 h1;
  ()

#set-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 0"
let lemma_nonce_freshness #im am i n h0 h1 =
 ()

let create im rgn key_length ppm cpm kpm npm compute_cipher_length compute_plain_length enc dec enc_low dec_low =
  let klr = new_region rgn in
  let mlr = new_region rgn in
  let kl = MM.alloc #klr #(key_log_key im) #(key_log_range kpm im) #(key_log_inv kpm im) in
  let ml = MM.alloc #mlr #(message_log_key im npm) #(message_log_range im cpm ppm npm) #(message_log_inv im cpm ppm npm) in
  recall_log im;
  AM key_length ppm cpm kpm npm compute_cipher_length compute_plain_length enc dec enc_low dec_low klr mlr kl ml


assume val boundless_random_bytes: n:nat -> lbytes n

(**
   This function generates a fresh random key. Honest, as well as dishonest ids can be created using keygen. However, note that the adversary can
   only access the raw representation of dishonest keys. The log is created in a fresh region below the ae_key_region.
*)
#reset-options
#set-options "--z3rlimit 2000 --max_ifuel 2 --max_fuel 0"
let gen #im #am i =
  recall_log im;
  MR.m_recall am.message_log;
  MR.m_recall am.key_log;
  match MM.lookup am.key_log i with
  | Some k ->
    k
  | None ->
    let rnd_k = boundless_random_bytes (UInt32.v am.key_length) in
    let k = Key rnd_k in
    recall_log im;
    MR.m_recall am.message_log;
    MR.m_recall am.key_log;
    MM.extend am.key_log i k;
    k

let set #im #am i b =
  Key b

(**
   The coerce function transforms a raw aes_key into an abstract key. Only dishonest ids can be used
   with this function.
*)
let coerce #im #am i raw_k =
  Key raw_k

(**
   The leak_key function transforms an abstract key into a raw aes_key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
let leak #im #am i k =
  k.raw

#set-options "--z3rlimit 5000 --max_ifuel 1 --max_fuel 0"
let instantiate_km #im am =
  let km = Key.create im (UInt32.v am.key_length) key am.kpm (get_rawGT #im #am) (log_freshness_invariant am) (log_freshness_framing_lemma am) (am.key_log_region) (gen #im #am) (set #im #am) (coerce #im #am) (leak #im #am) in
  km

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal AE module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

let encrypt #im am #i nl n k pl p =
  MR.m_recall am.message_log; recall_log im;
  lemma_honest_or_dishonest im i;
  lemma_registered_not_fresh im i;
  let h0 = get() in
  let honest_i = get_honest im i in
  let p' =
    if honest_i && ae_ind_cpa then (
      Plain.bytes_to_plainST am.ppm (create_zero_bytes pl)
    ) else (
      Plain.repr #im #am.ppm #i p)
  in
  let c = am.enc_low p' (Plain.bytes_to_plainST am.kpm k.raw) n in
  MR.m_recall am.message_log;
  recall_log im;
  let n:plain_bytes #am.npm = (Plain.plain_to_bytesST n) in
  let cl = compute_cipher_length am pl in
  MR.m_recall am.message_log; recall_log im;
  let h1 = get() in
  assert(modifies_one h0.tip h0 h1 /\ h0.tip <> root);
  admit();
  log_freshness_framing_lemma #im am h0 h1;
  MM.extend am.message_log (n,i) ((Plain.plain_to_bytesST c),p);
  lemma_registered_not_fresh im i;
  c


let decrypt #im am #i nl n k cl c =
  MR.m_recall am.message_log;
  recall_log im;
  lemma_honest_or_dishonest im i;
  let honest_i = get_honest im i in
  MR.m_recall am.message_log;
  recall_log im;
  if honest_i && ae_int_ctxt then
    let byte_nonce = Plain.plain_to_bytesST n in
    match MM.lookup am.message_log (byte_nonce,i) with
    | Some (c',m') ->
      if c' = (Plain.plain_to_bytesST c) then
        Some m'
      else
        None
    | None -> None
  else
    let p = (am.dec_low c (Plain.bytes_to_plainST am.kpm k.raw) n) in
    match p with
    | Some p' ->
      Some (Plain.coerce #im #am.ppm #i p')
    | None -> None
