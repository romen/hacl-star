(**
   TODO: - Documentation, some cleanup.
*)
module Box.ODH
open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open Crypto.Symmetric.Bytes

open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HS = FStar.HyperStack
module HH = FStar.HyperHeap
module HSalsa = Spec.HSalsa20
module Curve = Spec.Curve25519
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Index
module LE = FStar.Endianness

let smaller' n i1 i2 =
  let i1' = LE.little_endian i1 in
  let i2' = LE.little_endian i2 in
  i1' < i2'

let smaller om i1 i2 = smaller' om.dh_share_length i1 i2

//let share_from_exponent' dh_exp = Curve.scalarmult dh_exp Curve.base_point

let hash_fun #om = om.hash_low
let dh_exponentiate #om = om.exponentiate_low

//val share_from_exponent: #om:odh_module -> exp:dh_exponent om -> ST (sh:dh_share om)
//      (requires (fun h0 -> True))
//      (ensures (fun h0 res h1 ->
//        Plain.plain_to_bytesGT h1 res == om.exponentiate (Plain.plain_to_bytesGT h1 exp) om.base_point
//        /\ modifies_none h0 h1
//      ))
let share_from_exponent #om exp = om.exponentiate_low exp (get_base_point_low om)
let share_from_exponent_bytes #om exp = om.exponentiate exp (om.base_point)

noeq abstract type pkey' (om:odh_module) =
  | PKEY: pk_share:dh_share_bytes om -> pkey' om

//noeq abstract type skey' (om:odh_module) =
//  | SKEY: sk_exp:dh_exponent om -> pk:pkey' om{Plain.plain_to_bytesGT spm pk.pk_share == om.exponentiate (Plain.plain_to_bytesGT om.epm sk_exp) om.base_point} -> skey' om

noeq abstract type skey' (om:odh_module) =
  | SKEY: sk_exp:dh_exponent_bytes om -> pk:pkey' om -> skey' om

let skey = skey'
let pkey = pkey'

let get_pkey #om sk = sk.pk

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let get_hash_length om = om.hash_length
let get_dh_share_length om = om.dh_share_length
let get_dh_exponent_length om = om.dh_exponent_length
let get_base_point om = om.base_point
let get_index_module om = om.im
let get_key_index_module om = om.kim
let get_key_module om kim = om.km
let get_kpm om = om.kpm
let get_spm om = om.spm
let get_epm om = om.epm

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
let total_order_lemma #om i1 i2 =
  let i1:dh_share_bytes om = i1 in
  let i2:dh_share_bytes om = i2 in
  LE.lemma_little_endian_bij i1 i2

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let create hash_len dh_share_len dh_exp_len kpm spm epm hash hash_low exponentiate exponentiate_low base_point im kim km rgn =
  ODH rgn hash_len dh_share_len dh_exp_len kpm spm epm hash hash_low exponentiate exponentiate_low base_point im kim km

let pk_get_share_bytesGT #om k = k.pk_share

let pk_get_share #om k = Plain.bytes_to_plainST om.spm k.pk_share

let get_skeyGT #om sk =
  sk.sk_exp

let sk_get_share_bytesGT #om sk = sk.pk.pk_share

let sk_get_share #om sk =
  Plain.bytes_to_plainST om.spm sk.pk.pk_share

let compatible_keys #om sk pk =
  pk_get_share_bytesGT #om pk =!= sk_get_share_bytesGT sk

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let leak_skey #om sk =
  sk.sk_exp

assume val boundless_random_bytes: n:nat -> lbytes n

let keygen #om =
  let dh_exponent = boundless_random_bytes om.dh_exponent_length in
  let dh_pk = PKEY (share_from_exponent_bytes dh_exponent) in
  let dh_sk = SKEY dh_exponent dh_pk in
  dh_pk,dh_sk

let coerce_pkey #om dh_sh =
  PKEY dh_sh

let coerce_keypair #om dh_ex =
  let dh_sh = share_from_exponent_bytes #om dh_ex in
  let pk = PKEY dh_sh in
  let sk = SKEY dh_ex pk in
  pk,sk

let compose_ids om s1 s2 =
  if smaller om s1 s2 then
     let i = (s1,s2) in
     i
  else
    (total_order_lemma s1 s2;
    let i = (s2,s1) in
    i)

let prf_odhGT #om sk pk =
  let raw_k = om.exponentiate sk.sk_exp pk.pk_share in
  let k = om.hash raw_k in
  k

let lemma_shares om sk = ()

#set-options "--z3rlimit 1000 --max_ifuel 1 --max_fuel 0"
val prf_odh: om:odh_module -> sk:skey om -> pk:pkey om{compatible_keys sk pk} -> StackInline (k:(Key.get_keytype #om.kim om.km) (compose_ids om (pk_get_share_bytesGT pk) (sk_get_share_bytesGT sk)))
  (requires (fun h0 ->
    let i = compose_ids om (pk_get_share_bytesGT pk) (sk_get_share_bytesGT sk) in
    ID.registered om.kim i
    /\ Key.invariant om.km h0
  ))
  (ensures (fun h0 k h1 ->
    let i = compose_ids om (pk_get_share_bytesGT pk) (sk_get_share_bytesGT sk) in
    let raw = Key.get_rawGT #om.kim om.km i k in
    ((ID.honest om.kim i /\ b2t Flags.prf_odh) ==>
        modifies (Set.singleton (Key.get_log_region om.km)) h0 h1)
    // We should guarantee, that the key is randomly generated. Generally, calls to prf_odh should be idempotent. How to specify that?
    // Should we have a genPost condition that we guarantee here?
    /\ ((ID.dishonest om.kim i \/ ~(b2t Flags.prf_odh)) ==>
        (Plain.plain_to_bytesGT h1 raw == ((prf_odhGT sk pk)) // Functional correctness.
        /\ modifies_none h0 h1))
    /\ (modifies (Set.singleton (Key.get_log_region om.km))h0 h1 \/ modifies_none h0 h1)
    /\ Key.invariant om.km h1
  ))

let prf_odh om sk pk =
  let h0 = get() in
  let i1 = pk.pk_share in
  let i2 = sk.pk.pk_share in
  let i = compose_ids om i1 i2 in
  ID.recall_log om.im;
  ID.recall_log om.kim;
  ID.lemma_honest_or_dishonest om.kim i;
  let honest_i = ID.get_honest om.kim i in
  match honest_i && Flags.prf_odh with
  | true ->
    let k = Key.gen om.km i in
    let h1 = get() in
    Key.invariant_framing_lemma om.km h0 h1;
    k
  | false ->
    let h0 = get() in
    let raw_sk = Plain.bytes_to_plainST om.epm (leak_skey sk) in
    let h1 = get() in
    assert(Key.invariant om.km h1);
    admit();
    let raw_k = om.exponentiate_low raw_sk (pk_get_share pk) in
    let hashed_raw_k = om.hash_low raw_k in
    if not honest_i then
      let h1 = get() in
      Key.invariant_framing_lemma om.km h0 h1;
      assert((ID.dishonest om.kim i \/ ~(b2t Flags.prf_odh)));
      let h1 = get() in
      assert(Key.invariant om.km h1);
      admit();
      Key.coerce om.km i hashed_raw_k
    else
      let h1 = get() in
      Key.invariant_framing_lemma om.km h0 h1;
      //assert(~(ID.dishonest om.kim i \/ ~(b2t Flags.prf_odh)));
      admit();
      Key.set om.km i hashed_raw_k
