(**
   This module exists to provide type information and functions needed by Box.DH. Box.AE is not imported directly by
   Box.DH to preserve some notion of modularity. If Box.DH should be used with some other module, only Box.PlainDH
   should have to be edited.
*)
module Box.Key

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open Crypto.Symmetric.Bytes

open Box.Flags

module ID = Box.Index
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap
module Plain = Box.Plain

assume val is_random: bytes -> Type0

let index_module = ID.index_module
let plain_module = Plain.plain_module
let id = ID.id

type log_region =
  r:MR.rid{is_eternal_region r}

let key_raw (kpm:plain_module) = Plain.plain_bytes kpm

let check_length (max_length:nat) (n:nat) : GTot bool = n = max_length

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
#set-options "--__temp_no_proj Box.Key"
abstract noeq type key_module (im:index_module) =
  | KM:
    keylen: nat ->
    key_type: (i:id im -> t:Type0) ->
    kpm:plain_module{Plain.valid_length kpm == (check_length keylen)} ->
    get_rawGT: (i:id im -> (k:key_type i) -> GTot (raw:key_raw kpm)) -> // You have to have faith in this function...
    invariant: (h:mem -> t:Type0) -> // Invariant should still hold if only the top of the stack was touched
    invariant_framing_lemma: (h0:mem -> h1:mem -> Lemma
      (requires (invariant h0))
      (ensures ((modifies_one h0.tip h0 h1 /\ h0.tip <> root) ==> invariant h1))
    ) ->
    key_log_region: (rgn:log_region{disjoint rgn (ID.get_rgn im)}) ->
    gen: (i:id im -> ST (k:key_type i) // The spec should indicate that the result is random and that gen is idempotent
      (requires (fun h0 ->
        (ID.fresh im i h0 \/ ID.honest im i)
        /\ invariant h0))
      (ensures  (fun h0 k h1 ->
        invariant h1
        /\ modifies (Set.singleton key_log_region) h0 h1
        ))) ->
    set: ((i:id im {~(Game2? current_game)}) -> (raw:key_raw kpm) -> (k:key_type i{raw == get_rawGT i k})) ->
    coerce: (i:id im{ID.dishonest im i} -> (raw:key_raw kpm) -> (k:key_type i{raw == get_rawGT i k})) ->
    leak: (i:id im{ID.dishonest im i} -> k:key_type i -> (raw:key_raw kpm)) ->
    key_module im

val get_keylen: #im:index_module -> km:key_module im -> n:nat{n = km.keylen}
let get_keylen #im km =
  km.keylen

val get_keytype: #im:index_module -> km:key_module im -> t:(i:id im -> Type0)
let get_keytype #im km =
  km.key_type

val get_pm: #im:index_module -> km:key_module im -> pm:plain_module{pm == km.kpm}
let get_pm #im km = km.kpm

val get_rawGT: #im:index_module -> km:key_module im -> gr:(i:id im -> k:km.key_type i -> GTot (b:key_raw km.kpm)){gr == km.get_rawGT}
let get_rawGT #im km =
  km.get_rawGT

val get_log_region: #im:index_module -> km:key_module im -> rgn:log_region{rgn = km.key_log_region}
let get_log_region #im km =
  km.key_log_region

val gen: (#im:index_module) -> (km:key_module im) -> (i:id im) -> ST (k:km.key_type i)
  (requires (fun h0 ->
    (ID.fresh im i h0 \/ ID.honest im i)
    /\ km.invariant h0))
  (ensures  (fun h0 k h1 ->
    km.invariant h1
    /\ modifies (Set.singleton km.key_log_region) h0 h1
  ))
let gen #im km i =
  km.gen i

val set: (#im:index_module) -> (km:key_module im) -> (i:id im {~(Game2? current_game)}) -> (b:key_raw km.kpm) -> (k:km.key_type i{b == km.get_rawGT i k})
let set #im km i b =
  km.set i b

val coerce: (#im:index_module) -> (km:key_module im) -> (i:id im{ID.dishonest im i}) -> (b:key_raw km.kpm) -> (k:km.key_type i{b == km.get_rawGT i k})
let coerce #im km i b =
  km.coerce i b

val leak: #im:index_module -> (km:key_module im) -> i:id im{ID.dishonest im i} -> (k:km.key_type i) -> (b:key_raw km.kpm)
let leak #im km k =
  km.leak k

val invariant: #im:index_module -> km:key_module im -> inv:(h0:mem -> Type0){inv == km.invariant}
let invariant #im km =
  km.invariant

val invariant_framing_lemma: #im:index_module -> km:key_module im -> h0:mem -> h1:mem -> Lemma
  (requires (km.invariant h0))
  (ensures ((modifies_one h0.tip h0 h1 /\ h0.tip <> root) ==> km.invariant h1))
let invariant_framing_lemma #im km h0 h1 =
  km.invariant_framing_lemma h0 h1

#set-options "--z3rlimit 2000 --max_ifuel 2 --max_fuel 0"
val create: (im:index_module) ->
            (keylen: nat) ->
            (km_key_type: (i:id im -> t:Type0)) ->
            (km_kpm:plain_module{Plain.valid_length km_kpm == (check_length keylen)}) ->
            (km_get_rawGT: ((i:id im) -> (k:km_key_type i) -> GTot (raw:key_raw km_kpm))) -> // You have to have faith in this function...
            (km_invariant: (h:mem -> Type0)) ->
            (km_invariant_framing_lemma: (h0:mem -> h1:mem -> Lemma
              (requires (km_invariant h0))
              (ensures ((modifies_one h0.tip h0 h1 /\ h0.tip <> root) ==> km_invariant h1))
            )) ->
            (km_key_log_region: (r:log_region{disjoint r (ID.get_rgn im)})) ->
            (km_gen: (i:id im -> ST (k:km_key_type i) // The spec should indicate that the result is random and that gen is idempotent
              (requires (fun h0 ->
                (ID.fresh im i h0 \/ ID.honest im i)
                /\ km_invariant h0))
              (ensures  (fun h0 k h1 ->
                km_invariant h1
                /\ modifies (Set.singleton km_key_log_region) h0 h1
              )))) ->
            (km_set: (i:id im{~(Game2? current_game)} -> raw:key_raw km_kpm -> (k:km_key_type i{raw == km_get_rawGT i k}))) ->
            (km_coerce: (i:id im{ID.dishonest im i} -> raw:key_raw km_kpm -> (k:km_key_type i{raw == km_get_rawGT i k}))) ->
            (km_leak: (i:id im{ID.dishonest im i} -> k:km_key_type i -> (raw:key_raw km_kpm))) ->
            (km:key_module im{
              keylen == km.keylen
              /\ get_pm km == km_kpm
              /\ get_keytype km == km_key_type
              /\ get_keylen km == keylen
              /\ get_rawGT km == km_get_rawGT
              /\ invariant km == km_invariant
              /\ get_log_region km == km_key_log_region
    })
let create im keylen km_key_type kpm km_get_rawGT km_invariant km_invariant_framing_lemma km_key_log_region km_gen km_set km_coerce km_leak =
  let km = KM keylen km_key_type kpm km_get_rawGT km_invariant km_invariant_framing_lemma km_key_log_region km_gen km_set km_coerce km_leak in
  km
