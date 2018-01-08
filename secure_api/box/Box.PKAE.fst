(**
  This module represents the PKAE cryptographic security game expressed in terms of the underlying cryptobox construction.
*)
module Box.PKAE

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
module SPEC = Spec.CryptoBox
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Index
module ODH = Box.ODH
module AE = Box.AE
module LE = FStar.Endianness

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 0"
//let nonce = AE.nonce
//let cipher = AE.cipher
//let sub_id  = lbytes Curve.serialized_point_length
//let key_id = (i:(lbytes Curve.serialized_point_length*lbytes Curve.serialized_point_length){b2t (ODH.smaller' Curve.serialized_point_length (fst i) (snd i))})
//let plain = AE.ae_plain


//let valid_plain_length = AE.valid_plain_length
//let valid_cipher_length = AE.valid_cipher_length

let zero_nonce = Seq.create HSalsa.noncelen (UInt8.uint_to_t 0)
let hsalsa20_hash input = HSalsa.hsalsa20 input zero_nonce

let base_point:lbytes Curve.serialized_point_length = Curve.base_point

let pkey_len = Curve.serialized_point_length
let skey_len = Curve.scalar_length
let sub_id = b:bytes{Seq.length b = Curve.serialized_point_length}
let key_id = i:(sub_id * sub_id){b2t (ODH.smaller' Curve.serialized_point_length (fst i) (snd i))}

let valid_plain_length n = n / Spec.Salsa20.blocklen < pow2 32
let plain_buffer = b:FStar.Buffer.buffer UInt8.t{valid_plain_length (FStar.Buffer.length #UInt8.t b)}


val buffer_length_lemma: unit -> Lemma
  (requires True)
  (ensures forall (b:plain_buffer) . valid_plain_length (FStar.Buffer.length b))
let buffer_length_lemma() = ()

let buffer_to_bytesST n b = FStar.Buffer.to_seq #plain_buffer b n
let bytes_to_bufferST n b = FStar.Buffer.create b n
let buffer_to_bytesGT n b = FStar.Buffer.as_seq

let ppm = Plain.create (FStar.Buffer.buffer UInt8.t)
                       (fun n -> n / Spec.Salsa20.blocklen < pow2 32)
                       (FStar.Buffer.length)
                       (buffer_length_lemma)
                       (FStar.Buffer.as_seq)
                       (buffer_to_bytesST)
                       (bytes_to_bufferST)


val cpm:wire_module
val pkpm:wire_module
val skpm:wire_module
val npm:wire_module
#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 0"
private noeq type aux_t'
                         (im:ID.index_module)
                         (kim:ID.index_module)
                         (rgn:log_region)
                         =
  | AUX:
    am:AE.ae_module kim{extends (AE.get_message_log_region #kim am) rgn
                        /\ AE.get_ppm am == ppm
                        /\ AE.get_cpm am == cpm
                        /\ AE.get_npm am == npm} ->
    om:ODH.odh_module{ODH.get_hash_length om = HSalsa.keylen
                      /\ ODH.get_dh_share_length om = Curve.serialized_point_length
                      /\ ODH.get_dh_exponent_length om = Curve.scalar_length
                      ///\ ODH.dh_exponentiate om == Curve.scalarmult
                      ///\ ODH.hash_fun om == hsalsa20_hash
                      ///\ ODH.get_base_point om = base_point
                      /\ ODH.get_index_module om == im
                      /\ ODH.get_key_index_module om == kim
                      /\ ODH.get_kpm om == AE.get_kpm am
                      /\ ODH.get_spm om == pkpm
                      /\ ODH.get_epm om == skpm
                      } ->
    km:Key.key_module kim{
                          km == ODH.get_key_module om kim
                          /\ km == AE.instantiate_km am
                          /\ Key.get_keylen km == ODH.get_hash_length om
                          /\ extends (Key.get_log_region km) rgn} ->
    aux_t' im kim ppm cpm pkpm skpm npm rgn

let aux_t im kim ppm cpm pkpm skpm npm rgn = aux_t' im kim ppm cpm pkpm skpm npm rgn

let compute_cipher_length pkm = AE.compute_cipher_length pkm.aux.am
let compute_plain_length pkm = AE.compute_plain_length pkm.aux.am

val enc: pkm:pkae_module -> (p:wire_bytes #pkm.ppm -> wire_bytes #pkm.npm -> wire_bytes #pkm.pkpm -> wire_bytes #pkm.skpm -> Tot (c:bytes{Seq.length c = compute_cipher_length pkm (Seq.length p)}))
val dec: pkm:pkae_module -> (c:wire_bytes #pkm.cpm -> wire_bytes #pkm.npm -> wire_bytes #pkm.pkpm -> wire_bytes #pkm.skpm -> Tot (option (p:bytes{Seq.length p = compute_plain_length pkm (Seq.length c)})))
let enc pkm = SPEC.cryptobox
let dec pkm = SPEC.cryptobox_open

let skey pkm = ODH.skey pkm.aux.om
let pkey pkm = ODH.pkey pkm.aux.om

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 0"
let pkey_from_skey pkm sk = ODH.get_pkey pkm.aux.om sk
let pkey_raw_from_skey pkm sk = ODH.sk_get_share_bytesGT pkm.aux.om sk
let pkey_get_raw pkm pk = ODH.pk_get_share pkm.aux.om pk
let skey_get_raw pkm sk = ODH.get_skeyGT pkm.aux.om sk

let pkey_to_subId #pkm pk = ODH.pk_get_share pkm.aux.om pk
//let pkey_to_subId_inj #pkm pk = ODH.lemma_pk_get_share_inj pkm.aux.om pk


let compatible_keys pkm sk pk = ODH.compatible_keys pkm.aux.om sk pk

//let enc pkm p n pk sk =
//  SPEC.cryptobox p n (ODH.pk_get_share pkm.aux.om pk) (ODH.get_skeyGT pkm.aux.om sk)
//
//let dec pkm c n pk sk =
//  let p = SPEC.cryptobox_open c n (ODH.pk_get_share pkm.aux.om pk) (ODH.get_skeyGT pkm.aux.om sk) in
//  match p with
//  | Some p' ->
//    let p'':plain = p' in
//    Some p''
//  | None -> None

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 1"
let compose_ids pkm i1 i2 = ODH.compose_ids pkm.aux.om i1 i2

//let key_index_module = plain_index_module
//let plain_module = pm:Plain.plain_module{Plain.get_plain pm == plain /\ Plain.valid_length #pm == valid_plain_length}

#set-options "--z3rlimit 1600 --max_ifuel 2 --max_fuel 0 --__temp_no_proj Box.PKAE"
val message_log_lemma: pkm:pkae_module -> rgn:log_region{disjoint (ID.get_rgn pkm.pim) rgn} -> Lemma
  (requires True)
  (ensures message_log pkm.pim pkm.cpm pkm.ppm pkm.npm rgn === AE.message_log pkm.pim pkm.cpm pkm.ppm pkm.npm rgn)
let message_log_lemma pkm rgn =
  //assume(AE.ae_plain == plain pkm);
  //assume(AE.cipher == cipher pkm);
  //assume(AE.nonce == nonce pkm);
  //assume(pkm.key_id == ID.id pkm.pim);
  assert((message_log_key pkm.pim pkm.npm) == (AE.message_log_key pkm.pim pkm.npm));
  let ae_efun:((message_log_key pkm.pim pkm.npm) -> Type0) = AE.message_log_range pkm.pim pkm.ppm pkm.cpm pkm.npm in
  //admit();
  assert(FStar.FunctionalExtensionality.feq (message_log_value pkm.pim) (AE.message_log_value pkm.pim));
  assert(FStar.FunctionalExtensionality.feq (message_log_range pkm.pim pkm.ppm pkm.cpm pkm.npm) (AE.message_log_range pkm.pim pkm.ppm pkm.cpm pkm.npm));
  //admit();
  let inv = message_log_inv pkm.pim pkm.cpm pkm.ppm pkm.npm in
  let map_t =MM.map' (message_log_key pkm.pim pkm.npm) (message_log_range pkm.pim pkm.ppm pkm.cpm pkm.npm) in
  let inv_t = map_t -> Type0 in
  let ae_inv = AE.message_log_inv pkm.pim pkm.ppm pkm.cpm pkm.npm in
  let ae_inv:map_t -> Type0 = ae_inv in
  assert(FStar.FunctionalExtensionality.feq
    #map_t #Type
    inv ae_inv);
  assert(message_log pkm.pim pkm.ppm pkm.cpm pkm.npm rgn == AE.message_log pkm.pim pkm.ppm pkm.cpm pkm.npm rgn);
  ()


#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 0"
let get_message_log_region pkm = AE.get_message_log_region pkm.aux.am

val coerce: t1:Type -> t2:Type{t1 == t2} -> x:t1 -> t2
let coerce t1 t2 x = x

let get_message_logGT pkm =
  let (ae_log:AE.message_log pkm.pim (get_message_log_region pkm)) = AE.get_message_logGT #pkm.pim pkm.aux.am in
  let (ae_rgn:log_region) = AE.get_message_log_region pkm.aux.am in
  message_log_lemma pkm.pim ae_rgn;
  let log:message_log pkm.pim ae_rgn = coerce (AE.message_log pkm.pim ae_rgn) (message_log pkm.pim ae_rgn) ae_log in
  log

#set-options "--z3rlimit 1000 --max_ifuel 2 --max_fuel 1"
val create_aux: (im:index_module) ->
                (kim:ID.index_module{ID.id kim == key_id /\ disjoint (ID.get_rgn im) (ID.get_rgn kim)}) ->
                (pm:Plain.plain_module{Plain.get_plain pm == AE.ae_plain /\ Plain.valid_length #pm == AE.valid_plain_length}) ->
                rgn:rid{disjoint rgn (ID.get_rgn kim)/\ disjoint rgn (ID.get_rgn im)} ->
                ST (aux_t im kim pm rgn)
                (requires (fun h0 -> True))
                (ensures (fun h0 aux h1 -> True))
let create_aux im kim pm rgn =
  let am = AE.create kim pm rgn in
  let km = AE.instantiate_km #kim am in
  let om = ODH.create HSalsa.keylen Curve.serialized_point_length Curve.scalar_length hsalsa20_hash Curve.scalarmult Curve.base_point im kim km rgn in
  AUX am om km

val lemma_type_equality: t1:Type0 -> t2:Type0 -> pred:(t2 -> t2 -> bool) -> Lemma
  (requires t1 == t2)
  (ensures (t1 == t2 ==> i:(t1*t1){pred (fst i) (snd i)} == i:(t2*t2){pred (fst i) (snd i)}))
let lemma_type_equality t1 t2 pred = ()

#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 0"
let create rgn =
  let im_id_log_rgn = new_region rgn in
  let kim_id_log_rgn = new_region rgn in
  let im = ID.create im_id_log_rgn sub_id in
  let dh_share_length = Curve.serialized_point_length in
  lemma_type_equality (sub_id) (lbytes Curve.serialized_point_length) (ODH.smaller' dh_share_length);
  lemma_type_equality (sub_id) (ID.id im) (ODH.smaller' dh_share_length);
  let kim = ID.compose kim_id_log_rgn im (ODH.smaller' dh_share_length) in
  assert(sub_id == lbytes Curve.serialized_point_length);
  assert(key_id == i:(sub_id*sub_id){b2t (ODH.smaller' dh_share_length (fst i) (snd i))});
  assert(disjoint im_id_log_rgn kim_id_log_rgn);
  assert(ID.id kim == key_id);
  let pm = Plain.create plain AE.valid_plain_length AE.length in
  assert(FunctionalExtensionality.feq (Plain.valid_length #pm) valid_plain_length);
  let log_rgn = new_region rgn in
  let aux = create_aux im kim pm log_rgn in
  PKAE im kim pm log_rgn aux

let key (pkm:pkae_module) = AE.key pkm.pim

let zero_bytes = AE.create_zero_bytes

let nonce_is_fresh (pkm:pkae_module) (i:ID.id pkm.pim) (n:nonce) (h:mem) =
  AE.nonce_is_fresh pkm.aux.am i n h

let invariant pkm =
  Key.invariant pkm.pim pkm.aux.km

let gen pkm =
  ODH.keygen pkm.aux.om

#set-options "--z3rlimit 1000 --max_ifuel 0 --max_fuel 0"
let encrypt pkm n sk pk m =
  let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
  let k = ODH.prf_odh pkm.aux.om sk pk in
  let c = AE.encrypt pkm.aux.am #i n k m in
  let h = get() in
  ID.lemma_honest_or_dishonest pkm.pim i;
  let honest_i = ID.get_honest pkm.pim i in
  assert(FStar.FunctionalExtensionality.feq (message_log_range pkm.pim) (AE.message_log_range pkm.pim));
  MM.contains_stable (get_message_logGT pkm) (n,i) (c,m);
  MR.witness (get_message_logGT pkm) (MM.contains (get_message_logGT pkm) (n,i) (c,m));
  c

let decrypt pkm n sk pk c =
  let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
  let k = ODH.prf_odh pkm.aux.om sk pk in
  let m = AE.decrypt pkm.aux.am #i n k c in
  m

(* low-level wrapper *)

let my_create = create

open FStar.Buffer
open Hacl.Policies
module U64 = FStar.UInt64
type u64   = FStar.UInt64.t

let uint8_p = buffer Hacl.UInt8.t

let buf_to_seq (b:uint8_p): Stack (seq FStar.UInt8.t) (requires (fun h -> live h b)) (ensures (fun h0 s h1 -> live h1 b)) =
  let ss = to_seq_full b in
  let sl = seq_to_list ss in
  let fl = FStar.List.Tot.map declassify_u8 sl in
  seq_of_list fl

let as_seq h (b:uint8_p) =
  seq_of_list (FStar.List.Tot.map declassify_u8 (seq_to_list (Buffer.as_seq h b)))

assume val seq_to_buf: (s:seq FStar.UInt8.t) -> St (b:uint8_p)

let pkm = my_create root

#set-options "--z3rlimit 1000 --max_ifuel 1 --max_fuel 0"
val transmute_bytes_to_buffer: #pkm:pkae_module -> #i:ID.id pkm.pim -> p1:Plain.protected_plain_t pkm.pim plain i -> St (p2:Plain.protected_plain_t pkm.pim (Buffer.buffer Hacl.UInt8.t) i)
let transmute_bytes_to_buffer #pkm #i p1 =
  Plain.transmute_protected_plainST #pkm.pim #i #plain #uint8_p seq_to_buf p1

val encrypt_low:
  pkm:pkae_module ->
  sk:skey pkm -> //I use the abstract high level keys here
  pk:pkey pkm ->
  c:uint8_p ->
  m:Plain.protected_plain_t pkm.pim uint8_p (compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk))) ->
  mlen:u64{let len = U64.v mlen in length c = len /\ len = Plain.length #pkm.pim #pkm.pm m}  ->
  n:uint8_p ->
  Stack u32
    (requires (fun h -> live h c /\ Plain.live m h /\ live h n))  //we have to add the security specification here
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c /\
      ( let r = as_seq h1 c in
        let m = as_seq h1 (Plain.make_plainGT #pkm.im #pkm.pm m) in
        r = SPEC.cryptobox m (as_seq h1 n) (ODH.pk_get_share pkm.aux.om pk) (ODH.get_skeyGT pkm.aux.om sk) )))
let encrypt_low pkm sk pk c m mlen n =
  let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
  let m = Plain.transmute_protected_plainST #pkm.im #i #uint8_p #plain buf_to_seq m in
  let n = buf_to_seq n in
  let m = admit() in //conversion from m to abstract plaintext?
  let c' = encrypt pkm n sk pk m in
  seq_to_buf c c';
  0ul

val decrypt_low:
  m:uint8_p ->
  c:uint8_p ->
  mlen:u64  ->
  n:uint8_p ->
  pk:uint8_p->
  sk:uint8_p{disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let decrypt_low m c mlen n pk sk =
  admit()
