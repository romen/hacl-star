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
module Plain = Box.Plain
module ID = Box.Index


//let index_module = im:ID.index_module{ID.id im == sub_id}
//let plain_index_module = im:ID.index_module{ID.id im == key_id}

let log_region =
  r:MR.rid{is_eternal_region r}


let wire_module = Plain.wire_module
let index_module = ID.index_module
let id = ID.id
let wire (pm:wire_module) = Plain.get_wire_t pm
let protected_plain (#im:index_module) (#pm:wire_module) (i:id im) = p:Plain.protected_wire_t im (pt:Plain.get_wire_t pm) i{Plain. valid_wire_length pm (Plain.make_wire_tGT p)}
let wire_bytes (#pm:wire_module) = b:bytes{Plain.valid_length pm (Seq.length b)}


val pkey_len: nat
val skey_len: nat
val sub_id:eqtype
val key_id: Type0

let im = (im:ID.index_module{ID.id im == sub_id})
let pim = (pim:ID.index_module{ID.id pim == key_id})


val ppm:wire_module
val cpm:wire_module
val pkpm:wire_module
val skpm:wire_module
val npm:wire_module

val aux_t: (im:ID.index_module) -> (kim:ID.index_module) -> (rgn:log_region) -> Type u#1

#set-options "--__temp_no_proj Box.PKAE"
abstract noeq type pkae_module =
  | PKAE:
    im:ID.index_module{ID.id im == sub_id} ->
    pim:ID.index_module{ID.id pim == key_id} ->
    ppm:Plain.wire_module ->
    cpm:wire_module ->
    pkpm:wire_module{Plain.valid_length pkpm == (fun n -> n = pkey_len)} ->
    skpm:wire_module{Plain.valid_length skpm == (fun n -> n = skey_len)} ->
    npm:wire_module ->
    rgn:log_region ->
    aux: aux_t im pim rgn ->
    pkae_module

val compute_cipher_length: (pkm:pkae_module) -> (plain_len:nat{Plain.valid_length pkm.ppm plain_len} -> cipher_len:nat{Plain.valid_length pkm.cpm cipher_len})
val compute_plain_length:  (pkm:pkae_module) -> (cipher_len:nat{Plain.valid_length pkm.cpm cipher_len} -> plain_len:nat{Plain.valid_length pkm.ppm plain_len})

//val enc: pkm:pkae_module -> (p:wire_bytes #pkm.ppm -> wire_bytes #pkm.npm -> wire_bytes #pkm.pkpm -> wire_bytes #pkm.skpm -> Tot (c:bytes{Seq.length c = compute_cipher_length pkm (Seq.length p)}))
//val dec: pkm:pkae_module -> (c:wire_bytes #pkm.cpm -> wire_bytes #pkm.npm -> wire_bytes #pkm.pkpm -> wire_bytes #pkm.skpm -> Tot (option (p:bytes{Seq.length p = compute_plain_length pkm (Seq.length c)})))

#reset-options
val skey: pkae_module -> Type0
val pkey: pkae_module -> Type0

val pkey_from_skey: (pkm:pkae_module -> sk:skey pkm -> pk:pkey pkm)
val pkey_get_raw: (pkm:pkae_module) -> (pkey pkm) -> wire pkm.pkpm
val skey_get_raw: (pkm:pkae_module) -> (skey pkm) -> GTot (wire_bytes #pkm.skpm)

let pkey_get_raw_bytesGT (pkm:pkae_module) (pk:pkey pkm) = Plain.wire_t_to_bytesGT pkm.pkpm (pkey_get_raw pkm pk)

let cipher (pkm:pkae_module) = (c:Plain.get_wire_t pkm.cpm)
let plain (pkm:pkae_module) = (p:Plain.get_wire_t pkm.ppm)
let nonce (pkm:pkae_module) = (n:Plain.get_wire_t pkm.npm )

val pkey_to_subId: #pkm:pkae_module -> pk:pkey pkm -> ID.id pkm.im
val pkey_to_subId_inj: #pkm:pkae_module -> pk:pkey pkm -> Lemma
  (requires True)
  (ensures (forall pk' . pkey_to_subId #pkm pk == pkey_to_subId #pkm pk' <==> pk == pk'))
  [SMTPat (pkey_to_subId #pkm pk)]

val compatible_keys: (pkm:pkae_module -> sk:skey pkm -> pk:pkey pkm -> t:Type0{t <==> (pkey_to_subId pk) =!= pkey_to_subId (pkey_from_skey pkm sk)})

//val enc (pkm:pkae_module): plain pkm -> n:nonce pkm -> pk:pkey pkm -> sk:skey pkm{compatible_keys pkm sk pk} -> GTot (cipher pkm)
//val dec (pkm:pkae_module): c:cipher pkm -> n:nonce pkm -> pk:pkey pkm -> sk:skey pkm{compatible_keys pkm sk pk} -> GTot (option (plain pkm))

val compose_ids: pkm:pkae_module ->  s1:sub_id -> s2:sub_id{s2 <> s1} -> key_id

//val length: pkae:pkae_module -> p:plain -> n:nat{valid_plain_length n}



// Message log types
let message_log_key (im:index_module) (npm:wire_module) = (wire_bytes #npm*(i:id im))
let message_log_value (im:index_module) (cpm:wire_module) (ppm:wire_module) (i:id im) = (c:wire_bytes #cpm*m:protected_plain #im #ppm i)
let message_log_range (im:index_module) (cpm:wire_module) (ppm:wire_module) (npm:wire_module) (k:message_log_key im npm) = (message_log_value im cpm ppm (snd k))
let message_log_inv (im:index_module) (cpm:wire_module) (ppm:wire_module) (npm:wire_module) (f:MM.map' (message_log_key im npm) (message_log_range im cpm ppm npm)) = True

let message_log (im:index_module) (cpm:wire_module) (ppm:wire_module) (npm:wire_module) (rgn:log_region) =
  MM.t rgn (message_log_key im npm) (message_log_range im cpm ppm npm) (message_log_inv im cpm ppm npm)


val get_message_log_region: pkm:pkae_module -> Tot (lr:log_region{extends lr pkm.rgn})
val get_message_logGT: pkm:pkae_module -> Tot (message_log pkm.pim pkm.cpm pkm.ppm pkm.npm (get_message_log_region pkm)) //TODO: MK: would prefer this to be GTot

val create: rgn:rid -> St (pkm:pkae_module)

val zero_bytes: n:nat -> Tot (b:bytes{b=Seq.create n (UInt8.uint_to_t 0)})
//TODO: MK this can be modelled better

#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 0"
val nonce_is_fresh: (pkm:pkae_module) -> (i:ID.id pkm.pim) -> (n:nonce pkm) -> (h:mem) ->
  (t:Type0{t <==>
    (MR.m_contains (get_message_logGT pkm) h
    /\ MM.fresh (get_message_logGT pkm) ((Plain.wire_t_to_bytesGT pkm.npm n),i) h)})

val invariant: pkae_module -> mem -> Type0

val gen: pkm:pkae_module -> ST (keypair:(pkey pkm*skey pkm){fst keypair == pkey_from_skey pkm (snd keypair)})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    modifies_none h0 h1
  ))

let registered pkm i = ID.registered pkm.pim i
let honest pkm i = ID.honest pkm.pim i
let dishonest pkm i = ID.dishonest pkm.pim i

val encrypt: pkm:pkae_module ->
             n:nonce pkm ->
             sk:skey pkm ->
             pk:pkey pkm{compatible_keys pkm sk pk} ->
             p:(protected_plain #pkm.pim #pkm.ppm (compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)))) ->
             ST (cipher pkm)
  (requires (fun h0 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
    registered pkm i
    ///\ (Flags.Game0? Flags.current_game \/ Flags.Game5? Flags.current_game)
    /\ nonce_is_fresh pkm i n h0
    /\ invariant pkm h0
  ))
  (ensures  (fun h0 c h1 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
    True //modifies (Set.singleton pkm.rgn) h0 h1 // stateful changes even if the id is dishonest.
    /\ ((honest pkm i /\ b2t ae_ind_cpa) // Ideal behaviour if the id is honest and the assumption holds.
      ==> ((Plain.wire_t_to_bytesGT pkm.cpm c) == enc pkm (zero_bytes (Plain.length #pkm.pim #pkm.ppm #(compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk))) p)) (Plain.wire_t_to_bytesGT pkm.pkpm (pkey_get_raw pkm pk)) (skey_get_raw pkm sk) (Plain.wire_t_to_bytesGT pkm.npm n)))
    /\ ((dishonest pkm i \/ ~(b2t ae_ind_cpa)) ==>
      (let repr_p = ((Plain.repr #pkm.pim #pkm.ppm #(compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk))) p)) in
      (Plain.wire_t_to_bytesGT pkm.cpm c) == enc pkm (Plain.wire_t_to_bytesGT pkm.ppm repr_p) (Plain.wire_t_to_bytesGT pkm.pkpm (pkey_get_raw pkm pk)) (skey_get_raw pkm sk) (Plain.wire_t_to_bytesGT pkm.npm n)))
    // The message is added to the log. This also guarantees nonce-uniqueness.
    /\ MR.m_contains #(get_message_log_region pkm)(get_message_logGT pkm) h1
    /\ MR.witnessed (MM.contains #(get_message_log_region pkm) (get_message_logGT pkm) ((Plain.wire_t_to_bytesGT pkm.npm n),i) ((Plain.wire_t_to_bytesGT pkm.cpm c),p))
    /\ MR.m_sel #(get_message_log_region pkm) h1 (get_message_logGT pkm)== MM.upd (MR.m_sel #(get_message_log_region pkm) h0 (get_message_logGT pkm)) ((Plain.wire_t_to_bytesGT pkm.npm n),i) ((Plain.wire_t_to_bytesGT pkm.cpm c),p)
    /\ invariant pkm h1
  ))

val decrypt: pkm:pkae_module ->
             n:nonce pkm ->
             sk:skey pkm ->
             pk:pkey pkm{compatible_keys pkm sk pk} ->
             c:cipher pkm ->
             ST (option (protected_plain #pkm.pim #pkm.ppm (compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)))))
  (requires (fun h0 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
    registered pkm i
    /\ invariant pkm h0
  ))
  (ensures  (fun h0 p h1 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
    let nonce_bytes = Plain.wire_t_to_bytesGT pkm.npm n in
    modifies_none h0 h1
    /\ invariant pkm h1
    /\ ((~(b2t pkae) \/ dishonest pkm i) ==> // Concrete behaviour of the id is dishonest or if the assumption doesn't hold.
        (let option_m = dec pkm (Plain.wire_t_to_bytesGT pkm.cpm c) (Plain.wire_t_to_bytesGT pkm.pkpm (pkey_get_raw pkm pk)) (skey_get_raw pkm sk) nonce_bytes in // Functional correctness: we get a result iff the ciphertext is valid.
        (Some? option_m ==>
          Some? p
          /\ (let v_option_m = Some?.v option_m in
            let v_p = Some?.v p in
            Plain.wire_t_to_bytesGT pkm.ppm (Plain.make_wire_tGT #pkm.pim #pkm.ppm #(compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk))) v_p) == v_option_m))
        /\ (None? option_m ==>
            None? p)
      ))
    /\ (let log = get_message_logGT pkm in
      (b2t pkae /\ honest pkm i) ==> // Ideal behaviour otherwise: We get a result iff something is in the log.
        (Some? p ==>
          (MM.defined log (nonce_bytes,i) h0 /\ (fst (MM.value log (nonce_bytes,i) h0) == (Plain.wire_t_to_bytesGT pkm.cpm c) )
          /\ Some?.v p == snd (MM.value log (nonce_bytes,i) h0)))
      /\ (None? p ==>
          (MM.fresh log (nonce_bytes,i) h0 \/ Plain.wire_t_to_bytesGT pkm.cpm c =!= fst (MM.value log (nonce_bytes,i) h0)))
      )
  ))
