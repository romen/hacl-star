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
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Index

// Some basic types
val key_t: (pm:plain_module) -> (im:index_module) -> i:id im -> Type0

let log_region =
  r:MR.rid{is_eternal_region r}

let protected_plain (#im:index_module) (#pm:plain_module) (i:id im) = p:Plain.protected_plain_t im (pt:plain pm) i{Plain.valid_plain_length (Plain.make_plain_tGT p)}
let plain_bytes (#pm:plain_module) = b:bytes{Plain.valid_length pm (Seq.length b)}

// Key log types
let key_log_key (im:index_module) = i:id im
let key_log_value (kpm:plain_module) (im:index_module) (i:id im) = (key_t kpm im i)
let key_log_range (kpm:plain_module) (im:index_module) = fun (k:key_log_key im) -> (v:key_log_value kpm im k)
let key_log_inv (kpm:plain_module) (im:index_module) (f:MM.map' (key_log_key im) (key_log_range kpm im)) = True

let key_log_t (kpm:plain_module) (im:index_module) (rgn:log_region) = MM.t rgn (key_log_key im) (key_log_range kpm im) (key_log_inv kpm im)


// Message log types
let message_log_key (im:index_module) (npm:plain_module) = (plain_bytes #npm*(i:id im))
let message_log_value (im:index_module) (cpm:plain_module) (ppm:plain_module) (i:id im) = (c:plain_bytes #cpm*m:protected_plain #im #ppm i)
let message_log_range (im:index_module) (cpm:plain_module) (ppm:plain_module) (npm:plain_module) (k:message_log_key im npm) = (message_log_value im cpm ppm (snd k))
let message_log_inv (im:index_module) (cpm:plain_module) (ppm:plain_module) (npm:plain_module) (f:MM.map' (message_log_key im npm) (message_log_range im cpm ppm npm)) = True

let message_log (im:index_module) (cpm:plain_module) (ppm:plain_module) (npm:plain_module) (rgn:log_region) =
  MM.t rgn (message_log_key im npm) (message_log_range im cpm ppm npm) (message_log_inv im cpm ppm npm)

#set-options "--__temp_no_proj Box.AE"
abstract noeq type ae_module (im:index_module) =
  | AM :
    key_length: UInt32.t{(UInt32.v key_length) > 0} ->
    ppm:plain_module ->
    cpm:plain_module ->
    kpm:plain_module{Plain.valid_length kpm == (Key.check_length (UInt32.v key_length))} ->
    npm:plain_module ->
    compute_cipher_length: (plain_len:nat{Plain.valid_length ppm plain_len} -> cipher_len:nat{Plain.valid_length cpm cipher_len}) ->
    compute_plain_length:  (cipher_len:nat{Plain.valid_length cpm cipher_len} -> plain_len:nat{Plain.valid_length ppm plain_len}) ->
    enc: (p:plain_bytes #ppm -> plain_bytes #kpm -> plain_bytes #npm -> Tot (c:bytes{Seq.length c = compute_cipher_length (Seq.length p)})) ->
    dec: (c:plain_bytes #cpm -> plain_bytes #kpm -> plain_bytes #npm -> Tot (option (p:bytes{Seq.length p = compute_plain_length (Seq.length c)}))) ->
    enc_low:(p:plain ppm -> k:plain kpm -> n:plain npm -> ST (c:plain cpm)
      (requires (fun h0 -> True))
      (ensures (fun h0 c h1 ->
        Plain.plain_to_bytesGT h1 c == enc (Plain.plain_to_bytesGT h1 p) (Plain.plain_to_bytesGT h1 k) (Plain.plain_to_bytesGT h1 n)
        /\ modifies_none h0 h1
        /\ Plain.live c h1
      ))
      ) ->
    dec_low:(c:plain cpm -> k:plain kpm -> n:plain npm -> ST (option (p:plain ppm))
      (requires (fun h0 -> True))
      (ensures (fun h0 p h1 ->
        let spec_p = dec (Plain.plain_to_bytesGT h1 c) (Plain.plain_to_bytesGT h1 k) (Plain.plain_to_bytesGT h1 n) in
        (Some? p ==> (let v = Some?.v p in
          Some? spec_p /\ Plain.plain_to_bytesGT h1 v == Some?.v spec_p /\ Plain.live (Some?.v p) h1))
        /\ (None? p ==> None? spec_p)
        /\ modifies_none h0 h1
      ))
      ) ->
    key_log_region: (rgn:log_region{disjoint rgn (ID.get_rgn im) /\ is_eternal_region rgn})->
    message_log_region: (rgn:log_region{disjoint rgn key_log_region /\ disjoint rgn (ID.get_rgn im) /\ is_eternal_region rgn}) ->
    key_log: (key_log_t kpm im key_log_region) ->
    message_log: (message_log im cpm ppm npm message_log_region) ->
    ae_module im

let cipher (#im:index_module) (am:ae_module im) = (c:Plain.plain am.cpm)
//let plain  (#im:index_module) (am:ae_module im) = (p:Plain.plain am.ppm)
let nonce (#im:index_module) (am:ae_module im) = (n:Plain.plain am.npm )
let nonce_bytes (#im:index_module) (am:ae_module im) = (n:Plain.plain_bytes am.npm )
let key (#im:index_module) (#am:ae_module im) (i:id im) = key_t am.kpm im i
let key_raw (#im:index_module) (#am:ae_module im) = raw_t:plain_bytes #am.kpm

val create_zero_bytes: n:nat -> Tot (b:bytes{b=Seq.create n (UInt8.uint_to_t 0)})

private val get_rawGT: #im:index_module -> #am:ae_module im -> i:id im -> k:key #im #am i -> GTot (key_raw #im #am)

val recall_logs: #im:index_module -> am:ae_module im -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains am.message_log h1
    /\ MR.m_contains am.key_log h1
  ))

val get_message_log_region: #im:index_module  -> am:ae_module im -> Tot (lr:log_region{lr == am.message_log_region})

#set-options "--__temp_no_proj Box.AE"
#set-options "--z3rlimit 200 --max_ifuel 1 --max_fuel 0"
val get_message_logGT: #im:index_module  -> am:ae_module im -> Tot (ml:message_log im am.cpm am.ppm am.npm am.message_log_region{ml == am.message_log})

val get_ppm: #im:index_module -> am:ae_module im -> pm:plain_module{pm == am.ppm}
val get_cpm: #im:index_module -> am:ae_module im -> pm:plain_module{pm == am.cpm}
val get_npm: #im:index_module -> am:ae_module im -> pm:plain_module{pm == am.npm}
val get_kpm: #im:index_module -> am:ae_module im -> pm:plain_module{pm == am.kpm}

val compute_cipher_length: (#im:index_module) -> (am:ae_module im) -> (plain_len:nat{Plain.valid_length am.ppm plain_len} -> cipher_len:nat{Plain.valid_length am.cpm cipher_len})
val compute_plain_length: (#im:index_module) -> (am:ae_module im) -> (cipher_len:nat{Plain.valid_length am.cpm cipher_len} -> plain_len:nat{Plain.valid_length am.ppm plain_len})

val nonce_is_fresh: (#im:index_module) -> (am:ae_module im) -> (i:id im) -> (n:nonce_bytes am) -> (h:mem) -> (t:Type0{t <==>
    (MR.m_contains am.message_log h
    /\ MM.fresh am.message_log (n,i) h)})

let log_freshness_invariant (#im:index_module) (am:ae_module im) (h:mem) =
  MR.m_contains (get_log im) h
  /\ MR.m_contains am.message_log h
  /\ (forall i n . ID.fresh im i h ==> MM.fresh am.message_log (n,i) h)

//val log_freshness_framing_lemma: #im:index_module -> am:ae_module im -> h0:mem -> h1:mem -> Lemma
//  (requires log_freshness_invariant am h0)
//  (ensures (modifies_none h0 h1 ==> (log_freshness_invariant am h1)))

val lemma_nonce_freshness: #im:index_module  -> am:ae_module im -> i:id im -> n:nonce_bytes am -> h0:mem -> h1:mem -> Lemma
  (requires nonce_is_fresh am i n h0 /\ (modifies (Set.singleton am.key_log_region) h0 h1 \/ h0 == h1))
  (ensures ((modifies (Set.singleton am.key_log_region) h0 h1 \/ h0 == h1) ==> nonce_is_fresh am i n h1))

val create: im:index_module ->
            rgn:log_region{disjoint rgn (ID.get_rgn im) /\ is_just_below root rgn} ->
            key_length: UInt32.t{(UInt32.v key_length > 0)} ->
            ppm:plain_module ->
            cpm:plain_module ->
            kpm:plain_module{Plain.valid_length kpm == (check_length (UInt32.v key_length))} ->
            npm:plain_module ->
            compute_cipher_length: (plain_len:nat{Plain.valid_length ppm plain_len} -> cipher_len:nat{Plain.valid_length cpm cipher_len}) ->
            compute_plain_length:  (cipher_len:nat{Plain.valid_length cpm cipher_len} -> plain_len:nat{Plain.valid_length ppm plain_len}) ->
            enc: (p:plain_bytes #ppm -> plain_bytes #kpm -> plain_bytes #npm -> Tot (c:bytes{Seq.length c = compute_cipher_length (Seq.length p)})) ->
            dec: (c:plain_bytes #cpm -> plain_bytes #kpm -> plain_bytes #npm -> Tot (option (p:bytes{Seq.length p = compute_plain_length (Seq.length c)}))) ->
            enc_low:(p:plain ppm -> k:plain kpm -> n:plain npm -> ST (c:plain cpm)
              (requires (fun h0 -> True))
              (ensures (fun h0 c h1 ->
                Plain.plain_to_bytesGT h1 c == enc (Plain.plain_to_bytesGT h1 p) (Plain.plain_to_bytesGT h1 k) (Plain.plain_to_bytesGT h1 n)
                /\ modifies_none h0 h1
                /\ Plain.live c h1
              ))
              ) ->
            dec_low:(c:plain cpm -> k:plain kpm -> n:plain npm -> ST (option (p:plain ppm))
              (requires (fun h0 -> True))
              (ensures (fun h0 p h1 ->
                let spec_p = dec (Plain.plain_to_bytesGT h1 c) (Plain.plain_to_bytesGT h1 k) (Plain.plain_to_bytesGT h1 n) in
                (Some? p ==> (let v = Some?.v p in
                  Some? spec_p /\ Plain.plain_to_bytesGT h1 v == Some?.v spec_p /\ Plain.live (Some?.v p) h1))
                /\ (None? p ==> None? spec_p)
                /\ modifies_none h0 h1
              ))
              ) ->
            ST (am:ae_module im)
  (requires (fun h0 ->
    True
  ))
  (ensures (fun h0 am h1 ->
    modifies_none h0 h1
    /\ HH.extends am.message_log_region rgn
    /\ HH.extends am.key_log_region rgn
    /\ disjoint am.message_log_region am.key_log_region
    /\ MR.m_contains am.key_log h1
    /\ MR.m_contains am.message_log h1
    /\ MR.m_sel #am.key_log_region h1 am.key_log == MM.empty_map (key_log_key im) (key_log_range kpm im)
    /\ MR.m_sel #am.message_log_region h1 am.message_log == MM.empty_map (message_log_key im am.npm) (message_log_range im am.cpm am.ppm am.npm)
    /\ log_freshness_invariant #im am h1
    /\ ppm == am.ppm
    /\ cpm == am.cpm
    /\ kpm == am.kpm
    /\ npm == am.npm
  ))

private val gen: #im:index_module  -> #am:ae_module im -> i:id im -> ST (k:key #im #am i)
  (requires (fun h0 ->
    (fresh im i h0 \/ honest im i)
    /\ log_freshness_invariant am h0
  ))
  (ensures  (fun h0 k h1 ->
    (MM.fresh am.key_log i h0 ==>
              (modifies (Set.singleton am.key_log_region) h0 h1
              /\ MR.m_sel h1 am.key_log == MM.upd (MR.m_sel h0 am.key_log) i k))
    /\ (MM.defined am.key_log i h0 ==> h0 == h1)
    /\ log_freshness_invariant am h1
  ))

private val set: #im:index_module -> #am:ae_module im -> i:id im{~(Game2? current_game)} -> raw:key_raw #im #am -> (k:key #im #am i{get_rawGT i k == raw})

private val coerce: #im:index_module -> #am:ae_module im -> i:id im{dishonest im i} -> raw:key_raw #im #am -> (k:key #im #am i{get_rawGT i k == raw})

private val leak: #im:index_module -> #am:ae_module im -> i:id im{dishonest im i} -> k:key #im #am i -> Tot (raw:key_raw #im #am{raw == get_rawGT i k})

val instantiate_km: #im:index_module -> am:ae_module im -> km:key_module im{
    Key.get_keylen km == (UInt32.v am.key_length)
    /\ Key.get_pm km == am.kpm
    /\ Key.get_keytype km == key #im #am
    /\ Key.get_rawGT km == get_rawGT #im #am
    /\ Key.invariant km == log_freshness_invariant am
    /\ Key.get_log_region km == am.key_log_region
    /\ disjoint (Key.get_log_region km) am.message_log_region
    }

#reset-options
(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
 #set-options "--z3rlimit 500 --max_ifuel 1 --max_fuel 0"
val encrypt: #im:index_module -> am:ae_module im -> #(i:id im) -> nl:nat{Plain.valid_length am.npm nl} -> n:nonce am{Plain.plain_length #am.npm n = nl} -> k:key #im #am i -> pl:nat{Plain.valid_length am.ppm pl} -> p:protected_plain #im #am.ppm i{Plain.protected_plain_length #im #am.ppm p = pl} -> c:cipher am -> StackInline unit
(requires (fun h0 ->
  registered im i
  /\ nonce_is_fresh #im am i (Plain.plain_to_bytesGT h0 n) h0 // Nonce freshness
  /\ log_freshness_invariant #im am h0
  /\ Plain.plain_live p h0
  /\ Plain.live n h0
  /\ Plain.live c h0
))
(ensures  (fun h0 _ h1 ->
  registered im i
  /\ modifies (Set.singleton (get_message_log_region #im am)) h0 h1 // stateful changes even if the id is dishonest.
  /\ ((honest im i /\ b2t ae_ind_cpa) // Ideal behaviour if the id is honest and the assumption holds.
      ==> ((Plain.plain_to_bytesGT h1 c) == am.enc (create_zero_bytes (Plain.protected_plain_length #im #am.ppm #i p)) (get_rawGT i k) (Plain.plain_to_bytesGT h1 n)))
  /\ ((dishonest im i \/ ~(b2t ae_ind_cpa)) ==>
      (let repr_p = ((Plain.repr #im #am.ppm #i p)) in
      (Plain.plain_to_bytesGT h1 c) == am.enc (Plain.plain_to_bytesGT h1 repr_p) (get_rawGT i k) (Plain.plain_to_bytesGT h1 n)))
  /\ MR.m_contains am.message_log h1  // A message is added to the log even if the id is dishonest. This also guarantees nonce-uniqueness.
  /\ MR.witnessed (MM.contains am.message_log ((Plain.plain_to_bytesGT h1 n),i) ((Plain.plain_to_bytesGT h1 c),p))
  /\ MR.m_sel h1 am.message_log == MM.upd (MR.m_sel h0 am.message_log) ((Plain.plain_to_bytesGT h1 n),i) ((Plain.plain_to_bytesGT h1 c),p)
  /\ log_freshness_invariant #im am h1
  /\ Plain.live c h1
  /\ Plain.plain_live p h1
))

(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
*)
//#set-options "--z3rlimit 1000 --max_ifuel 1 --max_fuel 0"
val decrypt: #im:index_module -> am:ae_module im -> #(i:id im) -> nl:nat{Plain.valid_length am.npm nl} ->  n:nonce am{Plain.plain_length #am.npm n = nl} -> k:key #im #am i -> cl:nat{Plain.valid_length am.ppm cl} -> c:cipher am{Plain.plain_length #am.cpm c = cl} -> StackInline (option (protected_plain #im #am.ppm i))
  (requires (fun h0 ->
    registered im i // No in-between states of keys (i.e.) where one of the shares is fresh and one is registered
    /\ Plain.live c h0
    /\ Plain.live n h0
  ))
  (ensures  (fun h0 p h1 ->
    let modified_regions_honest = Set.singleton am.message_log_region in
    let byte_nonce = Plain.plain_to_bytesGT h1 n in
    registered im i
    /\ modifies_none h0 h1
    /\ ((~(b2t ae_int_ctxt) \/ dishonest im i) ==> // Concrete behaviour of the id is dishonest or if the assumption doesn't hold.
        (let option_m = am.dec (Plain.plain_to_bytesGT h1 c) (get_rawGT i k) byte_nonce in // Functional correctness: we get a result iff the ciphertext is valid.
          (Some? option_m ==>
            (Some? p
            /\ (let v_option_m = Some?.v option_m in
              let v_p = Some?.v p in
              (Plain.plain_to_bytesGT h1 (Plain.make_plain_tGT #im #am.ppm #i v_p)) == v_option_m
              /\ Plain.plain_live #im #am.ppm #i v_p h1)))
          /\ (None? option_m ==>
              None? p)
      ))
    // Ideal behaviour otherwise: We get a result iff something is in the log.
    /\ ((b2t ae_int_ctxt /\ honest im i) ==>
        (Some? p ==>
          (let v = Some?.v p in
          MM.defined am.message_log (byte_nonce,i) h0 /\ (fst (MM.value am.message_log (byte_nonce,i) h0) == (Plain.plain_to_bytesGT h1 c))
          /\ v == snd (MM.value am.message_log (byte_nonce,i) h0)
          /\ Plain.plain_live #im #am.ppm #i v h1))
    /\ (None? p
    ==> (MM.fresh am.message_log (byte_nonce,i) h0 \/ (Plain.plain_to_bytesGT h1 c) =!= fst (MM.value am.message_log (byte_nonce,i) h0)))
   )
  ))
