module Box.ODH

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

open Crypto.Symmetric.Bytes

module ID = Box.Index
module HH = FStar.HyperHeap
module Key = Box.Key

val smaller': n:nat -> i1:lbytes n -> i2:lbytes n -> b:bool{b ==> i1 <> i2}
let plain_module = Plain.plain_module

let plain (pm:plain_module) = Plain.plain pm
let plain_bytes (pm:plain_module) = b:bytes{Plain.valid_length pm (Seq.length b)}

#set-options "--__temp_no_proj Box.ODH"
#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 0"
abstract noeq type odh_module = // require subId type to be dh_share?
  | ODH:
    rgn:(r:HH.rid) ->
    hash_length:(n:nat{0 < n /\ n <= UInt.max_int 32}) ->
    dh_share_length:(n:nat{0 < n /\ n <= UInt.max_int 32}) ->
    dh_exponent_length:(n:nat{0 < n /\ n <= UInt.max_int 32}) ->
    kpm:plain_module{Plain.valid_length kpm == Key.check_length hash_length} ->
    spm:plain_module{Plain.valid_length spm == Key.check_length dh_share_length} ->
    epm:plain_module{Plain.valid_length epm == Key.check_length dh_exponent_length} ->
    hash: (lbytes dh_share_length -> (lbytes hash_length)) ->
    hash_low: (input:plain spm -> ST (output:plain kpm)
      (requires (fun h0 -> True))
      (ensures (fun h0 output h1 ->
        Plain.plain_to_bytesGT h1 output == hash (Plain.plain_to_bytesGT h1 input)
        /\ modifies_none h0 h1
      ))
    ) ->
    exponentiate: (e:lbytes dh_exponent_length -> sh:lbytes dh_share_length -> Tot (lbytes dh_share_length)) ->
    exponentiate_low: (e:plain epm -> sh:plain spm -> ST (res:plain spm)
      (requires (fun h0 -> True))
      (ensures (fun h0 res h1 ->
        Plain.plain_to_bytesGT h1 res == exponentiate (Plain.plain_to_bytesGT h1 e) (Plain.plain_to_bytesGT h1 sh)
        /\ modifies_none h0 h1
      ))
    ) ->
    base_point: lbytes dh_share_length ->
    //base_point_low: plain spm{Plain.plain_to_bytesGT spm h1 base_point_low == base_point} ->
    im:ID.index_module{ID.id im == lbytes dh_share_length} ->
    kim:ID.index_module{ID.id kim == i:(plain_bytes spm * plain_bytes spm){b2t (smaller' dh_share_length (fst i) (snd i))}} ->
    km:Key.key_module kim{Key.get_keylen km = hash_length /\ Key.get_pm km == kpm} ->
    odh_module

val smaller: om:odh_module -> i1:lbytes om.dh_share_length -> i2:lbytes om.dh_share_length -> b:bool{b == smaller' om.dh_share_length i1 i2}

let get_base_point_low om =
  Plain.bytes_to_plainST om.spm om.base_point

#set-options "--z3rlimit 1000 --max_ifuel 2 --max_fuel 0"
// Basic types
let dh_share (om:odh_module) = plain om.spm
let dh_share_bytes (om:odh_module) = plain_bytes om.spm
let dh_exponent (om:odh_module) = plain om.epm
let dh_exponent_bytes (om:odh_module) = plain_bytes om.epm
let hash_output (om:odh_module) = plain om.kpm
let hash_output_bytes (om:odh_module) = plain_bytes om.kpm
let key_id (om:odh_module) =  i:(dh_share_bytes om * dh_share_bytes om){b2t (smaller om (fst i) (snd i))}

val hash_fun: #om:odh_module -> hash:(input:dh_share om -> ST (hash_output om)
      (requires (fun h0 -> True))
      (ensures (fun h0 output h1 ->
        Plain.plain_to_bytesGT h1 output == om.hash (Plain.plain_to_bytesGT h1 input)
        /\ modifies_none h0 h1
      ))){hash == om.hash_low}

val dh_exponentiate: #om:odh_module -> exp:(e:dh_exponent om -> sh:dh_share om -> ST (res:dh_share om)
      (requires (fun h0 -> True))
      (ensures (fun h0 res h1 ->
        Plain.plain_to_bytesGT h1 res == om.exponentiate (Plain.plain_to_bytesGT h1 e) (Plain.plain_to_bytesGT h1 sh)
        /\ modifies_none h0 h1
      ))
    ){exp == om.exponentiate_low}

//val share_from_exponent: #om:odh_module -> exp:dh_exponent om -> ST (sh:dh_share om)
//      (requires (fun h0 -> True))
//      (ensures (fun h0 res h1 ->
//        Plain.plain_to_bytesGT h1 res == om.exponentiate (Plain.plain_to_bytesGT h1 exp) om.base_point
//        /\ modifies_none h0 h1
//      ))

// Key types and key handling
val skey: om:odh_module -> Type0
val pkey: om:odh_module -> Type0
val get_pkey: #om:odh_module -> skey om -> pkey om
//val get_pkey_bytesGT: om:odh_module -> skey om -> GTot (pkey om)

//val compatible_keys_lemma: om:odh_module -> sk:skey om -> pk:pkey om -> Lemma
//  (requires (compatible_keys om sk pk))
//  (ensures (compatible_keys om sk pk ==> (Plain.plain_to_bytesGT om.spm pk) =!= Plain.plain_to_bytesGT om.spm (get_pkey om sk)))


// Getters
val get_hash_length: om:odh_module -> n:nat{n = om.hash_length}
val get_dh_share_length: om:odh_module -> n:nat{n = om.dh_share_length}
val get_dh_exponent_length: om:odh_module -> n:nat{n = om.dh_exponent_length}
val get_base_point: om:odh_module -> sh:dh_share_bytes om{sh == om.base_point}
val get_index_module: om:odh_module -> im:ID.index_module{im==om.im}
val get_key_index_module: om:odh_module -> kim:ID.index_module{kim==om.kim}
val get_key_module: om:odh_module -> kim:ID.index_module{kim == om.kim} -> km:Key.key_module kim{km==om.km /\ Key.get_keylen km = om.hash_length}
val get_kpm: om:odh_module -> kpm:plain_module{kpm == om.kpm}
val get_spm: om:odh_module -> spm:plain_module{spm == om.spm}
val get_epm: om:odh_module -> epm:plain_module{epm == om.epm}

val total_order_lemma: (#om:odh_module -> i1:dh_share_bytes om -> i2:dh_share_bytes om -> Lemma
  (requires True)
  (ensures
    (b2t (smaller om i1 i2) ==> (forall i. i <> i1 /\ i <> i2 /\ b2t (smaller om i i1) ==> b2t (smaller om i i2)))
    /\ (~ (b2t (smaller om i1 i2)) <==> (i1 = i2 \/ b2t (smaller om i2 i1)))))

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
val create: om_hash_length:nat{ 0 < om_hash_length /\ om_hash_length <= UInt.max_int 32} ->
            om_dh_share_length:nat{0 < om_dh_share_length /\ om_dh_share_length <= UInt.max_int 32} ->
            om_dh_exponent_length:nat{0 < om_dh_exponent_length /\ om_dh_exponent_length <= UInt.max_int 32} ->
            om_kpm:plain_module{Plain.valid_length om_kpm == Key.check_length om_hash_length} ->
            om_spm:plain_module{Plain.valid_length om_spm == Key.check_length om_dh_share_length} ->
            om_epm:plain_module{Plain.valid_length om_epm == Key.check_length om_dh_exponent_length} ->
            om_hash: (lbytes om_dh_share_length -> (lbytes om_hash_length)) ->
            om_hash_low: (input:plain om_spm -> ST (output:plain om_kpm)
              (requires (fun h0 -> True))
              (ensures (fun h0 output h1 ->
                Plain.plain_to_bytesGT h1 output == om_hash (Plain.plain_to_bytesGT h1 input)
                /\ modifies_none h0 h1
              ))
            ) ->
            om_exponentiate: (e:lbytes om_dh_exponent_length -> sh:lbytes om_dh_share_length -> Tot (lbytes om_dh_share_length)) ->
            om_exponentiate_low: (e:plain om_epm -> sh:plain om_spm -> ST (res:plain om_spm)
              (requires (fun h0 -> True))
              (ensures (fun h0 res h1 ->
                Plain.plain_to_bytesGT h1 res == om_exponentiate (Plain.plain_to_bytesGT h1 e) (Plain.plain_to_bytesGT h1 sh)
                /\ modifies_none h0 h1
              ))
            ) ->
            om_base_point: lbytes om_dh_share_length ->
            om_im:ID.index_module{ID.id om_im == lbytes om_dh_share_length} ->
            om_kim:ID.index_module{ID.id om_kim == i:(plain_bytes om_spm * plain_bytes om_spm){b2t (smaller' om_dh_share_length (fst i) (snd i))}} ->
            om_km:Key.key_module om_kim{Key.get_keylen om_km = om_hash_length /\ Key.get_pm om_km == om_kpm} ->
            om_rgn:Key.log_region ->
            om:odh_module{
              om.kim == om_kim /\
              (let om_km:(km:Key.key_module om.kim{Key.get_keylen km = om_hash_length}) = om_km in
              get_hash_length om = om_hash_length
              /\ om_kpm == om.kpm
              /\ om_epm == om.epm
              /\ om_spm == om.spm
              /\ get_dh_share_length om = om_dh_share_length
              /\ get_dh_exponent_length om = om_dh_exponent_length
              /\ get_index_module om == om_im
              /\ get_key_index_module om == om_kim
              /\ (let km:(k:Key.key_module om_kim{Key.get_keylen k = om_hash_length}) = om_km in
                let fun_km:(k:Key.key_module om_kim{Key.get_keylen k = om_hash_length}) = get_key_module om om_kim in
              fun_km == km)
              /\ hash_fun #om == om_hash_low
              /\ dh_exponentiate #om == om_exponentiate_low
              /\ om_base_point == om.base_point
              )
            }

(**
  A DH public key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
  or dishonest).
*)

//val pkey: om:odh_module -> pkey'


(**
  A DH secret key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
  or dishonest).
*)

//val skey: om:odh_module -> skey'


val pk_get_share_bytesGT: (#om:odh_module) -> (pk:pkey om) -> (sh:dh_share_bytes om)

(**
  A helper function to obtain the raw bytes of a DH public key.
*)
val pk_get_share: #om:odh_module -> pk:pkey om -> StackInline (dh_sh:dh_share om) //{dh_sh = pk.pk_share})
  (requires (fun h ->
    0 < normalize_term (Seq.length (pk_get_share_bytesGT pk))
    /\ normalize_term (Seq.length (pk_get_share_bytesGT pk)) <= UInt.max_int 32
  ))
  (ensures (fun (h0:mem) p h1 ->
     let len = Plain.plain_length p in
     len > 0
     /\ ~(Buffer.contains h0 p)
     /\ Buffer.live h1 p /\ Buffer.idx p = 0 /\ Plain.plain_length p = len
     /\ Buffer.frameOf p = h0.tip
     /\ Map.domain h1.h == Map.domain h0.h
     /\ Buffer.modifies_0 h0 h1
     /\ Plain.plain_to_bytesGT h1 p == pk_get_share_bytesGT pk
   ))


val get_skeyGT: #om:odh_module -> sk:skey om -> GTot (raw:dh_exponent_bytes om) //{raw=sk.sk_exp})

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
(**
A helper function to obtain the share that corresponds to a DH secret key.
*)
val sk_get_share_bytesGT: #om:odh_module -> sk:skey om -> GTot (dh_sh:dh_share_bytes om)
val sk_get_share: (#om:odh_module) -> (sk:skey om) -> StackInline (dh_sh:dh_share om)
  (requires (fun h ->
    0 < normalize_term (Seq.length (sk_get_share_bytesGT sk))
    /\ normalize_term (Seq.length (sk_get_share_bytesGT sk)) <= UInt.max_int 32
  ))
  (ensures (fun (h0:mem) p h1 ->
     let len = Plain.plain_length p in
     len > 0
     /\ ~(Buffer.contains h0 p)
     /\ Buffer.live h1 p /\ Buffer.idx p = 0 /\ Plain.plain_length p = len
     /\ Buffer.frameOf p = h0.tip
     /\ Map.domain h1.h == Map.domain h0.h
     /\ Buffer.modifies_0 h0 h1
     /\ Plain.plain_to_bytesGT h1 p == sk_get_share_bytesGT sk
   ))

val compatible_keys: #om:odh_module -> sk:skey om -> pk:pkey om -> t:Type0{t <==> pk_get_share_bytesGT pk =!= sk_get_share_bytesGT sk}

val leak_skey: #om:odh_module -> sk:skey om{ID.dishonest om.im (sk_get_share_bytesGT sk) \/ ~Flags.prf_odh} -> Tot (raw:dh_exponent_bytes om{raw=get_skeyGT sk})

val keygen: #om:odh_module -> ST (dh_pair:(pkey om * skey om))
  (requires (fun h0 -> True))
  (ensures (fun h0 dh_pair h1 ->
    modifies_none h0 h1
    /\ fst dh_pair == get_pkey (snd dh_pair)
  ))

val coerce_pkey: #om:odh_module -> dh_sh:dh_share_bytes om{ID.dishonest om.im (dh_sh) \/ ~Flags.prf_odh} -> (pkey om)

(**
  coerce_keypair allows the adversary to coerce a DH exponent into a DH private key. The corresponding DH public key
  is generated along with it. Both keys are considered dishonest and the id is considered unfresh after coercion.
*)
val coerce_keypair: #om:odh_module -> dh_exp:dh_exponent_bytes om{ID.dishonest om.im (om.exponentiate dh_exp om.base_point)} -> ((pkey om) * (skey om))

val compose_ids: om:odh_module -> s1:dh_share_bytes om -> s2:dh_share_bytes om{s2 <> s1} -> (i:(dh_share_bytes om * dh_share_bytes om){b2t (smaller om (fst i) (snd i))})

(**
  GTot specification of the prf_odh function for use in type refinements.
*)
val prf_odhGT: #om:odh_module -> sk:skey om -> pk:pkey om{compatible_keys sk pk} -> GTot (ho:hash_output_bytes om{ho == om.hash (om.exponentiate (get_skeyGT sk) (pk_get_share_bytesGT pk))})

//val lemma_shares: om:odh_module -> sk:skey om -> Lemma
//  (requires True)
//  (ensures (pk_get_share om (get_pkey om sk)) == sk_get_share om sk)
//  [ SMTPat (sk_get_share om sk)]
//
//val lemma_share_bytes: om:odh_module -> sk:skey om -> Lemma
//  (requires True)
//  (ensures (pk_get_share_bytesGT om (get_pkey om sk)) == sk_get_share_bytesGT om sk)
//  [ SMTPat (sk_get_share_bytesGT om sk)]
