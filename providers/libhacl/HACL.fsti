module HACL

///
/// Curve25519
///

val hacl_curve25519_scalarmult:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  basepoint:uint8_p{length basepoint = 32} ->
  Stack unit
    (requires (fun h -> Buffer.live h mypublic /\ Buffer.live h secret /\ Buffer.live h basepoint))
    (ensures (fun h0 _ h1 -> Buffer.live h1 mypublic /\ modifies_1 mypublic h0 h1
     /\ Buffer.live h0 mypublic /\ Buffer.live h0 secret /\ Buffer.live h0 basepoint
     /\ (let secret = reveal_sbytes (as_seq h0 secret) in
        let basepoint = reveal_sbytes (as_seq h0 basepoint) in
        let mypublic = reveal_sbytes (as_seq h1 mypublic) in
        mypublic == Spec.Curve25519.(scalarmult secret basepoint))
     ))

///
/// Chacha20
///

val hacl_chacha20_init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  Stack log_t
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1
      /\ invariant log h1 st
      /\ (match Ghost.reveal log with MkLog k' n' -> k' == reveal_sbytes (as_seq h0 k)
           /\ n' == reveal_sbytes (as_seq h0 n))))

val hacl_chacha20_update:
  output:uint8_p{length output = 64} ->
  plain:uint8_p{disjoint output plain /\ length plain = 64} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:U32.t{U32.v ctr + 1 < pow2 32} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ updated_log == log
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (chacha20_cipher k n (U32.v ctr)))))

val hacl_chacha20_update_last:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len < 64 /\ UInt32.v len > 0} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt32.t{UInt32.v ctr + (length plain / 64) < pow2 32} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == (let mask = chacha20_cipher k n (UInt32.v ctr+(UInt32.v len / 64)) in
               let mask = Seq.slice mask 0 (UInt32.v len) in
               Spec.CTR.xor #(UInt32.v len) plain mask))))

val hacl_chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         let k = reveal_sbytes (as_seq h0 key) in
         let n = reveal_sbytes (as_seq h0 nonce) in
         let ctr = U32.v ctr in
         o == Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n ctr plain)))

///
/// Poly1305_64
///

val hacl_poly1305_64_onetimeauth:
  mac:uint8_p{length mac = 16} ->
  input:uint8_p{disjoint input mac} ->
  len:uint64_t{v len < pow2 32 /\ v len = length input} ->
  key:uint8_p{disjoint mac key /\ length key = 32} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1 /\ live h0 input /\ live h0 key
      /\ h1.[mac] == Spec.Poly1305.poly1305 h0.[input] h0.[key]))

///
/// Poly1305_32
///

val hacl_poly1305_32_onetimeauth:
  mac:uint8_p{length mac = 16} ->
  input:uint8_p{disjoint input mac} ->
  len:uint64_t{v len < pow2 32 /\ v len = length input} ->
  key:uint8_p{disjoint mac key /\ length key = 32} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1 /\ live h0 input /\ live h0 key
      /\ h1.[mac] == Spec.Poly1305.poly1305 h0.[input] h0.[key]))

///
/// SHA2
///

val hacl_sha2_256_size_hash : FStar.UInt32.t
val hacl_sha2_384_size_hash : FStar.UInt32.t
val hacl_sha2_512_size_hash : FStar.UInt32.t

val hacl_sha2_256_size_block : FStar.UInt32.t
val hacl_sha2_384_size_block : FStar.UInt32.t
val hacl_sha2_512_size_block : FStar.UInt32.t

val hacl_sha2_256_size_state : FStar.UInt32.t
val hacl_sha2_384_size_state : FStar.UInt32.t
val hacl_sha2_512_size_state : FStar.UInt32.t

val hacl_sha2_256_alloc:
  unit ->
  StackInline (state:uint32_p{length state = v hacl_sha2_256_size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

val hacl_sha2_384_alloc:
  unit ->
  StackInline (state:uint64_p{length state = v hacl_sha2_384_size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

val hacl_sha2_512_alloc:
  unit ->
  StackInline (state:uint64_p{length state = v hacl_sha2_512_size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

val hacl_sha2_256_init:
  state:uint32_p{length state = v hacl_sha2_256_size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H32.v counter = 0)))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h32s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h32s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H32.v counter = 0)))

val hacl_sha2_384_init:
  state:uint64_p{length state = v hacl_sha2_384_size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H64.v counter = 0)))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h64s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h64s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H64.v counter = 0)))

val hacl_sha2_512_init:
  state:uint64_p{length state = v hacl_sha2_512_size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H64.v counter = 0)))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h64s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h64s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H64.v counter = 0)))


val hacl_sha2_256_update:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  Hacl.Spec.Endianness.reveal_h32s seq_k == Spec.k /\ H32.v counter < (pow2 32 - 1))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_block = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H32.v counter_1 = H32.v counter_0 + 1 /\ H32.v counter_1 < pow2 32
                  /\ (Hacl.Spec.Endianness.reveal_h32s seq_hash_1 == Spec.update (Hacl.Spec.Endianness.reveal_h32s seq_hash_0) (Hacl.Spec.Endianness.reveal_sbytes seq_block)))))

val hacl_sha2_384_update:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  Hacl.Spec.Endianness.reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 1))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_block = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H64.v counter_1 = H64.v counter_0 + 1 /\ H64.v counter_1 < pow2 64
                  /\ (Hacl.Spec.Endianness.reveal_h64s seq_hash_1 == Spec.update (Hacl.Spec.Endianness.reveal_h64s seq_hash_0) (Hacl.Spec.Endianness.reveal_sbytes seq_block)))))

val hacl_sha2_512_update:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  Hacl.Spec.Endianness.reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 1))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_block = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H64.v counter_1 = H64.v counter_0 + 1 /\ H64.v counter_1 < pow2 64
                  /\ (Hacl.Spec.Endianness.reveal_h64s seq_hash_1 == Spec.update (Hacl.Spec.Endianness.reveal_h64s seq_hash_0) (Hacl.Spec.Endianness.reveal_sbytes seq_block)))))


val hacl_sha2_256_update_multi:
  state :uint32_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data /\
                 (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  Hacl.Spec.Endianness.reveal_h32s seq_k == Spec.k /\ H32.v counter < pow2 32 - (v n))))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1 /\
                 (let seq_hash0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_blocks = as_seq h0 data in
                  let seq_counter0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter0 = Seq.index seq_counter0 0 in
                  let counter1 = Seq.index seq_counter1 0 in
                  seq_k0 == seq_k1 /\
                  H32.v counter1 = H32.v counter0 + (v n) /\
                  H32.v counter1 < pow2 32 /\
                  Hacl.Spec.Endianness.reveal_h32s seq_hash1 ==
                  Spec.update_multi (Hacl.Spec.Endianness.reveal_h32s seq_hash0) (Hacl.Spec.Endianness.reveal_sbytes seq_blocks) )))


val hacl_sha2_384_update_multi:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint64_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data /\
                 (let seq_k = Seq.slice (as_seq h0 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  Hacl.Spec.Endianness.reveal_h64s seq_k == Spec.k /\ H64.v counter < pow2 64 - (v n))))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1 /\
                 (let seq_hash0 = Seq.slice (as_seq h0 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash1 = Seq.slice (as_seq h1 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
                  let seq_k0 = Seq.slice (as_seq h0 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_k1 = Seq.slice (as_seq h1 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_blocks = as_seq h0 data in
                  let seq_counter0 = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let seq_counter1 = Seq.slice (as_seq h1 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let counter0 = Seq.index seq_counter0 0 in
                  let counter1 = Seq.index seq_counter1 0 in
                  seq_k0 == seq_k1 /\
                  H64.v counter1 = H64.v counter0 + (v n) /\
                  H64.v counter1 < pow2 64 /\
                  Hacl.Spec.Endianness.reveal_h64s seq_hash1 ==
                  Spec.update_multi (Hacl.Spec.Endianness.reveal_h64s seq_hash0) (Hacl.Spec.Endianness.reveal_sbytes seq_blocks) )))

val hacl_sha2_512_update_multi:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint64_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data /\
                 (let seq_k = Seq.slice (as_seq h0 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  Hacl.Spec.Endianness.reveal_h64s seq_k == Spec.k /\ H64.v counter < pow2 64 - (v n))))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1 /\
                 (let seq_hash0 = Seq.slice (as_seq h0 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash1 = Seq.slice (as_seq h1 state) (U64.v pos_whash_w) (U64.(v pos_whash_w + v size_whash_w)) in
                  let seq_k0 = Seq.slice (as_seq h0 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_k1 = Seq.slice (as_seq h1 state) (U64.v pos_k_w) (U64.(v pos_k_w + v size_k_w)) in
                  let seq_blocks = as_seq h0 data in
                  let seq_counter0 = Seq.slice (as_seq h0 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let seq_counter1 = Seq.slice (as_seq h1 state) (U64.v pos_count_w) (U64.(v pos_count_w + v size_count_w)) in
                  let counter0 = Seq.index seq_counter0 0 in
                  let counter1 = Seq.index seq_counter1 0 in
                  seq_k0 == seq_k1 /\
                  H64.v counter1 = H64.v counter0 + (v n) /\
                  H64.v counter1 < pow2 64 /\
                  Hacl.Spec.Endianness.reveal_h64s seq_hash1 ==
                  Spec.update_multi (Hacl.Spec.Endianness.reveal_h64s seq_hash0) (Hacl.Spec.Endianness.reveal_sbytes seq_blocks) )))

val hacl_sha2_256_update_last:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint32_t {v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U32.div len size_block in
                  Hacl.Spec.Endianness.reveal_h32s seq_k == Spec.k /\ H32.v counter < (pow2 32 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = U32.(H32.v (Seq.index count 0) * (v size_block)) in
                  (Hacl.Spec.Endianness.reveal_h32s seq_hash_1) == Spec.update_last (Hacl.Spec.Endianness.reveal_h32s seq_hash_0) prevlen seq_data)))

val hacl_sha2_384_update_last:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint64_t {U64.v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U64.div len (u32_to_u64 size_block) in
                  Hacl.Spec.Endianness.reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = H64.((H64.v (Seq.index count 0)) * (U32.v size_block)) in
                  Hacl.Spec.Endianness.reveal_h64s seq_hash_1 == Spec.update_last (Hacl.Spec.Endianness.reveal_h64s seq_hash_0) prevlen seq_data)))

val hacl_sha2_512_update_last:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint64_t {U64.v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U64.div len (u32_to_u64 size_block) in
                  Hacl.Spec.Endianness.reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = H64.((H64.v (Seq.index count 0)) * (U32.v size_block)) in
                  Hacl.Spec.Endianness.reveal_h64s seq_hash_1 == Spec.update_last (Hacl.Spec.Endianness.reveal_h64s seq_hash_0) prevlen seq_data)))

val hacl_sha2_256_finish:
  state :uint32_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                  seq_hash = Spec.finish (Hacl.Spec.Endianness.reveal_h32s seq_hash_w))))

val hacl_sha2_384_finish:
  state :uint64_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash_final /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h1 state /\ live h0 state
                  /\ live h1 hash /\ live h0 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.finish (Hacl.Spec.Endianness.reveal_h64s seq_hash_w))))

val hacl_sha2_512_finish:
  state :uint64_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash_final /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h1 state /\ live h0 state
                  /\ live h1 hash /\ live h0 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.finish (Hacl.Spec.Endianness.reveal_h64s seq_hash_w))))

val hacl_sha2_256:
  hash :uint8_p {length hash = v size_hash} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 input) in
                  let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.hash seq_input)))

val hacl_sha2_384:
  hash :uint8_p {length hash = v size_hash_final} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 input) in
                  let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.hash seq_input)))

val hacl_sha2_512:
  hash :uint8_p {length hash = v size_hash_final} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 input) in
                  let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.hash seq_input)))


///
/// HMAC
///

val hacl_hmac_sha2_256_wrap_key:
  output :uint8_p  {length output = v Hash.size_block} ->
  key    :uint8_p  {disjoint output key} ->
  len    :uint32_t {v len = length key /\ v len < Spec_Hash.max_input_len_8} ->
  Stack unit
        (requires (fun h -> live h output /\ live h key /\
                  reveal_sbytes (as_seq h output) == Seq.create (v Hash.size_block) 0uy))
        (ensures  (fun h0 _ h1 -> live h1 output /\ live h1 key /\ live h0 output /\ live h0 key /\ modifies_1 output h0 h1
                  /\ reveal_sbytes (as_seq h0 output) == Seq.create (v Hash.size_block) 0uy
                  /\ reveal_sbytes (as_seq h1 output) == Spec.wrap_key (reveal_sbytes (as_seq h0 key))))

val hacl_hmac_sha2_256_hmac_core:
  mac  :uint8_p  {length mac = v Hash.size_hash} ->
  key  :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  data :uint8_p  {length data + v Hash.size_block < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  len  :uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1
                             /\ (as_seq h1 mac == Spec.hmac_core (as_seq h0 key) (as_seq h0 data))))

val hacl_hmac_sha2_256_hmac:
  mac     :uint8_p  {length mac = v Hash.size_hash} ->
  key     :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  keylen  :uint32_t {v keylen = length key} ->
  data    :uint8_p  {length data + v Hash.size_block < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  datalen :uint32_t {v datalen = length data} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1
                             /\ (as_seq h1 mac == Spec.hmac (as_seq h0 key) (as_seq h0 data))))

///
/// Ed25519
///

val hacl_ed25519_sign:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h1 signature /\ modifies_1 signature h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg]))

val hacl_ed25519_verify:
  public:uint8_p{length public = 32} ->
  msg:uint8_p ->
  len:UInt32.t{length msg = UInt32.v len /\ length msg < pow2 32 - 64} ->
  signature:uint8_p{length signature = 64} ->
  Stack bool
    (requires (fun h -> live h public /\ live h msg /\ live h signature))
    (ensures (fun h0 z h1 -> modifies_0 h0 h1 /\ live h0 msg /\ live h0 public /\ live h0 signature /\
      z == Spec.Ed25519.(verify (as_seq h0 public) (as_seq h0 msg) (as_seq h0 signature))))

val hacl_ed25519_secret_to_public:
  out:hint8_p{length out = 32} ->
  secret:hint8_p{length secret = 32 /\ disjoint out secret} ->
  Stack unit
    (requires (fun h -> live h out /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 secret /\ live h1 out /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.Ed25519.secret_to_public h0.[secret]))
