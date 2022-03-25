module Impl.Noise.HKDF

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence

module BS = Lib.ByteSequence
open Lib.Buffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Impl.Noise.Types

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(* Note that it is legit to use one of the input buffers as an output buffer at the same time *)
inline_for_extraction noextract
type kdf_st (nc : iconfig) =
  hash : hash_t nc ->
  keylen : size_t { size_v keylen = 0 \/ size_v keylen = 32 \/
                    size_v keylen = public_key_size (get_config nc) } ->
  key : lbuffer uint8 keylen ->
  dst1 : lbuffer_or_null uint8 (hash_vs nc) ->
  dst2 : lbuffer_or_null uint8 (hash_vs nc) ->
  dst3 : lbuffer_or_null uint8 (hash_vs nc) ->
  Stack (rtype hash_return_type)
  (requires (fun h -> live h hash /\ live h key /\ live h dst1 /\ live h dst2 /\ live h dst3 /\
                    disjoint hash key /\ disjoint dst1 dst2 /\ disjoint dst2 dst3 /\
                    disjoint dst1 dst3 /\
                    (* functional pre: *)
                    get_hash_pre nc))
  (ensures (fun h0 _ h1 ->
    modifies3 dst1 dst2 dst3 h0 h1 /\
    begin
    let dst1_v, dst2_v, dst3_v = Spec.hkdf #(get_config nc) h0.[|hash|] h0.[|key|] in
    (~(g_is_null dst1) ==>
                h1.[|dst1 <: hash_t nc|] `S.equal` dst1_v) /\
    (~(g_is_null dst1 \/ g_is_null dst2) ==>
                h1.[|dst2 <: hash_t nc|] `S.equal` dst2_v) /\
    (~(g_is_null dst1 \/ g_is_null dst2 \/ g_is_null dst3) ==>
                h1.[|dst3 <: hash_t nc|] `S.equal` dst3_v)
    end))

(*** KDF *)
(** The compiler for the general HKDF function which will get extracted *)
inline_for_extraction noextract
val kdf_m (#nc : iconfig) (csti : config_impls nc) :
  kdf_st nc

(*** Derived KDFs functions helpers *)
inline_for_extraction noextract
let kdf1
  (#nc : iconfig)
  (kdf_impl : kdf_st nc)
  (hash : hash_t nc)
  (keylen : size_t)
  (key : hashable_key_t nc{length key == size_v keylen})
  (dst1 : hash_t nc) :
  Stack (rtype hash_return_type)
  (requires (fun h -> live h hash /\ live h key /\ live h dst1 /\ disjoint hash key /\ get_hash_pre nc))
  (ensures (fun h0 r h1 ->
    modifies1 dst1 h0 h1 /\
    begin
    let r_v = Spec.kdf1 #(get_config nc) h0.[|hash|]
                        h0.[|key <: lbuffer uint8 keylen|] in
    h1.[|dst1|] `S.equal` r_v
    end)) =
  assert(~(g_is_null key));
  assert(~(g_is_null dst1));
  kdf_impl hash keylen key dst1 (null #MUT #uint8) (null #MUT #uint8)

inline_for_extraction noextract
let kdf2
  (#nc : iconfig)
  (kdf_impl : kdf_st nc)
  (hash : hash_t nc)
  (keylen : size_t)
  (key : hashable_key_t nc{length key == size_v keylen})
  (dst1 : hash_t nc)
  (dst2 : hash_t nc) :
  Stack (rtype hash_return_type)
  (requires (fun h -> live h hash /\ live h key /\ live h dst1 /\ live h dst2 /\
                    disjoint hash key /\ disjoint dst1 dst2 /\
                    get_hash_pre nc))
  (ensures (fun h0 r h1 ->
    modifies2 dst1 dst2 h0 h1 /\
    begin
    let dst1_v, dst2_v = Spec.kdf2 #(get_config nc) h0.[|hash|]
                        h0.[|key <: lbuffer uint8 keylen|] in
    h1.[|dst1|] `S.equal` dst1_v /\
    h1.[|dst2|] `S.equal` dst2_v
    end)) =
  kdf_impl hash keylen key dst1 dst2 (null #MUT #uint8)

inline_for_extraction noextract
let kdf2_no_key
  (#nc : iconfig)
  (kdf_impl : kdf_st nc)
  (hash : hash_t nc)
  (dst1 : hash_t nc)
  (dst2 : hash_t nc) :
  Stack (rtype hash_return_type)
  (requires (fun h -> live h hash /\ live h dst1 /\ live h dst2 /\
                    disjoint dst1 dst2 /\
                    get_hash_pre nc))
  (ensures (fun h0 r h1 ->
    modifies2 dst1 dst2 h0 h1 /\
    begin
    let dst1_v, dst2_v = Spec.kdf2_no_key #(get_config nc) h0.[|hash|] in
    h1.[|dst1|] `S.equal` dst1_v /\
    h1.[|dst2|] `S.equal` dst2_v
    end)) =
  (**) let h0 = HST.get () in
  (**) assert(h0.[|null #MUT #uint8 <: lbuffer uint8 0ul|] `Seq.equal` BS.lbytes_empty);
  kdf_impl hash 0ul (null #MUT #uint8) dst1 dst2 (null #MUT #uint8)

inline_for_extraction noextract
let kdf3
  (#nc : iconfig)
  (kdf_impl : kdf_st nc)
  (hash : hash_t nc)
  (keylen : size_t)
  (key : hashable_key_t nc{length key == size_v keylen})
  (dst1 : hash_t nc)
  (dst2 : hash_t nc)
  (dst3 : hash_t nc) :
  Stack (rtype hash_return_type)
  (requires (fun h -> live h hash /\ live h key /\ live h dst1 /\ live h dst2 /\ live h dst3 /\
                    disjoint hash key /\ disjoint dst1 dst2 /\ disjoint dst2 dst3 /\
                    disjoint dst1 dst3 /\
                    get_hash_pre nc))
  (ensures (fun h0 r h1 ->
    modifies3 dst1 dst2 dst3 h0 h1 /\
    begin
    let dst1_v, dst2_v, dst3_v = Spec.kdf3 #(get_config nc) h0.[|hash|]
                                           h0.[|key <: lbuffer uint8 keylen|] in
    h1.[|dst1|] `S.equal` dst1_v /\
    h1.[|dst2|] `S.equal` dst2_v /\
    h1.[|dst3|] `S.equal` dst3_v
    end)) =
  kdf_impl hash keylen key dst1 dst2 dst3
