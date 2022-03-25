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

friend Spec.Noise.CryptoPrimitives

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

/// First write a version of HKDF without any buffer allocation
inline_for_extraction noextract
type kdf_with_buffers_st (nc : iconfig) =
  (* The temporary output buffer *)
  output : lbuffer uint8 (size (hash_vsv nc + 1)) ->
  (* The secret buffer *)
  secret : hash_t nc ->
  (* Same parameters as for the resulting KDF *)
  hash : hash_t nc ->
  keylen : size_t { size_v keylen = 0 \/ size_v keylen = 32 \/
                    size_v keylen = public_key_size (get_config nc) } ->
  key : lbuffer uint8 keylen ->
  dst1 : lbuffer_or_null uint8 (hash_vs nc) ->
  dst2 : lbuffer_or_null uint8 (hash_vs nc) ->
  dst3 : lbuffer_or_null uint8 (hash_vs nc) ->
  Stack (rtype hash_return_type)
  (requires (fun h -> live h output /\ live h secret /\
                    disjoint output secret /\ disjoint output hash /\ disjoint output key /\
                    disjoint output dst1 /\ disjoint output dst2 /\ disjoint output dst3 /\
                    disjoint secret hash /\ disjoint secret key /\
                    disjoint secret dst1 /\ disjoint secret dst2 /\ disjoint secret dst3 /\
                    live h hash /\ live h key /\ live h dst1 /\ live h dst2 /\ live h dst3 /\
                    disjoint dst1 dst2 /\ disjoint dst2 dst3 /\ disjoint dst1 dst3 /\
                    (* functional pre: *)
                    get_hash_pre nc))
  (ensures (fun h0 _ h1 ->
    modifies5 output secret dst1 dst2 dst3 h0 h1 /\
    begin
    let dst1_v, dst2_v, dst3_v = Spec.hkdf #(get_config nc) h0.[|hash|] h0.[|key|] in
    (~(g_is_null dst1) ==>
                h1.[|dst1 <: hash_t nc|] `S.equal` dst1_v) /\
    (~(g_is_null dst1 \/ g_is_null dst2) ==>
                h1.[|dst2 <: hash_t nc|] `S.equal` dst2_v) /\
    (~(g_is_null dst1 \/ g_is_null dst2 \/ g_is_null dst3) ==>
                h1.[|dst3 <: hash_t nc|] `S.equal` dst3_v)
    end))

inline_for_extraction noextract
val kdf_with_buffers_m (#nc : iconfig) (csti : config_impls nc) : kdf_with_buffers_st nc

#push-options "--z3rlimit 100"
let kdf_with_buffers_m #nc csti output secret hash keylen key dst1 dst2 dst3 =
  [@inline_let] let a = get_hash_alg (get_config nc) in
  [@inline_let] let output_len = size (hash_vsv nc + 1) in
  let output_hash = sub output 0ul (hash_vs nc) in
  let output1 = sub output 0ul 1ul in
  let output2 : Ghost.erased _ = gsub output (hash_vs nc) 1ul in
  (**) let h0 = HST.get () in
  (* Extract *)
  ihmac csti secret (hash_vs nc) hash keylen key;
  (**) let h1 = HST.get () in
  (**) assert(Seq.equal h1.[|secret|] (ahmac a h0.[|hash|] h0.[|key|]));
  (* Expand first key *)
  if not (is_null dst1) then
    begin
    upd output 0ul (u8 1);
    let h1_0 = HST.get () in
    (**) assert(h1_0.[|output1|] `Seq.equal` (Seq.create 1 (u8 1)));
    ihmac csti output_hash (hash_vs nc) secret 1ul output1;
    (**) let h1_1 = HST.get () in
    (**) assert(Seq.equal h1_1.[|output_hash|]
    (**)        (ahmac a h1_0.[|secret|] h1_0.[|output1|]));
    update_sub (dst1 <: hash_t nc) 0ul (hash_vs nc) output_hash;
    (**) let h1_2 = HST.get () in
    (**) assert(Seq.equal h1_2.[|dst1 <: hash_t nc|]
    (**)        (ahmac a h1.[|secret|] (Seq.create 1 (u8 1))));    
    (* Expand second key *)
    if not (is_null dst2) then
      begin
      (**) let h2_0 = HST.get () in
      upd output (hash_vs nc) (u8 2);
      (**) let h2_1 = HST.get () in
      (**) assert(h2_1.[|output|] `Seq.equal`
      (**)       (Seq.append h2_0.[|(dst1 <: hash_t nc)|] (Seq.create 1 (u8 2))));
      ihmac csti output_hash (hash_vs nc) secret output_len output;
      update_sub (dst2 <: hash_t nc) 0ul (hash_vs nc) output_hash;
      (* Expand third key *)
      if not (is_null dst3) then
        begin
        (**) let h3_0 = HST.get () in
        upd output (hash_vs nc) (u8 3);
        (**) let h3_1 = HST.get () in
        (**) assert(h3_1.[|output|] `Seq.equal`
        (**)       (Seq.append h3_0.[|(dst2 <: hash_t nc)|] (Seq.create 1 (u8 3))));
        ihmac csti output_hash (hash_vs nc) secret output_len output;
        update_sub (dst3 <: hash_t nc) 0ul (hash_vs nc) output_hash
        end
      end
    end
#pop-options

#push-options "--z3rlimit 50"
let kdf_m #nc csti hash keylen key dst1 dst2 dst3 =
  push_frame ();
  (* Allocate the buffers *)
  let output = create #uint8 (size (hash_vsv nc + 1)) (u8 0) in
  let secret = create #uint8 (hash_vs nc) (u8 0) in

  (* Apply HKDF *)
  kdf_with_buffers_m #nc csti output secret hash keylen key dst1 dst2 dst3;
  
  (* Don't leave any sensitive information on the stack *)
  Lib.Memzero0.memzero (output <: LowStar.Buffer.buffer uint8) (size (hash_vsv nc + 1));
  Lib.Memzero0.memzero (secret <: LowStar.Buffer.buffer uint8) (hash_vs nc);
  pop_frame ()
#pop-options
