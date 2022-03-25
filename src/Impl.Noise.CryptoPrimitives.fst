module Impl.Noise.CryptoPrimitives

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence

module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module BS = Lib.ByteSequence
module LB = Lib.Buffer
open Lib.Buffer
module BB = Lib.ByteBuffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Meta.Noise
open Impl.Noise.Types

/// DH
module DH = Spec.Agile.DH

module ImplCFields = Hacl.Impl.Curve25519.Fields.Core
module ImplC51 = Hacl.Curve25519_51
module ImplC64 = Hacl.Curve25519_64
module ImplHPKEDH = Hacl.HPKE.Interface.DH

/// AEAD
module AEAD = Spec.Agile.AEAD
friend Spec.Agile.AEAD

module ImplPolyFields = Hacl.Impl.Poly1305.Fields
module ImplCP32 = Hacl.Chacha20Poly1305_32
module ImplCP128 = Hacl.Chacha20Poly1305_128
module ImplCP256 = Hacl.Chacha20Poly1305_256


/// Hash
module Hash = Spec.Agile.Hash
friend Spec.Agile.Hash

module ImplSHA2 = Hacl.Hash.SHA2
module ImplBlake2Core = Hacl.Impl.Blake2.Core
module ImplBlake2s32 = Hacl.Blake2s_32
module ImplBlake2s128 = Hacl.Blake2s_128
module ImplBlake2b32 = Hacl.Blake2b_32
module ImplBlake2b256 = Hacl.Blake2b_256

friend Spec.Noise.CryptoPrimitives

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** DH *)
(**** Curve25519 *)

let dh_sp_c25519 fs dest priv =
  begin
  match with_norm(fs) with
  | ImplCFields.M51 -> ImplC51.secret_to_public dest priv
  | ImplCFields.M64 -> ImplC64.secret_to_public dest priv
  end;
  success _

let dh_c25519 fs dest priv pub =
  let b =
    match with_norm(fs) with
    | ImplCFields.M51 -> ImplC51.ecdh dest priv pub
    | ImplCFields.M64 -> ImplC64.ecdh dest priv pub
  in
  convert_subtype #dh_rtype #(rtype dh_hash_return_type)
                  (if b then CSuccess else CDH_error)

(*** AEAD *)
(**** AES GCM *)

module ImplEAEAD = EverCrypt.AEAD
open EverCrypt.Error

#push-options "--z3rlimit 100"
let aead_encrypt_aes256_gcm key nonce aad_len aad plen plain cipher =
  (**) assert_norm(Spec.aaead_max_input AEAD.AES256_GCM <= pow2 31);
  (**) let h0 = HST.get () in
  push_frame ();
  let n8 : lbuffer uint8 8ul = create 8ul (u8 0) in
  BB.uint_to_bytes_be n8 (secret nonce);
  (**) let h3 = HST.get () in
  (**) assert(h3.[|n8|] == BS.uint_to_bytes_be (secret nonce));
  (**) let h4 = HST.get () in
  let output : lbuffer uint8 plen = sub cipher 0ul plen in
  let tag : aead_tag_t = sub cipher plen aead_tag_vs in
  let r = EverCrypt.AEAD.encrypt_expand_aes256_gcm_no_check key n8 8ul
                         aad aad_len plain plen output tag in
  (**) assert(r == EverCrypt.Error.Success);
  (**) let h5 = HST.get () in
  (**) assert(
  (**)   let h0 = h4 in
  (**)   let h1 = h5 in
  (**)   Seq.equal (Seq.append h1.[|output|] h1.[|tag|])
  (**)       (Spec.Agile.AEAD.encrypt #AEAD.AES256_GCM
  (**)                     h0.[|key|] h0.[|n8|] h0.[|aad|] h0.[|plain|]));
  (**) assert(h5.[|cipher|] `S.equal` (Seq.append h5.[|output|] h5.[|tag|]));
  (* Don't leave information on the stack - not sure that this is necessary *)
  Lib.Memzero0.memzero #uint8 n8 8ul;
  pop_frame();
  convert_subtype #unit #(rtype encrypt_return_type) ()
#pop-options

#push-options "--z3rlimit 100"
let aead_decrypt_aes256_gcm key nonce aad_len aad plen plain cipher =
  (**) assert_norm(Spec.aaead_max_input AEAD.AES256_GCM <= pow2 31);
  (**) let h0 = HST.get () in
  push_frame ();
  let n8 : lbuffer uint8 8ul = create 8ul (u8 0) in
  BB.uint_to_bytes_be n8 (secret nonce);
  (**) let h3 = HST.get () in
  (**) assert(h3.[|n8|] == BS.uint_to_bytes_be (secret nonce));
  (**) let h4 = HST.get () in
  let cplain : lbuffer uint8 plen = sub cipher 0ul plen in
  let tag : aead_tag_t = sub cipher plen aead_tag_vs in
  let r = EverCrypt.AEAD.decrypt_expand_aes256_gcm_no_check key n8 8ul
                            aad aad_len cplain plen tag plain in
  (**) assert(r == EverCrypt.Error.Success \/ r == AuthenticationFailure);
  (**) let h5 = HST.get () in
  (**) assert(h5.[|cipher|] `S.equal` (Seq.append h5.[|cplain|] h5.[|tag|]));
  (**) assert(
  (**)   let h0 = h4 in
  (**)   let h1 = h5 in
  (**)   let opt_plain_v = Spec.Agile.AEAD.decrypt #AEAD.AES256_GCM
  (**)                          h0.[|key|] h0.[|n8|] h0.[|aad|] h0.[|cipher|] in
  (**)   match r, opt_plain_v with
  (**)   | EverCrypt.Error.Success, Some plain_v ->
  (**)     h1.[|plain|] `Seq.equal` plain_v
  (**)   | AuthenticationFailure, None -> True
  (**)   | _ -> False);
  (* Don't leave information on the stack - not sure that this is necessary *)
  Lib.Memzero0.memzero #uint8 n8 8ul;
  pop_frame();
  convert_subtype #decrypt_rtype #(rtype decrypt_return_type)
    begin match r with
    | EverCrypt.Error.Success -> CSuccess
    | AuthenticationFailure -> CDecrypt_error
    end
#pop-options

(**** Chacha20Poly1305 *)

inline_for_extraction noextract
val compute_nonce12 :
  (be : bool) ->
  (nonce12 : lbuffer uint8 (size 12)) ->
  (nonce : pub_uint64) ->
  Stack unit
  (requires (fun h -> live h nonce12 /\
                    h.[|nonce12|] `S.equal` (S.create 12 (u8 0))))
  (ensures (fun h0 _ h1 ->
              modifies1 nonce12 h0 h1 /\
              (let n8 = if be then BS.uint_to_bytes_be (secret nonce)
                              else BS.uint_to_bytes_le (secret nonce) in
               S.equal h1.[|nonce12|] ((S.create 4 (u8 0)) @| n8))))

#push-options "--z3rlimit 50"
let compute_nonce12 be nonce12 nonce =
  (**) let h0 = HST.get () in
  (**) let nonce12_begin : Ghost.erased (lbuffer uint8 (size 4)) =
                           gsub nonce12 0ul (size 4) in
  let nonce12_end : lbuffer uint8 (size 8) = sub nonce12 (size 4) (size 8) in
  (**) let nonce_byteseq : Ghost.erased (lseq uint8 8) =
           if be then BS.uint_to_bytes_be (secret nonce)
                 else BS.uint_to_bytes_le (secret nonce) in
  if be then BB.uint_to_bytes_be nonce12_end (secret nonce)
        else BB.uint_to_bytes_le nonce12_end (secret nonce);
  (**) let h1 = HST.get () in
  (* Reason about the beginning of the full nonce *)
  (**) calc (S.equal) {
  (**)   S.sub h1.[|nonce12|] 0 4;
  (**) (S.equal) {}
  (**)   S.sub h0.[|nonce12|] 0 4;
  (**) (S.equal) {}
  (**)   h0.[|nonce12_begin|];
  (**) (S.equal) {}
  (**)   S.create 4 (u8 0);
  (**) };
  (* Reason about the end of the full nonce *)
  (**) assert((S.sub h1.[|nonce12|] 4 8) `S.equal` nonce_byteseq);
  (* Reason about the full nonce *)
  (**) calc (S.equal) {
  (**)   h1.[|nonce12|];
  (**) (S.equal) { lemma_lslice h1.[|nonce12|] 4 }
  (**)   (slice h1.[|nonce12|] 0 4) @| (slice h1.[|nonce12|] 4 12);
  (**) (S.equal) {}
  (**)   (S.create 4 (u8 0)) @| nonce_byteseq;
  (**) }
#pop-options

#push-options "--z3rlimit 200"
let aead_encrypt_cp fs key nonce aad_len aad plen plain cipher =
  push_frame ();
  let n12 = create 12ul (u8 0) in
  compute_nonce12 (**) false (**) n12 nonce;
  let output : lbuffer uint8 plen = sub cipher 0ul plen in
  let tag : aead_tag_t = sub cipher plen aead_tag_vs in
  begin match with_norm(fs) with
  | ImplPolyFields.M32 -> ImplCP32.aead_encrypt key n12 aad_len aad plen plain output tag
  | ImplPolyFields.M128 -> ImplCP128.aead_encrypt key n12 aad_len aad plen plain output tag
  | ImplPolyFields.M256 -> ImplCP256.aead_encrypt key n12 aad_len aad plen plain output tag
  end;
  (**) let h1 = HST.get () in
  (**) assert(h1.[|cipher|] `S.equal` (concat h1.[|output|] h1.[|tag|]));
  (* Don't leave information on the stack - not sure that this is necessary *)
  Lib.Memzero0.memzero #uint8 n12 12ul;
  pop_frame();
  convert_subtype #unit #(rtype encrypt_return_type) ()
#pop-options

#push-options "--z3rlimit 200"
let aead_decrypt_cp fs key nonce aad_len aad plen plain cipher =
  push_frame ();
  let n12 = create 12ul (u8 0) in
  compute_nonce12 false n12 nonce;
  let output : lbuffer uint8 plen = sub cipher 0ul plen in
  let tag : aead_tag_t = sub cipher plen aead_tag_vs in
  let r =
    match with_norm(fs) with
    | ImplPolyFields.M32 -> ImplCP32.aead_decrypt key n12 aad_len aad plen plain output tag
    | ImplPolyFields.M128 -> ImplCP128.aead_decrypt key n12 aad_len aad plen plain output tag
    | ImplPolyFields.M256 -> ImplCP256.aead_decrypt key n12 aad_len aad plen plain output tag
  in
  (**) let h1 = HST.get () in
  (**) assert(h1.[|cipher|] `S.equal` (concat h1.[|output|] h1.[|tag|]));
  (* Don't leave information on the stack - not sure that this is necessary *)
  Lib.Memzero0.memzero #uint8 n12 12ul;
  pop_frame();
  convert_subtype #decrypt_rtype #(rtype decrypt_return_type)
    (if r =. 0ul then CSuccess else CDecrypt_error)
#pop-options

(*** Hash *)
(**** General *)
/// We define several utilities to easily generate the implementations for do_hash2.
/// There are two possibilities:
/// - either we do one-time hash on the concatenation of the current hash and the input
/// - or we use incremental hash (preferred if available)

inline_for_extraction noextract
val do_hash2 (#a : hash_alg) (#pre : Type0) (impl : do_hash_st a pre) : do_hash2_st a pre

let do_hash2 #a #pre impl hash inlen input =
  push_frame ();
  let data_len : size_t = size (ahash_size a) +. inlen in
  let data : lbuffer uint8 data_len = create data_len (u8 0) in
  concat2 (ahash_vs a) hash inlen input data;
  let _ = impl hash data_len data in
  (* There is no need to memzero the data *)
//  Lib.Memzero0.memzero #uint8 data data_len;
  pop_frame ();
  convert_subtype #unit #(rtype hash_return_type) ()

module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface

inline_for_extraction noextract
val do_incr_hash2 //(#a : hash_alg) (#pre : Type0)
                  (#index : Type0)
                  (#c : I.block index)
                  (#i:index)
                  (#t:Type0 { t == (I.Stateful?.s (I.Block?.state c)) i })
                  (#t':Type0 { t' == I.optional_key i c.I.km c.I.key })
                  (alloca : F.alloca_st c i t t')
                  (update : F.update_st c i t t')
                  (finish : F.finish_st c i t t')
                  (k : (I.Stateful?.s (I.Block?.key c) i)) :
  hash : lbuffer uint8 (I.Block?.output_len c i) ->
  inlen : size_t ->
  input : lbuffer uint8 inlen ->
  Stack (rtype hash_return_type)
  (requires (fun h ->
    I.Stateful?.invariant (I.Block?.key c) #i h k /\
    live h hash /\ live h input /\
    v (I.Block?.output_len c i) + size_v inlen <= I.Block?.max_input_length c i
    ))
  (ensures (fun h0 _ h1 ->
    modifies1 hash h0 h1 /\
    h1.[|hash|] `S.equal`
    I.Block?.spec_s c i (I.Stateful?.v (I.Block?.key c) i h0 k)
                        (Seq.append h0.[|hash|] h0.[|input|])))

let do_incr_hash2 #index #c #i #t #t' alloca update finish k =
  fun hash inlen input ->
  (**) let h0 = HST.get () in
  push_frame ();
  (**) let h1 = HST.get () in
  (**) I.Stateful?.frame_invariant (I.Block?.key c) B.loc_none k h0 h1;
  (**) assert(I.Stateful?.invariant (I.Block?.key c) h1 k);
  let s = alloca k in
  update s hash (I.Block?.output_len c i);
  (**) assert(Seq.Base.append Seq.Base.empty h0.[|hash|] `Seq.equal` h0.[|hash|]);
  update s input inlen;
  finish s hash;
  (* There is no need to memzero the state *)
  pop_frame ();
  convert_subtype #unit #(rtype hash_return_type) ()

(**** SHA2 *)

let hash_sha2_256 output inlen input =
  ImplSHA2.hash_256 input inlen output;
  convert_subtype #unit #(rtype hash_return_type) ()

let hash_sha2_512 output inlen input =
  ImplSHA2.hash_512 input inlen output;
  convert_subtype #unit #(rtype hash_return_type) ()

let hash2_sha2_256 =
  do_incr_hash2 Hacl.Streaming.SHA2.alloca_256
                Hacl.Streaming.SHA2.update_256
                Hacl.Streaming.SHA2.finish_256
                ()

let hash2_sha2_512 =
  do_incr_hash2 Hacl.Streaming.SHA2.alloca_512
                Hacl.Streaming.SHA2.update_512
                Hacl.Streaming.SHA2.finish_512
                ()

let hmac_sha2_256 output keylen key datalen data =
  (**) normalize_term_spec(Hash.max_input_length Hash.SHA2_256);
  (**) assert(length key <= Hash.max_input_length Hash.SHA2_256);
  (**) assert(Spec.Agile.HMAC.keysized Hash.SHA2_256 (length key));
  Hacl.HMAC.compute_sha2_256 output key keylen data datalen;
  convert_subtype #unit #(rtype hash_return_type) ()

let hmac_sha2_512 output keylen key datalen data =
  (**) normalize_term_spec(Hash.max_input_length Hash.SHA2_512);
  (**) assert(length key <= Hash.max_input_length Hash.SHA2_512);
  (**) assert(Spec.Agile.HMAC.keysized Hash.SHA2_512 (length key));
  Hacl.HMAC.compute_sha2_512 output key keylen data datalen;
  convert_subtype #unit #(rtype hash_return_type) ()

(**** Blake2 *)

let hash_blake2 a m output inlen input =
  begin match with_norm(a), with_norm(m) with
  | Hash.Blake2S, ImplBlake2Core.M32 ->
    ImplBlake2s32.blake2s 32ul output inlen input 0ul (null #MUT #uint8)
  | Hash.Blake2S, ImplBlake2Core.M128 ->
    ImplBlake2s128.blake2s 32ul output inlen input 0ul (null #MUT #uint8)
  | Hash.Blake2B, ImplBlake2Core.M32 ->
    ImplBlake2b32.blake2b 64ul output inlen input 0ul (null #MUT #uint8)
  | Hash.Blake2B, ImplBlake2Core.M256 ->
    ImplBlake2b256.blake2b 64ul output inlen input 0ul (null #MUT #uint8)
  end;
  convert_subtype #unit #(rtype hash_return_type) ()

let hash2_blake2 a m =
  match with_norm(a), with_norm(m) with
  | Hash.Blake2S, ImplBlake2Core.M32 ->
    do_incr_hash2 Hacl.Streaming.Blake2.blake2s_32_no_key_alloca
                  Hacl.Streaming.Blake2.blake2s_32_no_key_update
                  Hacl.Streaming.Blake2.blake2s_32_no_key_finish
                  ()
  | Hash.Blake2S, ImplBlake2Core.M128 ->
    do_incr_hash2 Hacl.Streaming.Blake2s_128.blake2s_128_no_key_alloca
                  Hacl.Streaming.Blake2s_128.blake2s_128_no_key_update
                  Hacl.Streaming.Blake2s_128.blake2s_128_no_key_finish
                  ()
  | Hash.Blake2B, ImplBlake2Core.M32 ->
    do_incr_hash2 Hacl.Streaming.Blake2.blake2b_32_no_key_alloca
                  Hacl.Streaming.Blake2.blake2b_32_no_key_update
                  Hacl.Streaming.Blake2.blake2b_32_no_key_finish
                  ()
  | Hash.Blake2B, ImplBlake2Core.M256 ->
    do_incr_hash2 Hacl.Streaming.Blake2b_256.blake2b_256_no_key_alloca
                  Hacl.Streaming.Blake2b_256.blake2b_256_no_key_update
                  Hacl.Streaming.Blake2b_256.blake2b_256_no_key_finish
                  ()

let hmac_blake2 a m output keylen key datalen data =
  [@inline_let]
  let hmac : Hacl.HMAC.compute_st a =
    match a, m with
    | Hash.Blake2S, ImplBlake2Core.M32 ->
      Hacl.HMAC.compute_blake2s_32
    | Hash.Blake2B, ImplBlake2Core.M32 ->
      Hacl.HMAC.compute_blake2b_32
    | Hash.Blake2S, ImplBlake2Core.M128 ->
      Hacl.HMAC.Blake2s_128.compute_blake2s_128
    | Hash.Blake2B, ImplBlake2Core.M256 ->
      Hacl.HMAC.Blake2b_256.compute_blake2b_256
  in
  hmac output key keylen data datalen;
  convert_subtype #unit #(rtype hash_return_type) ()

(*** Tests *)
open Spec.Noise.Instances

let iwgc : iconfig = IConfig wgc True True True

let wgc_impl : config_impls iwgc =
  Config_impls
    (dh_sp_c25519 ImplCFields.M51)
    (dh_c25519 ImplCFields.M51)
    (aead_encrypt_cp ImplPolyFields.M32)
    (aead_decrypt_cp ImplPolyFields.M32)
    (hash_blake2 Hash.Blake2S ImplBlake2Core.M32)
    (hash2_blake2 Hash.Blake2S ImplBlake2Core.M32)
    (hmac_blake2 Hash.Blake2S ImplBlake2Core.M32)
