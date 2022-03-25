module Impl.Noise.CipherState

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
module BS = Lib.ByteSequence
module LB = Lib.Buffer
open Lib.Buffer
module BB = Lib.ByteBuffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Impl.Noise.Types
open Impl.Noise.HKDF

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Integers conversion *)
(* TODO: those are not used anymore *)
inline_for_extraction noextract
let uint64_from_bytes b : Tot uint64 =
  BS.uint_from_bytes_le b
let uint64_gfrom_buffer (h : HS.mem) (b : lbuffer uint8 (size 8)) : GTot uint64 =
  uint64_from_bytes (as_seq h b)

inline_for_extraction noextract
val uint64_from_buffer:
  i:lbuffer uint8 (size 8) ->
  Stack uint64
    (requires fun h0 -> live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ live h1 i /\
      o == uint64_gfrom_buffer h0 i)

inline_for_extraction noextract
let uint64_to_bytes i : Tot (lseq uint8 8) =
  BS.uint_to_bytes_le #U64 #SEC i

inline_for_extraction noextract
val uint64_to_buffer:
  o:lbuffer uint8 (size 8) ->
  i:uint64 ->
  Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      live h1 o /\ modifies (loc o) h0 h1 /\
      as_seq h1 o == uint64_to_bytes i)

let uint64_to_from_bytes_eq (i : uint64) :
  Lemma(uint64_from_bytes (uint64_to_bytes i) == i) =
  BS.lemma_uint_to_from_bytes_le_preserves_value #U64 #SEC i

let uint64_from_to_bytes_eq (s : lseq uint8 8) :
  Lemma(uint64_to_bytes (uint64_from_bytes s) `S.equal` s) =
  BS.lemma_uint_from_to_bytes_le_preserves_value #U64 #SEC s

val uint64_from_zeros_eq_lem :
  s : lseq uint8 8{forall (k : size_nat{k < 8}). S.index s k == u8 0} ->
  Lemma(uint64_from_bytes (s) == u64 0)

(*** Definition, getters, setters *)
/// We don't put the nonce inside the meta cipher state, because it will be handled
/// by the meta information ([meta_info]).
inline_for_extraction //noextract
type cipher_state_m =
  opt_aead_key_t

inline_for_extraction noextract
let csm_get_k (st : cipher_state_m) : opt_aead_key_t =
  st

/// Build a meta cipher state from all the necessary fields
inline_for_extraction noextract
let mk_csm (st_k : opt_aead_key_t) : cipher_state_m =
  st_k

let cs_unchanged (st : cipher_state_m) (h0 h1 : mem) : Type0 =
  unchanged_lbuffer_or_null (csm_get_k st) h0 h1

let eval_opt_aead_key (h : HS.mem) (k : opt_aead_key_t) :
  GTot (option (lseq uint8 aead_key_vsv)) =
  pn_as_seq h k
let eval_aead_key (h : HS.mem) (k : opt_aead_key_t{not (g_is_null k)}) : GTot aead_key =
  nn_as_seq h k

let eval_cipher_state_mf (h : HS.mem) (st_k : opt_aead_key_t)
                         (has_key : bool{has_key ==> (not (g_is_null st_k))})
                         (n : nat) :
  GTot (cipher_state) =
  let k_v = if has_key then Some (nn_as_seq h st_k) else None in
  { k = k_v; n = n; }

let eval_cipher_state_m (h : HS.mem) (st : cipher_state_m)
                        (has_key : bool{has_key ==> (not (g_is_null (csm_get_k st)))})
                        (n : nat) :
  GTot (cipher_state) =
  eval_cipher_state_mf h (csm_get_k st) has_key n

let live_csm (h : mem) (st : cipher_state_m) : Type0 =
  live h (csm_get_k st)

let disjoint_csm (st : cipher_state_m) : Type0 =
  True

/// Cipher state parameters invariant
let csm_inv (h : mem) (st : cipher_state_m) (has_key : bool) : Type0 =
  live_csm h st /\ disjoint_csm st /\ (if has_key then ~(g_is_null (csm_get_k st)) else True)

/// Same as [csm_inv], but the predicate takes a variable for every field of the
/// meta state.
let csf_inv (h : mem) (st_k : opt_aead_key_t) (has_key : bool) : Type0 =
  live h st_k /\ (if has_key then ~(g_is_null st_k) else True)

let csm_loc (st : cipher_state_m) : GTot B.loc =
  loc (csm_get_k st)

let csf_loc (st_k : opt_aead_key_t) : GTot B.loc =
  loc st_k

let csm_loc_disjoint (st : cipher_state_m) : B.loc -> GTot Type0 =
  B.loc_disjoint (csm_loc st)

let csm_disjoint (st : cipher_state_m)
                 (#t : buftype) (#a : Type0) (#len : size_t)
                 (b : lbuffer_t t a len) : GTot Type0 =
  B.loc_disjoint (csm_loc st) (loc b)

let csf_disjoint (st_k : opt_aead_key_t)
                 (#t : buftype) (#a : Type0) (#len : size_t)
                 (b : lbuffer_t t a len) : GTot Type0 =
  B.loc_disjoint (loc st_k) (loc b)

let csm_modifies1 (st : cipher_state_m)
                  (#a : Type0) (b : buffer_t MUT a) (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b) (csm_loc st)) h1 h2

(*** Transition functions *)

inline_for_extraction noextract
val initialize_key_Some :
  key : aead_key_t ->
  st_k : opt_aead_key_t ->
  ST unit
  (requires (fun h -> csf_inv h st_k true /\ live h key /\
                    disjoint st_k key))
  (ensures (fun h0 _ h1 ->
              modifies1 st_k h0 h1 /\
              eval_cipher_state_mf h1 st_k true 0 ==
                Spec.initialize_key (Some (eval_aead_key h1 key))))

val initialized_cipher_state_no_key_lem :
  h : HS.mem ->
  st_k : opt_aead_key_t ->
  Lemma
  (requires True)
  (ensures (eval_cipher_state_mf h st_k false 0 == Spec.initialize_key None))

inline_for_extraction noextract
type encrypt_with_ad_with_key_st (nc : iconfig) =
  (aad_len : size_t{size_v aad_len <= aead_max_input (get_config nc)}) ->
  (aad : lbuffer uint8 aad_len) ->
  (plen : size_t{size_v plen <= aead_max_input (get_config nc) /\
                 size_v plen + aead_tag_size <= max_size_t}) ->
  (p : lbuffer uint8 plen) ->
  (c : lbuffer uint8 (size (size_v plen + aead_tag_vsv))) ->
  (st_k : opt_aead_key_t) ->
  (nonce : aead_nonce_t) ->
  Stack (rtype encrypt_return_type)
  (requires (fun h -> csf_inv h st_k true /\ live h aad /\ live h p /\ live h c /\
                    disjoint st_k aad /\ disjoint st_k p /\
                    disjoint aad c /\ disjoint p c /\
                    disjoint st_k c /\ disjoint p aad /\
                    (* functional pre: *)
                    v nonce < saturated_nonce_value /\
                    get_aead_pre nc))
  (ensures (fun h0 r h1 ->
              modifies1 c h0 h1 /\
              is_success r /\ (* sanity check *)
              begin
              let aad_v = as_seq h0 aad in
              let p_v = as_seq h0 p in                
              let st_v = eval_cipher_state_mf h0 st_k true (v nonce) in
              match Spec.encrypt_with_ad (get_config nc) aad_v p_v st_v with
              | Fail _ -> False
              | Res (c_v, st1_v) ->
                length c = S.length c_v /\ S.equal h1.[|c|] c_v /\
                eval_cipher_state_mf h1 st_k true ((v nonce) + 1) == st1_v
              end))

inline_for_extraction noextract
val encrypt_with_ad_with_key_m (#nc : iconfig) (csi : config_impls nc) :
  encrypt_with_ad_with_key_st nc

inline_for_extraction noextract
type decrypt_with_ad_with_key_st (nc : iconfig) =
  (aad_len : size_t{size_v aad_len <= aead_max_input (get_config nc)}) ->
  (aad : lbuffer uint8 aad_len) ->
  (plen : size_t{size_v plen <= aead_max_input (get_config nc) /\
                 size_v plen + aead_tag_size <= max_size_t}) ->
  (p : lbuffer uint8 plen) ->
  (c : lbuffer uint8 (size (size_v plen + aead_tag_vsv))) ->
  (st_k : opt_aead_key_t) ->
  (nonce : aead_nonce_t) ->
  Stack (rtype decrypt_return_type)
  (requires (fun h -> csf_inv h st_k true /\ live h aad /\ live h p /\ live h c /\
                    disjoint st_k aad /\ disjoint st_k c /\
                    disjoint aad p /\ disjoint p c /\
                    disjoint st_k p /\ disjoint c aad /\
                    (* functional pre: *)
                    v nonce < saturated_nonce_value /\
                    get_aead_pre nc))
  (ensures (fun h0 r h1 ->
              modifies1 p h0 h1 /\
              begin
              let aad_v = h0.[|aad|] in
              let c_v = h0.[|c|] in
              let st_v = eval_cipher_state_mf h0 st_k true (v nonce) in
              let r_v = Spec.decrypt_with_ad (get_config nc) aad_v c_v st_v in
              match to_prim_error_code r, r_v with
              | CDecrypt_error, Fail e ->
                (e == Input_size \/ e == Decryption) /\
                eval_cipher_state_mf h1 st_k true (v nonce) == st_v
              | CSuccess, Res (p_v, st1_v) ->
                length p == S.length p_v /\ h1.[|p|] `S.equal` p_v /\
                eval_cipher_state_mf h1 st_k true ((v nonce) + 1) == st1_v
              | _ -> False
              end))

inline_for_extraction noextract
val decrypt_with_ad_with_key_m (#nc : iconfig) (csi : config_impls nc) :
  decrypt_with_ad_with_key_st nc

(*** Functions container *)
/// Tuple containing implementations for the cipher state functions
inline_for_extraction noextract
let cs_impls (nc : iconfig) =
  config_impls nc & kdf_st nc &
  encrypt_with_ad_with_key_st nc & decrypt_with_ad_with_key_st nc

inline_for_extraction noextract
let csi_get_prims (#nc : iconfig) (csi : cs_impls nc) :
  Tot (config_impls nc) =
  match csi with prims, kdf, enc, dec -> prims

inline_for_extraction noextract
let csi_get_kdf (#nc : iconfig) (csi : cs_impls nc) :
  Tot (kdf_st nc) =
  match csi with prims, kdf, enc, dec -> kdf

inline_for_extraction noextract
let csi_get_encrypt_with_ad_with_key (#nc : iconfig) (csi : cs_impls nc) :
  Tot (encrypt_with_ad_with_key_st nc) =
  match csi with prims, kdf, enc, dec -> enc

inline_for_extraction noextract
let csi_get_decrypt_with_ad_with_key (#nc : iconfig) (csi : cs_impls nc) :
  Tot (decrypt_with_ad_with_key_st nc) =
  match csi with prims, kdf, enc, dec -> dec
