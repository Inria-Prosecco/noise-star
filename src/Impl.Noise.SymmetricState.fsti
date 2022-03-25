module Impl.Noise.SymmetricState

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
module LB = Lib.Buffer
open Lib.Buffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Definition, getters, setters *)
inline_for_extraction noextract
type symmetric_state_m (nc : iconfig) =
  cipher_state_m & chaining_key_t nc & hash_t nc

inline_for_extraction noextract
let ssm_get_c_state (#nc : iconfig) (st : symmetric_state_m nc) : cipher_state_m =
  (* Doesn't normalize correctly at extraction if we write:
   * [> let (cs, ck, h) = st in h
   * See: https://github.com/FStarLang/FStar/issues/2038
   *)
  match st with cs, ck, h -> cs

inline_for_extraction noextract
let ssm_get_ck (#nc : iconfig) (st : symmetric_state_m nc) : chaining_key_t nc =
  match st with cs, ck, h -> ck

inline_for_extraction noextract
let ssm_get_h (#nc : iconfig) (st : symmetric_state_m nc) : hash_t nc =
  match st with cs, ck, h -> h

/// Build a meta symmetric state from all the necessary fields
inline_for_extraction noextract
let mk_ssm (#nc : iconfig)
           (st_cs_k : opt_aead_key_t)
           (st_ck : chaining_key_t nc)
           (st_h : hash_t nc) :
  symmetric_state_m nc =
  [@inline_let] let csm = mk_csm st_cs_k in
  csm, st_ck, st_h

let eval_key_chain (#nc : iconfig) (h : HS.mem) (k : chaining_key_t nc) :
  GTot (chaining_key (get_config nc)) =
  as_seq h k
let eval_hash (#nc : iconfig) (h : HS.mem) (b : hash_t nc) :
  GTot (hash (get_config nc)) =
  as_seq h b

let ss_unchanged (#nc : iconfig)
                 (st : symmetric_state_m nc)
                 (h0 h1 : mem) : Type0 =
  cs_unchanged (ssm_get_c_state st) h0 h1 /\
  h1.[|(ssm_get_ck st)|] `S.equal` h0.[|(ssm_get_ck st)|] /\
  h1.[|(ssm_get_h st)|] `S.equal` h0.[|(ssm_get_h st)|]

let eval_symmetric_state_m
  (#nc : iconfig) (h : HS.mem) (st : symmetric_state_m nc)
  (has_key : bool{has_key ==> (not (g_is_null (csm_get_k (ssm_get_c_state st))))})
  (nonce : nat) :
  GTot (st_v:symmetric_state (get_config nc){Some? st_v.c_state.k == has_key}) =
  let cst_v = eval_cipher_state_mf h (csm_get_k (ssm_get_c_state st)) has_key nonce in
  let ck_v = eval_key_chain h (ssm_get_ck st) in
  let h_v = eval_hash h (ssm_get_h st) in
  { c_state = cst_v; ck = ck_v; h = h_v; }

(* Predicates to reason about aliasing *)
let live_ssm_no_csm (#nc : iconfig) (h : mem) (st : symmetric_state_m nc) : Type0 =
  live h (ssm_get_ck st) /\ live h (ssm_get_h st)

let live_ssm (#nc : iconfig) (h : mem) (st : symmetric_state_m nc) : Type0 =
  live_csm h (ssm_get_c_state st) /\ live_ssm_no_csm h st

let disjoint_ssm_no_csm (#nc : iconfig) (st : symmetric_state_m nc) : Type0 =
  csm_disjoint (ssm_get_c_state st) (ssm_get_ck st) /\
  csm_disjoint (ssm_get_c_state st) (ssm_get_h st) /\
  disjoint (ssm_get_ck st) (ssm_get_h st)

let disjoint_ssm (#nc : iconfig) (st : symmetric_state_m nc) : Type0 =
  disjoint_csm (ssm_get_c_state st) /\ disjoint_ssm_no_csm st

/// Symmetric state invariant
let ssm_inv (#nc : iconfig) (h : mem) (st : symmetric_state_m nc) (has_sk : bool) : Type0 =
  csm_inv h (ssm_get_c_state st) has_sk /\ live_ssm_no_csm h st /\ disjoint_ssm_no_csm st

(** The union of all locations in the symmetric state *)
let ssm_loc (#nc : iconfig) (st : symmetric_state_m nc) : GTot B.loc =
  B.loc_union (loc (ssm_get_ck st))
    (B.loc_union (loc (ssm_get_h st)) (csm_loc (ssm_get_c_state st)))

let ssm_loc_disjoint (#nc : iconfig) (st : symmetric_state_m nc) : B.loc -> GTot Type0 =
  B.loc_disjoint (ssm_loc st)

let ssm_disjoint (#nc : iconfig)
                 (st : symmetric_state_m nc)
                 (#t : buftype) (#a : Type0) (#len : size_t)
                 (b : lbuffer_t t a len) : GTot Type0 =
  B.loc_disjoint (ssm_loc st) (loc b)

(** Modify clauses *)
let ssm_modifies0 (#nc : iconfig) (st : symmetric_state_m nc) (h1 h2 : HS.mem) =
  modifies (ssm_loc st) h1 h2

let ssm_modifies1 (#nc : iconfig) (st : symmetric_state_m nc)
                  (#a : Type0) (b : buffer_t MUT a) (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b) (ssm_loc st)) h1 h2

let ssm_modifies2 (#nc : iconfig) (st : symmetric_state_m nc)
                  (#a0 #a1 : Type0) (b0 : buffer_t MUT a0) (b1 : buffer_t MUT a1)
                  (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b0) (B.loc_union (loc b1) (ssm_loc st))) h1 h2

let ssm_modifies3 (#nc : iconfig) (st : symmetric_state_m nc)
                  (#a0 #a1 #a2 : Type0)
                  (b0 : buffer_t MUT a0) (b1 : buffer_t MUT a1) (b2 : buffer_t MUT a2)
                  (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b0) (B.loc_union (loc b1)
                        (B.loc_union (loc b2) (ssm_loc st)))) h1 h2

(*** State transition functions *)
(**** Initialize symmetric *)
let initialize_symmetric_pre
    (#nc : iconfig)
    (protocol_name_len : hashable_size_t nc)
    (protocol_name : hashable_t nc protocol_name_len)
    (st : symmetric_state_m nc)
    (h : mem) : Type0 =
  ssm_inv h st false /\ live h protocol_name /\
  ssm_disjoint st protocol_name /\
  (* If the protocol name is smaller than the hash size, we pad it
   * with zeros to initialiaze the hash. In the implementation,
   * we just copy to an initially zeroed hash. *)
  begin
  if size_v protocol_name_len <= hash_vsv nc then
    S.equal (as_seq h (ssm_get_h st)) (S.create (hash_vsv nc) (u8 0))
  (* Otherwise we use the hash function *)
  else
    get_hash_pre nc
  end

let initialize_symmetric_post
    (#nc : iconfig)
    (protocol_name_len : hashable_size_t nc)
    (protocol_name : hashable_t nc protocol_name_len)
    (st : symmetric_state_m nc)
    (h0 : mem) (r : rtype hash_return_type) (h1 : mem) : Type0 =
  ssm_modifies0 st h0 h1 /\
  is_success r /\ (* sanity check *)
  begin
  let r_v = Spec.initialize_symmetric h0.[|protocol_name|] in
  eval_symmetric_state_m h1 st false 0 == r_v
  end
    

/// fst : fields stateful (because stateful, and takes one parameter per field of the
/// structure, rather than the structure itself
inline_for_extraction noextract
type initialize_symmetric_fst (nc : iconfig) =
  protocol_name_len : hashable_size_t nc ->
  protocol_name : hashable_t nc protocol_name_len ->
  st_cs_k : opt_aead_key_t ->
  st_ck : chaining_key_t nc ->
  st_h : hash_t nc ->
  Stack (rtype hash_return_type)
  (requires (fun h -> let st = mk_ssm st_cs_k st_ck st_h in
                    initialize_symmetric_pre #nc protocol_name_len protocol_name st h))
  (requires (fun h0 r h1 -> let st = mk_ssm st_cs_k st_ck st_h in
                          initialize_symmetric_post #nc protocol_name_len protocol_name
                                                    st h0 r h1))

inline_for_extraction noextract
type initialize_symmetric_st (nc : iconfig) =
  protocol_name_len : hashable_size_t nc ->
  protocol_name : hashable_t nc protocol_name_len ->
  st : symmetric_state_m nc ->
  Stack (rtype hash_return_type)
  (requires (fun h -> initialize_symmetric_pre #nc protocol_name_len protocol_name st h))
  (requires (fun h0 r h1 -> initialize_symmetric_post #nc protocol_name_len protocol_name
                                                   st h0 r h1))

inline_for_extraction noextract
val initialize_symmetric_fm (#nc : iconfig) (nci : config_impls nc) :
  initialize_symmetric_fst nc

(**** Mix key *)
let mix_key_pre
    (#nc : iconfig)
    (has_sk : Ghost.erased bool)
    (key : public_key_t nc)
    (st : symmetric_state_m nc)
    (nonce : Ghost.erased nat)
    (h : mem) : Type0 =
  ssm_inv h st true /\ live h key /\
  ssm_disjoint st (key <: lbuffer uint8 (size (length key))) /\
  get_hash_pre nc

let mix_key_post
    (#nc : iconfig)
    (has_sk : Ghost.erased bool)
    (key : public_key_t nc)
    (st : symmetric_state_m nc{not(g_is_null (csm_get_k (ssm_get_c_state st)))})
    (nonce : Ghost.erased nat)
    (h0 : mem) (r : rtype hash_return_type) (h1 : mem) : Type0 =
  ssm_modifies0 st h0 h1 /\
  is_success r /\ (* sanity check *)
  eval_symmetric_state_m h1 st (**) true (**) 0 ==
    Spec.mix_key h0.[|key <: lbuffer uint8 (size (length key))|]
                 (eval_symmetric_state_m h0 st has_sk nonce)

inline_for_extraction noextract
type mix_key_fst (nc : iconfig) =
  has_sk : Ghost.erased bool ->
  key : public_key_t nc ->
  st_cs_k : opt_aead_key_t ->
  st_ck : chaining_key_t nc ->
  st_h : hash_t nc ->
  nonce : Ghost.erased nat ->
  Stack (rtype hash_return_type)
  (requires (fun h -> let st = mk_ssm st_cs_k st_ck st_h in
                    mix_key_pre #nc has_sk key st nonce h))
  (ensures (fun h0 r h1 -> let st = mk_ssm st_cs_k st_ck st_h in
                         mix_key_post #nc has_sk key st nonce h0 r h1))

inline_for_extraction noextract
type mix_key_st (nc : iconfig) =
  has_sk : Ghost.erased bool ->
  key : public_key_t nc ->
  st : symmetric_state_m nc ->
  nonce : Ghost.erased nat ->
  Stack (rtype hash_return_type)
  (requires (fun h -> mix_key_pre #nc has_sk key st nonce h))
  (ensures (fun h0 r h1 -> mix_key_post #nc has_sk key st nonce h0 r h1))

inline_for_extraction noextract
val mix_key_fm (#nc : iconfig) (csi : cs_impls nc) :
  mix_key_fst nc

(**** Mix hash *)

let mix_hash_pre
    (#nc : iconfig)
    (has_sk : Ghost.erased bool)
    (input_len : hashable_size_t nc)
    (input : hashable_t nc input_len)
    (st : symmetric_state_m nc)
    (nonce : Ghost.erased nat)
    (h : mem) : Type0 =
  ssm_inv h st false /\ live h input /\ ssm_disjoint st input /\
  (g_is_null (csm_get_k (ssm_get_c_state st)) ==> Ghost.reveal has_sk == false) /\
  get_hash_pre nc

let mix_hash_post
    (#nc : iconfig)
    (has_sk : Ghost.erased bool)
    (input_len : hashable_size_t nc)
    (input : hashable_t nc input_len)
    (st : symmetric_state_m nc{Ghost.reveal has_sk ==>
                               not (g_is_null (csm_get_k (ssm_get_c_state st)))})
    (nonce : Ghost.erased nat)
    (h0 : mem) (r : rtype hash_return_type) (h1 : mem) : Type0 =
  ssm_modifies0 st h0 h1 /\
  is_success r /\ (* sanity check *)
  eval_symmetric_state_m h1 st has_sk nonce ==
    Spec.mix_hash h0.[|input|] (eval_symmetric_state_m h0 st has_sk nonce)

inline_for_extraction noextract
type mix_hash_fst (nc : iconfig) =
  has_sk : Ghost.erased bool ->
  input_len : hashable_size_t nc ->
  input : hashable_t nc input_len ->
  st_cs_k : Ghost.erased opt_aead_key_t ->
  st_ck : Ghost.erased (chaining_key_t nc) ->
  st_h : hash_t nc ->
  nonce : Ghost.erased nat ->
  Stack (rtype hash_return_type)
  (requires (fun h -> let st = mk_ssm st_cs_k st_ck st_h in
                    mix_hash_pre #nc has_sk input_len input st nonce h))
  (requires (fun h0 r h1 -> let st = mk_ssm st_cs_k st_ck st_h in
                          mix_hash_post #nc has_sk input_len input st nonce h0 r h1))

inline_for_extraction noextract
type mix_hash_st (nc : iconfig) =
  has_sk : Ghost.erased bool ->
  input_len : hashable_size_t nc ->
  input : hashable_t nc input_len ->
  st : symmetric_state_m nc ->
  nonce : Ghost.erased nat ->
  Stack (rtype hash_return_type)
  (requires (fun h -> mix_hash_pre #nc has_sk input_len input st nonce h))
  (requires (fun h0 r h1 -> mix_hash_post #nc has_sk input_len input st nonce h0 r h1))

inline_for_extraction noextract
val mix_hash_fm (#nc : iconfig) (csi : cs_impls nc) :
  mix_hash_fst nc

(**** Mix key and hash *)
let mix_key_and_hash_pre
    (#nc : iconfig)
    (has_sk : Ghost.erased bool)
    (psk : preshared_key_t)
    (st : symmetric_state_m nc)
    (nonce : Ghost.erased nat)
    (h : mem) =
  ssm_inv h st true /\ live h psk /\
  ssm_disjoint st psk /\
  get_hash_pre nc

let mix_key_and_hash_post
    (#nc : iconfig)
    (has_sk : Ghost.erased bool)
    (psk : preshared_key_t)
    (st : symmetric_state_m nc{not (g_is_null (csm_get_k (ssm_get_c_state st)))})
    (nonce : Ghost.erased nat)
    (h0 : mem) (r : rtype hash_return_type) (h1 : mem) =
  ssm_modifies0 st h0 h1 /\
  is_success r /\ (* sanity check *)
  eval_symmetric_state_m h1 st (**) true (**) 0 ==
    Spec.mix_key_and_hash h0.[|psk|] (eval_symmetric_state_m h0 st has_sk nonce)

inline_for_extraction noextract
type mix_key_and_hash_fst (nc : iconfig) =
  has_sk : Ghost.erased bool ->
  psk : preshared_key_t ->
  st_cs_k : opt_aead_key_t ->
  st_ck : chaining_key_t nc ->
  st_h : hash_t nc ->
  nonce : Ghost.erased nat ->
  Stack (rtype hash_return_type)
  (requires (fun h -> let st = mk_ssm st_cs_k st_ck st_h in
                    mix_key_and_hash_pre #nc has_sk psk st nonce h))
  (ensures (fun h0 r h1 -> let st = mk_ssm st_cs_k st_ck st_h in
                         mix_key_and_hash_post #nc has_sk psk st nonce h0 r h1))

inline_for_extraction noextract
type mix_key_and_hash_st (nc : iconfig) =
  has_sk : Ghost.erased bool ->
  psk : preshared_key_t ->
  st : symmetric_state_m nc ->
  nonce : Ghost.erased nat ->
  Stack (rtype hash_return_type)
  (requires (fun h -> mix_key_and_hash_pre #nc has_sk psk st nonce h))
  (ensures (fun h0 r h1 -> mix_key_and_hash_post #nc has_sk psk st nonce h0 r h1))

inline_for_extraction noextract
val mix_key_and_hash_fm (#nc : iconfig) (csi : cs_impls nc)
                        (mix_hash_impl : mix_hash_fst nc) :
  mix_key_and_hash_fst nc

(**** Encrypt and hash *)
let encrypt_and_hash_pre
    (#nc : iconfig)
    (has_sk : bool)
    (msg_len : plain_message_len_t nc)
    (msg : plain_message_t nc msg_len)
    (cipher : lbuffer uint8 (size (opt_encrypt_size has_sk (size_v msg_len))))
    (st : symmetric_state_m nc)
    (nonce : aead_nonce_t)
    (h : mem) : Type0 =
  ssm_inv h st has_sk /\
  live h msg /\ live h cipher /\
  ssm_disjoint st msg /\ ssm_disjoint st cipher /\
  disjoint msg cipher /\
  (has_sk ==> (v nonce < saturated_nonce_value /\ get_aead_pre nc)) /\
  get_hash_pre nc

let encrypt_and_hash_post
    (#nc : iconfig)
    (has_sk : bool)
    (msg_len : plain_message_len_t nc)
    (msg : plain_message_t nc msg_len)
    (cipher : lbuffer uint8 (size (opt_encrypt_size has_sk (size_v msg_len))))
    (st : symmetric_state_m nc{has_sk ==> not (g_is_null (csm_get_k (ssm_get_c_state st)))})
    (nonce : aead_nonce_t)
    (h0 : mem) (r : rtype encrypt_hash_return_type) (h1 : mem) :
    Type0 =
  ssm_modifies1 st cipher h0 h1 /\
  is_success r /\ (* sanity check *)
  begin
  let st0_v = eval_symmetric_state_m h0 st has_sk (v nonce) in
  let nonce1 = if has_sk then v nonce + 1 else v nonce in
  match Spec.encrypt_and_hash h0.[|msg|] st0_v with
  | Fail _ -> False
  | Res (cipher_v, st1_v) ->
    length cipher = S.length cipher_v /\ h1.[|cipher|] `S.equal` cipher_v /\
    st1_v == eval_symmetric_state_m h1 st has_sk nonce1
  end

inline_for_extraction noextract
type encrypt_and_hash_special_fst (nc : iconfig) (has_sk : bool) =
  msg_len : plain_message_len_t nc ->
  msg : plain_message_t nc msg_len ->
  cipher : lbuffer uint8 (size (opt_encrypt_size has_sk (size_v msg_len))) ->
  st_cs_k : opt_aead_key_t ->
  st_ck : Ghost.erased (chaining_key_t nc) ->
  st_h : hash_t nc ->
  nonce : aead_nonce_t ->
  Stack (rtype encrypt_hash_return_type)
  (requires (fun h -> let st = mk_ssm st_cs_k st_ck st_h in
                    encrypt_and_hash_pre #nc has_sk msg_len msg cipher st nonce h))
  (ensures (fun h0 r h1 -> let st = mk_ssm st_cs_k st_ck st_h in
                         encrypt_and_hash_post #nc has_sk msg_len msg cipher st nonce h0 r h1))

inline_for_extraction noextract
type encrypt_and_hash_fst (nc : iconfig) =
  has_sk : bool ->
  encrypt_and_hash_special_fst nc has_sk

inline_for_extraction noextract
type encrypt_and_hash_special_st (nc : iconfig) (has_sk : bool) =
  msg_len : plain_message_len_t nc ->
  msg : plain_message_t nc msg_len ->
  cipher : lbuffer uint8 (size (opt_encrypt_size has_sk (size_v msg_len))) ->
  st : symmetric_state_m nc ->
  nonce : aead_nonce_t ->
  Stack (rtype encrypt_hash_return_type)
  (requires (fun h -> encrypt_and_hash_pre #nc has_sk msg_len msg cipher st nonce h))
  (ensures (fun h0 r h1 -> encrypt_and_hash_post #nc has_sk msg_len msg cipher st nonce h0 r h1))

inline_for_extraction noextract
type encrypt_and_hash_st (nc : iconfig) =
  has_sk : bool ->
  encrypt_and_hash_special_st nc has_sk

inline_for_extraction noextract
let encrypt_and_hash_no_key_fst nc = encrypt_and_hash_special_fst nc false

inline_for_extraction noextract
val encrypt_and_hash_no_key_fm (#nc : iconfig) (mix_hash_impl : mix_hash_fst nc) :
  encrypt_and_hash_no_key_fst nc

inline_for_extraction noextract
let encrypt_and_hash_with_key_fst nc = encrypt_and_hash_special_fst nc true

inline_for_extraction noextract
val encrypt_and_hash_with_key_fm (#nc : iconfig) (csi : cs_impls nc)
                                 (mix_hash_impl : mix_hash_fst nc) :
  encrypt_and_hash_with_key_fst nc

inline_for_extraction noextract
val encrypt_and_hash_fm
  (#nc : iconfig)
  (encrypt_and_hash_no_key_impl : encrypt_and_hash_special_fst nc false)
  (encrypt_and_hash_with_key_impl : encrypt_and_hash_special_fst nc true) :
  encrypt_and_hash_fst nc

(**** Decrypt and hash *)
let decrypt_and_hash_pre
    (#nc : iconfig)
    (has_sk : bool)
    (msg_len : plain_message_len_t nc)
    (msg : plain_message_t nc msg_len)
    (cipher : lbuffer uint8 (size (opt_encrypt_size has_sk (size_v msg_len))))
    (st : symmetric_state_m nc)
    (nonce : aead_nonce_t)
    (h : mem) : Type0 =
  ssm_inv h st has_sk /\
  live h msg /\ live h cipher /\
  ssm_disjoint st msg /\ ssm_disjoint st cipher /\
  disjoint msg cipher /\
  (has_sk ==> (v nonce < saturated_nonce_value /\ get_aead_pre nc)) /\
  get_hash_pre nc

let decrypt_and_hash_post
    (#nc : iconfig)
    (has_sk : bool)
    (msg_len : plain_message_len_t nc)
    (msg : plain_message_t nc msg_len)
    (cipher : lbuffer uint8 (size (opt_encrypt_size has_sk (size_v msg_len))))
    (st : symmetric_state_m nc{has_sk ==> not (g_is_null (csm_get_k (ssm_get_c_state st)))})
    (nonce : aead_nonce_t)
    (h0 : mem) (r : rtype (decrypt_hash_return_type has_sk)) (h1 : mem) : Type0 =
  ssm_modifies1 st msg h0 h1 /\
  begin
  let st0_v = eval_symmetric_state_m h0 st has_sk (v nonce) in
  let nonce1 = if has_sk then v nonce + 1 else v nonce in
  match to_prim_error_code r, Spec.decrypt_and_hash h0.[|cipher|] st0_v with
  | CDecrypt_error, Fail Decryption ->
    has_sk == true /\ (* sanity check *)
    eval_symmetric_state_m h1 st has_sk (v nonce) == st0_v
  | CSuccess, Res (msg_v, st1_v) ->
    S.length h1.[|msg|] == S.length msg_v /\
    h1.[|msg|] `S.equal` msg_v /\
    st1_v == eval_symmetric_state_m h1 st has_sk nonce1
  | _ -> False
  end

inline_for_extraction noextract
type decrypt_and_hash_special_fst (nc : iconfig) (has_sk : bool) =
  msg_len : plain_message_len_t nc ->
  msg : plain_message_t nc msg_len ->
  cipher : lbuffer uint8 (size (opt_encrypt_size has_sk (size_v msg_len))) ->
  st_cs_k : opt_aead_key_t ->
  st_ck : Ghost.erased (chaining_key_t nc) ->
  st_h : hash_t nc ->
  nonce : aead_nonce_t ->
  Stack (rtype (decrypt_hash_return_type has_sk))
  (requires (fun h -> let st = mk_ssm st_cs_k st_ck st_h in
                    decrypt_and_hash_pre #nc has_sk msg_len msg cipher st nonce h))
  (ensures (fun h0 r h1 -> let st = mk_ssm st_cs_k st_ck st_h in
                         decrypt_and_hash_post #nc has_sk msg_len msg cipher st nonce h0 r h1))

inline_for_extraction noextract
type decrypt_and_hash_fst (nc : iconfig) =
  has_sk : bool ->
  decrypt_and_hash_special_fst nc has_sk

inline_for_extraction noextract
type decrypt_and_hash_special_st (nc : iconfig) (has_sk : bool) =
  msg_len : plain_message_len_t nc ->
  msg : plain_message_t nc msg_len ->
  cipher : lbuffer uint8 (size (opt_encrypt_size has_sk (size_v msg_len))) ->
  st : symmetric_state_m nc ->
  nonce : aead_nonce_t ->
  Stack (rtype (decrypt_hash_return_type has_sk))
  (requires (fun h -> decrypt_and_hash_pre #nc has_sk msg_len msg cipher st nonce h))
  (ensures (fun h0 r h1 -> decrypt_and_hash_post #nc has_sk msg_len msg cipher st nonce h0 r h1))

inline_for_extraction noextract
type decrypt_and_hash_st (nc : iconfig) =
  has_sk : bool ->
  decrypt_and_hash_special_st nc has_sk

inline_for_extraction noextract
let decrypt_and_hash_no_key_fst nc = decrypt_and_hash_special_fst nc false

inline_for_extraction noextract
val decrypt_and_hash_no_key_fm (#nc : iconfig) (mix_hash_impl : mix_hash_fst nc) :
  decrypt_and_hash_no_key_fst nc

inline_for_extraction noextract
let decrypt_and_hash_with_key_fst nc = decrypt_and_hash_special_fst nc true

inline_for_extraction noextract
val decrypt_and_hash_with_key_fm (#nc : iconfig) (csi : cs_impls nc)
                                 (mix_hash_impl : mix_hash_fst nc) :
  decrypt_and_hash_with_key_fst nc

inline_for_extraction noextract
val decrypt_and_hash_fm
  (#nc : iconfig)
  (decrypt_and_hash_no_key_impl : decrypt_and_hash_special_fst nc false)
  (decrypt_and_hash_with_key_impl : decrypt_and_hash_special_fst nc true) :
  decrypt_and_hash_fst nc

(**** Split *)
let split_pre
    (#nc : iconfig)
    (st : symmetric_state_m nc)
    (cst1 : cipher_state_m)
    (cst2 : cipher_state_m)
    (h : mem) : Type0 =
  ssm_inv h st true /\ csm_inv h cst1 true /\ csm_inv h cst2 true /\
  B.loc_disjoint (ssm_loc st) (csm_loc cst1) /\
  B.loc_disjoint (ssm_loc st) (csm_loc cst2) /\
  B.loc_disjoint (csm_loc cst1) (csm_loc cst2) /\
  get_hash_pre nc

let split_post
    (#nc : iconfig)
    (st : symmetric_state_m nc{not (g_is_null (csm_get_k (ssm_get_c_state st)))})
    (cst1 : cipher_state_m{not (g_is_null (csm_get_k cst1))})
    (cst2 : cipher_state_m{not (g_is_null (csm_get_k cst2))})
    (h0 : mem) (r : rtype hash_return_type) (h1 : mem) : Type0 =
  modifies2 (csm_get_k cst1) (csm_get_k cst2) h0 h1 /\
  is_success r /\ (* sanity check *)
  begin
  forall (b: bool) (n : nat).
//  forall (b: bool) (n : aead_nonce).
  let st_v = eval_symmetric_state_m h0 st b n in
  let cst1_v, cst2_v = Spec.split st_v in
  eval_cipher_state_m h1 cst1 true 0 == cst1_v /\
  eval_cipher_state_m h1 cst2 true 0 == cst2_v
  end

inline_for_extraction noextract
type split_fst (nc : iconfig) =
  st_cs_k : Ghost.erased opt_aead_key_t ->
  st_ck : chaining_key_t nc ->
  st_h : Ghost.erased (hash_t nc) ->
  k1 : aead_key_t ->
  k2 : aead_key_t ->
  Stack (rtype hash_return_type)
  (requires (fun h -> let st = mk_ssm st_cs_k st_ck st_h in
                    let cst1 = mk_csm k1 in
                    let cst2 = mk_csm k2 in
                    split_pre #nc st cst1 cst2 h))
  (ensures (fun h0 r h1 -> let st = mk_ssm st_cs_k st_ck st_h in
                         let cst1 = mk_csm k1 in
                         let cst2 = mk_csm k2 in
                         split_post #nc st cst1 cst2 h0 r h1))

inline_for_extraction noextract
type split_st (nc : iconfig) =
  st : symmetric_state_m nc ->
  cst1 : cipher_state_m ->
  cst2 : cipher_state_m ->
  Stack (rtype hash_return_type)
  (requires (fun h -> split_pre #nc st cst1 cst2 h))
  (ensures (fun h0 r h1 -> split_post #nc st cst1 cst2 h0 r h1))

inline_for_extraction noextract
val split_fm (#nc : iconfig) (kdf_impl : kdf_st nc) :
  split_fst nc

(*** Helpers *)
/// We mostly manipulate functions which have in their signature one variable
/// per structure field. However, as it is not convenient to manipulate, we provide
/// some helpers which take a structure as parameter.
/// Note that we can't only use functions which take structures as parameters because
/// otherwise those structures would appear in the generated C code, while those
/// should only be meta.
inline_for_extraction noextract
let initialize_symmetric_m (#nc : iconfig) (impl : initialize_symmetric_fst nc) :
  initialize_symmetric_st nc =
  fun protocol_name_len protocol_name st ->
    impl protocol_name_len protocol_name (csm_get_k (ssm_get_c_state st))
         (ssm_get_ck st) (ssm_get_h st)

inline_for_extraction noextract
let mix_key_m (#nc : iconfig) (impl : mix_key_fst nc) : mix_key_st nc =
  fun has_sk key st nonce ->
    impl has_sk key (csm_get_k (ssm_get_c_state st)) (ssm_get_ck st) (ssm_get_h st) nonce

inline_for_extraction noextract
let mix_hash_m (#nc : iconfig) (impl : mix_hash_fst nc) : mix_hash_st nc =
  fun has_sk input_len input st nonce ->
    impl has_sk input_len input (csm_get_k (ssm_get_c_state st))
         (ssm_get_ck st) (ssm_get_h st) nonce

inline_for_extraction noextract
let mix_key_and_hash_m (#nc : iconfig) (impl : mix_key_and_hash_fst nc) :
  mix_key_and_hash_st nc =
  fun has_sk psk st nonce ->
    impl has_sk psk (csm_get_k (ssm_get_c_state st)) (ssm_get_ck st)
         (ssm_get_h st) nonce

inline_for_extraction noextract
let encrypt_and_hash_m (#nc : iconfig) (impl : encrypt_and_hash_fst nc) :
  encrypt_and_hash_st nc =
  fun has_sk msg_len msg cipher st nonce ->
    impl has_sk msg_len msg cipher (csm_get_k (ssm_get_c_state st)) (ssm_get_ck st)
         (ssm_get_h st) nonce

inline_for_extraction noextract
let decrypt_and_hash_m (#nc : iconfig) (impl : decrypt_and_hash_fst nc) :
  decrypt_and_hash_st nc =
  fun has_sk msg_len msg cipher st nonce ->
    impl has_sk msg_len msg cipher (csm_get_k (ssm_get_c_state st)) (ssm_get_ck st)
         (ssm_get_h st) nonce

inline_for_extraction noextract
let split_m (#nc : iconfig) (impl : split_fst nc) : split_st nc =
  fun st cst1 cst2 ->
    impl (csm_get_k (ssm_get_c_state st)) (ssm_get_ck st) (ssm_get_h st)
         (csm_get_k cst1) (csm_get_k cst2)

(*** Functions container *)

inline_for_extraction noextract
let ss_impls (nc : iconfig) =
  cs_impls nc & initialize_symmetric_st nc &
  mix_key_st nc & mix_hash_st nc & mix_key_and_hash_st nc &
  encrypt_and_hash_st nc & decrypt_and_hash_st nc & split_st nc

inline_for_extraction noextract
let ssi_get_csi (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (cs_impls nc) =
  (*
   * Doesn't normalize if we do the following:
   * [> let (csi, init, mk, mh, mkh, enc, dec, s) = ssi in csi
   *)
  match ssi with | csi, init, mk, mh, mkh, enc, dec, s -> csi

inline_for_extraction noextract
let ssi_get_prims (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (config_impls nc) =
  csi_get_prims (ssi_get_csi ssi)

inline_for_extraction noextract
let ssi_get_kdf (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (kdf_st nc) =
  csi_get_kdf (ssi_get_csi ssi)

inline_for_extraction noextract
let ssi_get_initialize_symmetric (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (initialize_symmetric_st nc) =
  match ssi with csi, init, mk, mh, mkh, enc, dec, s -> init

inline_for_extraction noextract
let ssi_get_mix_key (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (mix_key_st nc) =
  match ssi with csi, init, mk, mh, mkh, enc, dec, s -> mk

inline_for_extraction noextract
let ssi_get_mix_hash (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (mix_hash_st nc) =
  match ssi with csi, init, mk, mh, mkh, enc, dec, s -> mh

inline_for_extraction noextract
let ssi_get_mix_key_and_hash (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (mix_key_and_hash_st nc) =
  match ssi with csi, init, mk, mh, mkh, enc, dec, s -> mkh

inline_for_extraction noextract
let ssi_get_encrypt_and_hash (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (encrypt_and_hash_st nc) =
  match ssi with csi, init, mk, mh, mkh, enc, dec, s -> enc

inline_for_extraction noextract
let ssi_get_decrypt_and_hash (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (decrypt_and_hash_st nc) =
  match ssi with csi, init, mk, mh, mkh, enc, dec, s -> dec

inline_for_extraction noextract
let ssi_get_split (#nc : iconfig) (ssi : ss_impls nc) :
  Tot (split_st nc) =
  match ssi with csi, init, mk, mh, mkh, enc, dec, s -> s
