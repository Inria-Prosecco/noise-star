module Impl.Noise.HandshakeState

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence
open Lib.ByteSequence

module B = LowStar.Buffer
open Lib.Buffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.TypeOrUnit

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

(* Align the .fst and the .fsti *)
private val _align_beg : unit

(*** Definition, getters, setters *)
/// TODO: LowStar.Monotonic.Buffer.all_disjoint / all_live
inline_for_extraction noextract
type handshake_state_m (nc : iconfig) =
  symmetric_state_m nc & keypair_m nc & keypair_m nc &
  opt_public_key_t nc & opt_public_key_t nc & opt_preshared_key_t

inline_for_extraction noextract
let mk_hsm
  (#nc : iconfig) 
  (ss : symmetric_state_m nc)
  (static : keypair_m nc)
  (ephemeral : keypair_m nc)
  (remote_static : opt_public_key_t nc)
  (remote_ephemeral : opt_public_key_t nc)
  (psk : opt_preshared_key_t) : handshake_state_m nc =
  ss, static, ephemeral, remote_static, remote_ephemeral, psk

inline_for_extraction noextract
let hsm_get_sym_state (#nc : iconfig) (st : handshake_state_m nc) :
  symmetric_state_m nc =
  (* Doesn't normalize correctly at extraction if we write:
   * [> let (ss, static, ephemeral, rstatic, rephemeral, psk) = st in ss
   * See: https://github.com/FStarLang/FStar/issues/2038
   *)
  match st with ss, static, ephemeral, rstatic, rephemeral, psk -> ss

inline_for_extraction noextract
let hsm_get_static (#nc : iconfig) (st : handshake_state_m nc) :
  keypair_m nc =
  match st with ss, static, ephemeral, rstatic, rephemeral, psk -> static

inline_for_extraction noextract
let hsm_get_ephemeral (#nc : iconfig) (st : handshake_state_m nc) :
  keypair_m nc =
  match st with ss, static, ephemeral, rstatic, rephemeral, psk -> ephemeral

inline_for_extraction noextract
let hsm_get_remote_static (#nc : iconfig) (st : handshake_state_m nc) :
  opt_public_key_t nc =
  match st with ss, static, ephemeral, rstatic, rephemeral, psk -> rstatic

inline_for_extraction noextract
let hsm_get_remote_ephemeral (#nc : iconfig) (st : handshake_state_m nc) :
  opt_public_key_t nc =
  match st with ss, static, ephemeral, rstatic, rephemeral, psk -> rephemeral

inline_for_extraction noextract
let hsm_get_preshared (#nc : iconfig) (st : handshake_state_m nc) :
  opt_preshared_key_t =
  match st with ss, static, ephemeral, rstatic, rephemeral, psk -> psk

let hs_unchanged (#nc : iconfig)
                 (st : handshake_state_m nc)
                 (h0 h1 : mem) : Type0 =
  ss_unchanged (hsm_get_sym_state st) h0 h1 /\
  unchanged_keypair_m (hsm_get_static st) h0 h1 /\
  unchanged_keypair_m (hsm_get_ephemeral st) h0 h1 /\
  unchanged_lbuffer_or_null (hsm_get_remote_static st) h0 h1 /\
  unchanged_lbuffer_or_null (hsm_get_remote_ephemeral st) h0 h1 /\
  unchanged_lbuffer_or_null (hsm_get_preshared st) h0 h1


(** Predicate which, given a [meta_info], states which fields of a
  * [handshake_state_m] must be non-null *)
let hs_nn_pred (#nc : iconfig)  (smi : meta_info) (st : handshake_state_m nc) : GTot bool =
  let hsf = smi.hsf in
  buffer_nn_pred hsf.sk (csm_get_k (ssm_get_c_state (hsm_get_sym_state st))) &&
  keypair_nn_pred hsf.s (hsm_get_static st) &&
  keypair_nn_pred hsf.e (hsm_get_ephemeral st) &&
  buffer_nn_pred hsf.rs (hsm_get_remote_static st) &&
  buffer_nn_pred hsf.re (hsm_get_remote_ephemeral st) &&
  buffer_nn_pred hsf.psk (hsm_get_preshared st)

let eval_handshake_state_m
  (#nc : iconfig) (h : mem) (st : handshake_state_m nc)
  (smi : meta_info{hs_nn_pred smi st}) :
  GTot (st_v:handshake_state (get_config nc){
    Some? st_v.sym_state.c_state.k == smi.hsf.sk /\
    Some? st_v.static == smi.hsf.s /\
    Some? st_v.ephemeral == smi.hsf.e /\
    Some? st_v.remote_static == smi.hsf.rs /\
    Some? st_v.remote_ephemeral == smi.hsf.re /\
    Some? st_v.preshared == smi.hsf.psk}) =
  let sym_state_v =
    eval_symmetric_state_m h (hsm_get_sym_state st) smi.hsf.sk smi.nonce in
  let static_v =
    if smi.hsf.s then Some (eval_keypair_m h (hsm_get_static st)) else None in
  let ephemeral_v =
    if smi.hsf.e then Some (eval_keypair_m h (hsm_get_ephemeral st)) else None in
  let remote_static_v =
    if smi.hsf.rs then Some (eval_public_key h (hsm_get_remote_static st))
                  else None in
  let remote_ephemeral_v =
    if smi.hsf.re then Some (eval_public_key h (hsm_get_remote_ephemeral st))
                  else None in
  let preshared_v =
    if smi.hsf.psk then Some (eval_preshared_key h (hsm_get_preshared st)) else None in
  {
    sym_state = sym_state_v;
    static = static_v;
    ephemeral = ephemeral_v;
    remote_static = remote_static_v;
    remote_ephemeral = remote_ephemeral_v;
    preshared = preshared_v;
  }

(** Predicates to reason about aliasing *)
let live_hsm_no_ssm (#nc : iconfig) (h : mem) (st : handshake_state_m nc) : Type0 =
  live_kpm h (hsm_get_static st) /\ live_kpm h (hsm_get_ephemeral st) /\
  live h (hsm_get_remote_static st) /\ live h (hsm_get_remote_ephemeral st) /\
  live h (hsm_get_preshared st)

let live_hsm (#nc : iconfig) (h : mem) (st : handshake_state_m nc) : Type0 =
  live_ssm h (hsm_get_sym_state st) /\ live_hsm_no_ssm h st

(** Disjointness predicate: between symmetric state and keys *)
let hsm_disjoint_keys_and_ssm (#nc : iconfig) (st : handshake_state_m nc) : Type0 =
  ssm_loc_disjoint (hsm_get_sym_state st) (keypair_loc (hsm_get_static st)) /\
  ssm_loc_disjoint (hsm_get_sym_state st) (keypair_loc (hsm_get_ephemeral st)) /\
  ssm_loc_disjoint (hsm_get_sym_state st) (loc (hsm_get_remote_static st)) /\
  ssm_loc_disjoint (hsm_get_sym_state st) (loc (hsm_get_remote_ephemeral st)) /\
  ssm_loc_disjoint (hsm_get_sym_state st) (loc (hsm_get_preshared st))

(** Disjointness predicate: between remote keys, and between remote and local keys *)
let hsm_disjoint_remote_and_local_keys (#nc : iconfig) (st : handshake_state_m nc) : Type0 =
  kpm_loc_disjoint (hsm_get_static st) (loc (hsm_get_remote_static st)) /\
  kpm_loc_disjoint (hsm_get_static st) (loc (hsm_get_remote_ephemeral st)) /\
  kpm_loc_disjoint (hsm_get_static st) (loc (hsm_get_preshared st)) /\
  kpm_loc_disjoint (hsm_get_ephemeral st) (loc (hsm_get_remote_static st)) /\
  kpm_loc_disjoint (hsm_get_ephemeral st) (loc (hsm_get_remote_ephemeral st)) /\
  kpm_loc_disjoint (hsm_get_ephemeral st) (loc (hsm_get_preshared st)) /\
  B.loc_disjoint (loc (hsm_get_remote_static st)) (loc (hsm_get_remote_ephemeral st)) /\
  B.loc_disjoint (loc (hsm_get_remote_static st)) (loc (hsm_get_preshared st)) /\
  B.loc_disjoint (loc (hsm_get_remote_ephemeral st)) (loc (hsm_get_preshared st))

(** Disjointness predicate: between local keys *)
let hsm_disjoint_local_keys (#nc : iconfig) (st : handshake_state_m nc) : Type0 =
  disjoint_kpm (hsm_get_static st) /\ disjoint_kpm (hsm_get_ephemeral st) /\
  B.loc_disjoint (keypair_loc (hsm_get_static st)) (keypair_loc (hsm_get_ephemeral st))

(** Disjointness predicate: between all the fields, but no internal disjointess
  * of symmetric state *)
let disjoint_hsm_no_ssm (#nc : iconfig) (st : handshake_state_m nc) : Type0 =
  hsm_disjoint_keys_and_ssm st /\
  hsm_disjoint_remote_and_local_keys st /\
  hsm_disjoint_local_keys st

(** Disjointness predicate : between all the fields *)
let disjoint_hsm (#nc : iconfig) (st : handshake_state_m nc) : Type0 =
  disjoint_ssm (hsm_get_sym_state st) /\ disjoint_hsm_no_ssm st

(** Valid [handshake_state_m] *)
let hsm_inv (#nc : iconfig) (h : mem) (st : handshake_state_m nc) (smi : meta_info) :
  (t:Type0{t ==> hs_nn_pred smi st}) =
  hs_nn_pred smi st /\ ssm_inv h (hsm_get_sym_state st) smi.hsf.sk /\
  live_hsm_no_ssm h st /\ disjoint_hsm_no_ssm st

let smaller_hsm_impl_hs_nn_pred
  (#nc : iconfig)
  (smi0 smi1 : meta_info)
  (st : handshake_state_m nc) :
  Lemma
  (requires (less_than smi0 smi1 /\ hs_nn_pred smi1 st))
  (ensures hs_nn_pred smi0 st) = ()

(** The union of all locations in the handshake state *)
let hsm_loc (#nc : iconfig) (st : handshake_state_m nc) : GTot B.loc =
  B.loc_union (ssm_loc (hsm_get_sym_state st))
    (B.loc_union (keypair_loc (hsm_get_static st))
      (B.loc_union (keypair_loc (hsm_get_ephemeral st))
        (B.loc_union (loc (hsm_get_remote_static st))
          (B.loc_union (loc (hsm_get_remote_ephemeral st)) (loc (hsm_get_preshared st))))))

let hsm_loc_only_remote (#nc : iconfig) (st : handshake_state_m nc) : GTot B.loc =
  B.loc_union (ssm_loc (hsm_get_sym_state st))
    (B.loc_union (loc (hsm_get_remote_static st))
      (loc (hsm_get_remote_ephemeral st)))

let hsm_loc_disjoint (#nc : iconfig) (st : handshake_state_m nc) : B.loc -> GTot Type0 =
  B.loc_disjoint (hsm_loc st)

let hsm_disjoint (#nc : iconfig)
                 (st : handshake_state_m nc)
                 (#t : buftype) (#a : Type0) (#len : size_t)
                 (b : lbuffer_t t a len) : GTot Type0 =
  B.loc_disjoint (hsm_loc st) (loc b)

(** Modify clauses *)
let hsm_modifies0 (#nc : iconfig) (st : handshake_state_m nc) (h1 h2 : HS.mem) =
  modifies (hsm_loc st) h1 h2

let hsm_modifies1 (#nc : iconfig)
                  (st : handshake_state_m nc)
                  (#a : Type0) (b : buffer_t MUT a) (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b) (hsm_loc st)) h1 h2

let hsm_modifies2 (#nc : iconfig)
                  (st : handshake_state_m nc)
                  (#a0 #a1 : Type0) (b0 : buffer_t MUT a0) (b1 : buffer_t MUT a1)
                  (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b0) (B.loc_union (loc b1) (hsm_loc st))) h1 h2

let hsm_modifies3 (#nc : iconfig)
                  (st : handshake_state_m nc)
                  (#a0 #a1 #a2 : Type0)
                  (b0 : buffer_t MUT a0) (b1 : buffer_t MUT a1) (b2 : buffer_t MUT a2)
                  (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b0) (B.loc_union (loc b1) (B.loc_union (loc b2) (hsm_loc st)))) h1 h2

let hsm_modifies0_only_remote (#nc : iconfig) (st : handshake_state_m nc) (h1 h2 : HS.mem) =
  modifies (hsm_loc_only_remote st) h1 h2

let hsm_modifies1_only_remote (#nc : iconfig)
                  (st : handshake_state_m nc)
                  (#a : Type0) (b : buffer_t MUT a) (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b) (hsm_loc_only_remote st)) h1 h2

let hsm_modifies2_only_remote (#nc : iconfig)
                  (st : handshake_state_m nc)
                  (#a0 #a1 : Type0) (b0 : buffer_t MUT a0) (b1 : buffer_t MUT a1)
                  (h1 h2 : HS.mem) =
  modifies (B.loc_union (loc b0) (B.loc_union (loc b1) (hsm_loc_only_remote st))) h1 h2


(** Valid hsm - we need to have the refinement with [hs_nn_pred] because even though
  * it is already in [hsm_inv], F* doesn't manage to use it to typecheck
  * the occurences of [handshake_state_m] given to [eval_handshake_state_m]. *)
let is_valid_hsm (#nc : iconfig) (smi : meta_info) (st : handshake_state_m nc) :
  GTot bool =
  hs_nn_pred smi st

type valid_hsm (nc : iconfig) (smi : meta_info) =
  st:handshake_state_m nc{is_valid_hsm smi st}

(** The below [handshake_state_m] refinement types give conditions on the
  * availability of the key pointers with regard to the send/receive operations
  * that will follow. For example, if we update the remote static key (the
  * corresponding flag should initially be false, because there should be
  * no key so far) its pointer should be non-null before we actually perform
  * the operation. This basically means that in order to compute the conditions
  * about the available pointers we need to use the post [meta_info],
  * computed to relate the concrete state at the end (and not the beginning)
  * of the execution with the one from the spec.
  * *)
(* TODO: change the position of token/pattern and smi parameters *)
type valid_receive_pretoken_hsm nc token smi =
  valid_hsm nc (receive_pretoken_update_smi token smi)

type valid_receive_premessage_hsm nc msg smi =
  valid_hsm nc (receive_premessage_update_smi msg smi)

type valid_send_token_hsm nc is_psk token smi =
  valid_hsm nc (send_token_update_smi is_psk token smi)

type valid_send_message_hsm nc is_psk pattern smi =
  valid_hsm nc (send_message_update_smi is_psk pattern smi)

type valid_receive_token_hsm nc is_psk token smi =
  valid_hsm nc (receive_token_update_smi is_psk token smi)

type valid_receive_message_hsm nc is_psk pattern smi =
  valid_hsm nc (receive_message_update_smi is_psk pattern smi)


(*** Initialization *)

let initialize_handshake_state_pre
    (#nc : iconfig)
    (pname_len : hashable_size_t nc)
    (protocol_name : hashable_t nc pname_len)
    (prlg_len : hashable_size_t nc)
    (prologue : hashable_t nc prlg_len)
    (#s_b: bool)
    (spriv : private_key_t_or_unit nc s_b)
    (spub : public_key_t_or_unit nc s_b)
    (#e_b: bool)
    (epriv : private_key_t_or_unit nc e_b)
    (epub : public_key_t_or_unit nc e_b)
    (#rs_b: bool) (rs : public_key_t_or_unit nc rs_b)
    (#re_b: bool) (re : public_key_t_or_unit nc re_b)
    (#psk_b: bool) (psk : preshared_key_t_or_unit psk_b)
    (st : handshake_state_m nc)
    (h : mem) : Type0 =
  let sk_b = false in
  let hsf = { sk = sk_b; s = s_b; e = e_b; rs = rs_b; re = re_b; psk = psk_b; } in
  let smi = { hsf = hsf; nonce = 0; } in
  hsm_inv h st smi /\
  live h protocol_name /\ live h prologue /\
  lbuffer_or_unit_live h spriv /\ lbuffer_or_unit_live h spub /\
  lbuffer_or_unit_live h epriv /\ lbuffer_or_unit_live h epub /\
  lbuffer_or_unit_live h rs /\ lbuffer_or_unit_live h re /\
  lbuffer_or_unit_live h psk /\
  ssm_disjoint (hsm_get_sym_state st) protocol_name /\
  ssm_disjoint (hsm_get_sym_state st) prologue /\
  hsm_loc_disjoint st (B.loc_union (lbuffer_or_unit_loc spriv) (lbuffer_or_unit_loc spub)) /\
  hsm_loc_disjoint st (B.loc_union (lbuffer_or_unit_loc epriv) (lbuffer_or_unit_loc epub)) /\
  hsm_loc_disjoint st (lbuffer_or_unit_loc rs) /\ hsm_loc_disjoint st (lbuffer_or_unit_loc re) /\
  hsm_loc_disjoint st (lbuffer_or_unit_loc psk) /\
  S.equal (as_seq h (ssm_get_h (hsm_get_sym_state st))) (S.create (hash_vsv nc) (u8 0)) /\
  get_hash_pre nc

let initialize_handshake_state_post
    (#nc : iconfig)
    (pname_len : hashable_size_t nc)
    (protocol_name : hashable_t nc pname_len)
    (prlg_len : hashable_size_t nc)
    (prologue : hashable_t nc prlg_len)
    (#s_b: bool)
    (spriv : private_key_t_or_unit nc s_b)
    (spub : public_key_t_or_unit nc s_b)
    (#e_b: bool)
    (epriv : private_key_t_or_unit nc e_b)
    (epub : public_key_t_or_unit nc e_b)
    (#rs_b: bool) (rs : public_key_t_or_unit nc rs_b)
    (#re_b: bool) (re : public_key_t_or_unit nc re_b)
    (#psk_b: bool) (psk : preshared_key_t_or_unit psk_b)
    (st : handshake_state_m nc)
    (h0 : mem) (r : rtype hash_return_type) (h1 : mem) :
  Pure Type0
  (* Some predicates have preconditions which are given by the pre *)
  (requires (initialize_handshake_state_pre pname_len protocol_name prlg_len prologue
                                            spriv spub epriv epub rs re psk st h0))
  (ensures (fun _ -> True))
  =
  let mod_loc = ssm_loc (hsm_get_sym_state st) in
  let sloc = if not s_b then B.loc_none else keypair_loc (hsm_get_static st) in
  let eloc = if not e_b then B.loc_none else keypair_loc (hsm_get_ephemeral st) in
  let rs_loc = if not rs_b then B.loc_none else loc (hsm_get_remote_static st) in
  let re_loc = if not re_b then B.loc_none else loc (hsm_get_remote_ephemeral st) in
  let psk_loc = if not psk_b then B.loc_none else loc (hsm_get_preshared st) in
  let mod_loc =
    B.loc_union mod_loc
      (B.loc_union sloc
        (B.loc_union eloc
          (B.loc_union rs_loc
            (B.loc_union re_loc psk_loc))))
  in
  B.modifies mod_loc h0 h1 /\
  is_success r /\ (* sanity check *)
  begin
  let pname_v = h0.[|protocol_name|] in
  let prologue_v = h0.[|prologue|] in
  let sk_b = false in
  let s_v = keys_t_or_unit_to_keypair h0 spriv spub in
  let e_v = keys_t_or_unit_to_keypair h0 epriv epub in
  let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
  let re_v = lbuffer_or_unit_to_opt_lseq h0 re in
  let psk_v = lbuffer_or_unit_to_opt_lseq h0 psk in
  let hsf = { sk = sk_b; s = s_b; e = e_b; rs = rs_b; re = re_b; psk = psk_b; } in
  let smi = { hsf = hsf; nonce = 0; } in
  let st1_v = eval_handshake_state_m h1 st smi in
  st1_v == Spec.initialize_handshake_state pname_v prologue_v
                                           s_v e_v rs_v re_v psk_v
  end

inline_for_extraction noextract
type initialize_handshake_state_st (nc : iconfig) =
  pname_len : hashable_size_t nc ->
  protocol_name : hashable_t nc pname_len ->
  prlg_len : hashable_size_t nc ->
  prologue : hashable_t nc prlg_len ->
  #s_b: bool ->
  spriv : private_key_t_or_unit nc s_b ->
  spub : public_key_t_or_unit nc s_b ->
  #e_b: bool ->
  epriv : private_key_t_or_unit nc e_b ->
  epub : public_key_t_or_unit nc e_b ->
  #rs_b: bool -> rs : public_key_t_or_unit nc rs_b ->
  #re_b: bool -> re : public_key_t_or_unit nc re_b ->
  #psk_b: bool -> psk : preshared_key_t_or_unit psk_b ->
  st : handshake_state_m nc ->
  Stack (rtype hash_return_type)
  (requires (fun h ->
     initialize_handshake_state_pre pname_len protocol_name prlg_len prologue
                                    spriv spub epriv epub rs re psk st h))
  (ensures (fun h0 r h1 ->
     initialize_handshake_state_post pname_len protocol_name prlg_len prologue
                                     spriv spub epriv epub rs re psk st h0 r h1))

inline_for_extraction noextract
val initialize_handshake_state_m (#nc : iconfig) (ssi : ss_impls nc) :
  initialize_handshake_state_st nc

(*** Premessages *)
inline_for_extraction noextract
let premessage_vsv (nc : iconfig) (pattern : list premessage_token) : nat =
  List.length pattern * (public_key_vsv nc)

noextract
let premessage_size_pred (nc : iconfig) (pattern : list premessage_token) : Type0 =
  premessage_vsv nc pattern <= max_size_t

inline_for_extraction noextract
let premessage_vs (nc : iconfig)
                  (pattern : list premessage_token{premessage_size_pred nc pattern}) :
    size_t =
  size (premessage_vsv nc pattern)  

inline_for_extraction noextract
type premessage_t (nc : iconfig)
                  (pattern : list premessage_token{premessage_size_pred nc pattern}) =
  lbuffer uint8 (premessage_vs nc pattern)

inline_for_extraction noextract
let token_premessage_return_type : return_type = unit_return_type

inline_for_extraction noextract
let tokens_premessage_return_type : return_type = unit_return_type

(**** Send premessage(s) *)
let send_premessage_token_post
    (#nc : iconfig)
    (smi : meta_info)
    (tk : premessage_token)
    (st : valid_hsm nc smi)
    (out : public_key_t nc)
    (h0 : mem) (r : rtype token_premessage_return_type) (h1 : mem) : Type0 =
  ssm_modifies1 (hsm_get_sym_state st) out h0 h1 /\
  begin
  let st0_v = eval_handshake_state_m h0 st smi in
  let st1_v = eval_handshake_state_m h1 st smi in
  let r1_v = Spec.send_premessage_token tk st0_v in
  match to_prim_error_code r, r1_v with
  | CSuccess, Res (msg_v, st1'_v) ->
    S.length msg_v = length out /\
    msg_v `S.equal` h1.[|out|] /\ st1_v == st1'_v
  | _ -> False
  end

inline_for_extraction noextract
type send_premessage_token_st (nc : iconfig) =
  smi : Ghost.erased meta_info ->
  tk : premessage_token ->
  st : valid_hsm nc smi ->
  out : public_key_t nc ->
  Stack (rtype token_premessage_return_type)
  (requires (fun h -> hsm_inv h st smi /\ live h out /\ hsm_disjoint st out /\
                    has_pretoken smi tk /\
                    (if tk = PS then get_hash_pre nc else True)))
  (ensures (send_premessage_token_post smi tk st out))

inline_for_extraction noextract
val send_premessage_token_m (#nc : iconfig) (ssi : ss_impls nc) :
  send_premessage_token_st nc

inline_for_extraction noextract
type send_premessage_tokens_st (nc : iconfig) =
  smi : Ghost.erased meta_info ->
  pattern : list premessage_token{premessage_size_pred nc pattern} ->
  st : valid_hsm nc smi ->
  out : premessage_t nc pattern ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h -> hsm_inv h st smi /\ live h out /\ hsm_disjoint st out /\
                    has_pretokens smi pattern /\
                    (if List.mem PS pattern then get_hash_pre nc else True)))
  (ensures (
     fun h0 r h1 ->
     ssm_modifies1 (hsm_get_sym_state st) out h0 h1 /\
     begin
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi in
     let r1_v = Spec.send_premessage_tokens pattern st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Res (msg_v, st1'_v) ->
       S.length msg_v == length out /\ msg_v `S.equal` h1.[|out|] /\ st1_v == st1'_v
     | _ -> False
     end))

(**** Receive premessage(s) *)
let receive_premessage_token_post
    (#nc : iconfig)
    (smi0 : meta_info)
    (tk : premessage_token)
    (st : valid_receive_pretoken_hsm nc tk smi0)
    (input : public_key_t nc)
    (h0 : mem) (r : rtype token_premessage_return_type) (h1 : mem) :
    Type0 =
  hsm_modifies0 st h0 h1 /\
  begin
  let smi1 = receive_pretoken_update_smi tk smi0 in
  let st0_v = eval_handshake_state_m h0 st smi0 in
  let st1_v = eval_handshake_state_m h1 st smi1 in
  let input_v = h0.[|input|] in
  let r1_v = Spec.receive_premessage_token tk input_v st0_v in
  match to_prim_error_code r, r1_v with
  | CSuccess, Res st1'_v -> st1_v == st1'_v
  | _ -> False
  end

inline_for_extraction noextract
type receive_premessage_token_st (nc : iconfig) =
  smi : Ghost.erased meta_info ->
  tk : premessage_token ->
  st : valid_receive_pretoken_hsm nc tk smi ->
  input : public_key_t nc ->
  Stack (rtype token_premessage_return_type)
  (requires (fun h -> hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
                    no_remote_pretoken smi tk /\
                    (if tk = PS then get_hash_pre nc else True)))
  (ensures (receive_premessage_token_post smi tk st input))

inline_for_extraction noextract
val receive_premessage_token_m (#nc : iconfig) (ssi : ss_impls nc) :
  receive_premessage_token_st nc

inline_for_extraction noextract
type receive_premessage_tokens_st (nc : iconfig) =
  smi : Ghost.erased meta_info ->
  pattern : list premessage_token{premessage_size_pred nc pattern} ->
  st : valid_receive_premessage_hsm nc pattern smi ->
  input : premessage_t nc pattern ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h -> hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
                    no_remote_pretokens smi pattern /\
                    (if List.mem PS pattern then get_hash_pre nc else True)))
  (ensures (fun h0 r h1 -> hsm_modifies0 st h0 h1 /\
              (let st0_v = eval_handshake_state_m h0 st smi in
               let smi' = receive_premessage_update_smi pattern smi in
               let st1_v = eval_handshake_state_m h1 st smi' in
               let input_v = h0.[|input|] in
               let r1_v = Spec.receive_premessage_tokens pattern input_v st0_v in
               match to_prim_error_code r, r1_v with
               | CSuccess, Res st1'_v -> st1_v == st1'_v
               | _ -> False)))

(*** DH *)

(**** DH: symmetric state *)
/// In order to be able not to declare [inline_for_extraction] the implementation
/// of dh_update, we define a specification (with an implementation) which takes
/// as parameters structure fields rather than the structures themselves. The
/// implementation has a signature adequate for extraction.
/// From this implementation, we can define a version which operates on handshake
/// states and is easier to manipulate, but will be inlined at extraction.

let dh_update_sym_state
  (#nc : config)
  (msg : bytes)
  (opt_priv : option (keypair nc))
  (opt_pub : option (public_key nc))
  (st : symmetric_state nc) :
  Tot (eresult (bytes & (symmetric_state nc))) =
  match opt_priv, opt_pub with
  | Some priv, Some pub ->
    (match dh priv.priv pub with
     | Some k -> Res (msg, Spec.mix_key k st)
     | None -> Fail DH)
  | _ -> Fail No_key

let dh_update_sym_state_pre
    (#nc : iconfig)
    (msg : Ghost.erased bytes)
    (has_sk : Ghost.erased bool)
    (priv_sec : private_key_t nc)
    (priv_pub : Ghost.erased (public_key_t nc))
    (pub : public_key_t nc)
    (st : symmetric_state_m nc)
    (nonce : Ghost.erased nat)
    (h : mem) : Type0 =
  let priv : keypair_m nc = mk_keypair_m priv_sec priv_pub in
  ssm_inv h st (**) true (**) /\ kpm_is_valid h priv true /\ live h pub /\
  ssm_loc_disjoint st (keypair_loc priv) /\
  ssm_disjoint st pub /\
  get_dh_pre nc /\ get_hash_pre nc

let dh_update_sym_state_post
    (#nc : iconfig)
    (msg : Ghost.erased bytes)
    (has_sk : Ghost.erased bool)
    (priv_sec : private_key_t nc)
    (priv_pub : Ghost.erased (public_key_t nc))
    (pub : public_key_t nc)
    (st : symmetric_state_m nc{~(g_is_null (csm_get_k (ssm_get_c_state st)))})
    (nonce : Ghost.erased nat)
    (h0 : mem) (r : rtype dh_hash_return_type) (h1 : mem) : Type0 =
  let priv : keypair_m nc = mk_keypair_m priv_sec priv_pub in
  ssm_modifies0 st h0 h1 /\
  begin
  let st0_v = eval_symmetric_state_m h0 st has_sk nonce in
  let st1_v = eval_symmetric_state_m h1 st (**) true 0 (**) in
  let r_v = dh_update_sym_state msg (Some (eval_keypair_m h0 priv))
                               (Some (eval_public_key h0 pub)) st0_v in
  match to_prim_error_code r, r_v with
  | CSuccess, Res (_, st1'_v) -> st1_v == st1'_v
  | CDH_error, Fail DH -> eval_symmetric_state_m h1 st has_sk nonce == st0_v
  | _ -> False
  end

inline_for_extraction noextract
type dh_update_sym_state_fst (nc : iconfig) =
  msg : Ghost.erased bytes ->
  has_sk : Ghost.erased bool ->
  priv_sec : private_key_t nc ->
  priv_pub : Ghost.erased (public_key_t nc) ->
  pub : public_key_t nc ->
  st_cs_k : opt_aead_key_t ->
  st_ck : chaining_key_t nc ->
  st_h : hash_t nc ->
  nonce : Ghost.erased nat ->
  Stack (rtype dh_hash_return_type)
  (requires (fun h ->
     let st = mk_ssm st_cs_k st_ck st_h in
     dh_update_sym_state_pre msg has_sk priv_sec priv_pub pub st nonce h))
  (ensures (fun h0 r h1 ->
     let st = mk_ssm st_cs_k st_ck st_h in
     dh_update_sym_state_post msg has_sk priv_sec priv_pub pub st nonce h0 r h1))

(**** DH: handshake state *)

let dh_update_pre
    (#nc : iconfig)
    (msg : Ghost.erased bytes)
    (smi : Ghost.erased meta_info)
    (priv : keypair_m nc)
    (pub : public_key_t nc)
    (st : valid_hsm nc (smi_set_sk true smi))
    (h : mem) : Type0 =
  hsm_inv h st smi /\ kpm_is_valid h priv true /\ live h pub /\
  ssm_loc_disjoint (hsm_get_sym_state st) (keypair_loc priv) /\
  ssm_disjoint (hsm_get_sym_state st) pub /\
  get_dh_pre nc /\ get_hash_pre nc

let dh_update_post
    (#nc : iconfig)
    (msg : Ghost.erased bytes)
    (smi : Ghost.erased meta_info)
    (priv : keypair_m nc{~(g_is_null (kpm_get_priv priv)) /\ ~(g_is_null (kpm_get_pub priv))})
    (pub : public_key_t nc)
    (st : valid_hsm nc (smi_set_sk true smi))
    (h0 : mem) (r : rtype dh_hash_return_type) (h1 : mem) : Type0 =
  ssm_modifies0 (hsm_get_sym_state st) h0 h1 /\
  begin
  let st0_v = eval_handshake_state_m h0 st smi in
  let smi1 = {smi_set_sk true smi with nonce = 0} in
  let st1_v = eval_handshake_state_m h1 st (**) smi1 (**) in
  let r_v = Spec.dh_update msg (Some (eval_keypair_m h0 priv))
                               (Some (eval_public_key h0 pub)) st0_v in
  match to_prim_error_code r, r_v with
  | CSuccess, Res (_, st1'_v) -> st1_v == st1'_v
  | CDH_error, Fail DH -> eval_handshake_state_m h1 st smi == st0_v
  | _ -> False
  end

inline_for_extraction noextract
type dh_update_st (nc : iconfig) =
  msg : Ghost.erased bytes ->
  smi : Ghost.erased meta_info ->
  priv : keypair_m nc ->
  pub : public_key_t nc ->
  st : valid_hsm nc (smi_set_sk true smi) ->
  Stack (rtype dh_hash_return_type)
  (requires (fun h -> dh_update_pre msg smi priv pub st h))
  (ensures (fun h0 r h1 -> dh_update_post msg smi priv pub st h0 r h1))

inline_for_extraction noextract
val dh_update_sym_state_fm (#nc : iconfig) (ssi : ss_impls nc) :
  dh_update_sym_state_fst nc

inline_for_extraction noextract
val dh_update_m (#nc : iconfig) (dh_update_impl : dh_update_sym_state_fst nc) :
  dh_update_st nc

inline_for_extraction noextract
let ssdh_impls (nc : iconfig) =
  ss_impls nc & dh_update_st nc

inline_for_extraction noextract
let ssdhi_get_ssi (#nc : iconfig) (ssdhi : ssdh_impls nc) :
  Tot (ss_impls nc) =
  match ssdhi with ssi, dh -> ssi

inline_for_extraction noextract
let ssdhi_get_dh_update (#nc : iconfig) (ssdhi : ssdh_impls nc) :
  Tot (dh_update_st nc) =
  match ssdhi with ssi, dh -> dh
