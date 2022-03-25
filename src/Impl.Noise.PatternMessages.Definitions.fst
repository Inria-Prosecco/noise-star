module Impl.Noise.PatternMessages.Definitions

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence
module SB = FStar.Seq.Base
module L = FStar.List
module Seq = FStar.Seq

module B = LowStar.Buffer
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
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.SendReceive
open Impl.Noise.RecursivePremessages
open Impl.Noise.RecursiveMessages
open Impl.Noise.FlatStructures
open Impl.Noise.CryptoPrimitives

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(*** Generic function types *)
(**** Initialization *)
(* Condition on the psk flag for the premessages *)
noextract
let psk_flag_premessage_cond (hsk : handshake_pattern) (psk : bool) : bool =
  (* [psk ==> hsk is psk] *)
  if psk then chskf_check_is_psk hsk else true

noextract
let initialize_funct_pre (#nc : iconfig)
                         (hsk : handshake_pattern) (initiator : bool)
                         (spriv epriv : opt_private_key_t nc)
                         (psk : opt_preshared_key_t) =
  let pskb = not (g_is_null psk) in
  let smi = if pskb then normalize_term(initialize_post_smi hsk initiator true)
            else normalize_term(initialize_post_smi hsk initiator false) in
  (* We initialize the static and ephemeral keys if and only if they are used
   * in the pattern *)
  (smi.hsf.s <==> ~(g_is_null spriv)) /\ (smi.hsf.e <==> ~(g_is_null epriv)) /\
  (* We may initialize the psk, but only if this is a PSK handshake *)
  (~(g_is_null psk) ==> smi.hsf.psk)

(* This lemma helps prove the [initialize_funct_pre] component in the
 * [initialize] precondition (see above). *)
let prove_initialize_funct_pre_lem
  (#nc : iconfig) (hsk : handshake_pattern) (initiator : bool)
  (spriv epriv : opt_private_key_t nc) (psk : opt_preshared_key_t) :
  Lemma(
    (norm [delta_only[`%initialize_funct_pre]]
         (initialize_funct_pre hsk initiator spriv epriv psk)) ==>
    initialize_funct_pre hsk initiator spriv epriv psk)
  =
  norm_spec [delta_only[`%initialize_funct_pre]]
         (initialize_funct_pre hsk initiator spriv epriv psk)

let initialize_gen_pre
    (#nc : iconfig)
    (hsk : Ghost.erased handshake_pattern)
    (initiator : Ghost.erased bool)
    (spriv : opt_private_key_t nc)
    (spub : opt_public_key_t nc)
    (epriv : opt_private_key_t nc)
    (epub : opt_public_key_t nc)
    (psk : opt_preshared_key_t)
    (st : handshake_state_t nc)
    (h : mem) : Type0 =
  live h spriv /\ live h spub /\ live h epriv /\ live h epub /\
  live h psk /\ live h st /\
  disjoint st spriv /\ disjoint st spub /\
  disjoint st epriv /\ disjoint st epub /\
  disjoint st psk /\
  h.[|st|] `S.equal` (S.create (handshake_state_vsv nc) (u8 0)) /\
  initialize_funct_pre hsk initiator spriv epriv psk /\
  (* TODO: can't prove [initialize_handshake_state] precondition
     if those two hypotheses are written as refinements for the types
     of spriv and spub below *)
  (g_is_null spriv <==> g_is_null spub) /\
  (g_is_null epriv <==> g_is_null epub) /\
  (**)
  get_hash_pre nc

let initialize_gen_post
    (#nc : iconfig)
    (hsk : Ghost.erased handshake_pattern)
    (initiator : Ghost.erased bool)
    (pname_v : hashable (get_config nc))
    (prologue_v : hashable (get_config nc))
    (spriv : opt_private_key_t nc)
    (spub : opt_public_key_t nc)
    (epriv : opt_private_key_t nc)
    (epub : opt_public_key_t nc)
    (psk : opt_preshared_key_t)
    (st : handshake_state_t nc)
    (h0 : mem) (r : rtype hash_return_type) (h1 : mem) : Type0 =
  modifies1 st h0 h1 /\
  is_success r /\ (* sanity check *)
  begin
  let smi = initialize_post_smi hsk initiator (not (g_is_null psk)) in
  let s_v = eval_opt_split_keypair h0 spriv spub in
  let e_v = eval_opt_split_keypair h0 epriv epub in
  let psk_v = eval_opt_preshared_key h0 psk in
  let st1_v = eval_handshake_state h1 st smi in
  st1_v == Spec.initialize pname_v prologue_v s_v e_v psk_v
  end

inline_for_extraction noextract
type initialize_st (nc : iconfig) =
  hsk : Ghost.erased handshake_pattern ->
  initiator : Ghost.erased bool ->
  pname_len : hashable_size_t nc ->
  protocol_name : hashable_t nc pname_len ->
  prlg_len : hashable_size_t nc ->
  prologue : hashable_t nc prlg_len ->
  spriv : opt_private_key_t nc ->
  spub : opt_public_key_t nc ->
  epriv : opt_private_key_t nc ->
  epub : opt_public_key_t nc ->
  psk : opt_preshared_key_t ->
  st : handshake_state_t nc ->
  Stack (rtype hash_return_type)
  (requires (fun h ->
     live h protocol_name /\ live h prologue /\
     disjoint st protocol_name /\ disjoint st prologue /\
     initialize_gen_pre hsk initiator spriv spub epriv epub psk st h))
  (ensures (fun h0 r h1 ->
     initialize_gen_post hsk initiator h0.[|protocol_name|] h0.[|prologue|]
                         spriv spub epriv epub psk st h0 r h1))

#push-options "--z3rlimit 100 --ifuel 1"
inline_for_extraction noextract
let initialize_m
    (#nc : iconfig)
    (initialize_handshake_state_impl : initialize_handshake_state_st nc) :
    initialize_st nc =
  fun hsk initiator pname_len protocol_name prlg_len prologue spriv spub
    epriv epub psk st ->
  (**) let h0 = HST.get () in
  assert(
    let s_b = not (g_is_null spriv) in
    let e_b = not (g_is_null epriv) in
    let psk_b = not (g_is_null psk) in
    let smi = initialize_post_smi hsk initiator psk_b in
    smi.hsf.sk == false /\ smi.hsf.rs == false /\ smi.hsf.re == false /\ smi.hsf.psk == psk_b /\
    smi.hsf.s == s_b /\ smi.hsf.e == e_b
  );
  (* We need to use a small trick to ensure the tuples will be inlined by Kremlin *)
  (* TODO: find a way not to duplicate this piece of code *)
  let (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
      mremote_static, mremote_ephemeral, mpreshared =
      handshake_state_t_to_m st
  in
  [@inline_let]
  let mst : handshake_state_m nc =
    (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
    mremote_static, mremote_ephemeral, mpreshared
  in
  (**) let smi : Ghost.erased _ = initialize_post_smi hsk initiator (not (g_is_null psk)) in
  (**) handshake_state_t_to_m_impl_hsm_inv h0 mst st smi;
  (**) assert(hsm_inv h0 mst smi);
  (**) eval_handshake_state_eq h0 mst st smi;
  (**) initialize_unfold_lem h0.[|protocol_name|] h0.[|prologue|]
                             (eval_opt_split_keypair h0 spriv spub)
                             (eval_opt_split_keypair h0 epriv epub)
                             (eval_opt_preshared_key h0 psk);
  // We introduce "useless" let bindings so that the pointers are not inlined
  // (if those pointers are NULL, the nullity check will not extract correctly
  // to C otherwise).
  let spriv = spriv in
  let s_null = is_null spriv in
  [@inline_let] let spriv = if s_null then () else spriv in
  [@inline_let] let spub = if s_null then () else spub in
  let epriv = epriv in
  let e_null = is_null epriv in
  [@inline_let] let epriv = if e_null then () else epriv in
  [@inline_let] let epub = if e_null then () else epub in
  let psk = psk in
  let psk_null = is_null psk in
  [@inline_let] let psk = if psk_null then () else psk in
  initialize_handshake_state_impl pname_len protocol_name prlg_len prologue
                                  #(not s_null) spriv spub #(not e_null) epriv epub
                                  #false () #false () #(not psk_null) psk mst
#pop-options

inline_for_extraction noextract
type initialize_from_lists_st (nc : iconfig) =
  hsk : Ghost.erased handshake_pattern ->
  protocol_name_v : list uint8 {
    let l = normalize_term(List.length protocol_name_v) in
    l > 0 /\ l + hash_size (get_config nc) <= max_size_t} ->
  prologue_v : list uint8 {
    let l = normalize_term(List.length prologue_v) in
    l > 0 /\ l + hash_size (get_config nc) <= max_size_t} ->
  initiator : Ghost.erased bool ->
  spriv : opt_private_key_t nc ->
  spub : opt_public_key_t nc ->
  epriv : opt_private_key_t nc ->
  epub : opt_public_key_t nc ->
  psk : opt_preshared_key_t ->
  st : handshake_state_t nc ->
  Stack (rtype hash_return_type)
  (requires (fun h ->
     initialize_gen_pre hsk initiator spriv spub epriv epub psk st h))
  (ensures (fun h0 r h1 ->
     (**) normalize_term_spec(List.length protocol_name_v);
     (**) normalize_term_spec(List.length prologue_v);
     (**) hash_max_input_norm_lem (get_config nc);
     initialize_gen_post hsk initiator
                         (of_list protocol_name_v) (of_list prologue_v)
                         spriv spub epriv epub psk st h0 r h1))

#push-options "--z3rlimit 100 --ifuel 1"
inline_for_extraction noextract
let initialize_from_lists_m
    (#nc : iconfig)
    (initialize_handshake_state_impl : initialize_handshake_state_st nc) :
    initialize_from_lists_st nc =
  fun hsk protocol_name_v prologue_v initiator spriv spub epriv epub psk st ->
  (**) normalize_term_spec(List.length protocol_name_v);
  (**) normalize_term_spec(List.length prologue_v);
  (**) let h0 = HST.get () in
  push_frame();
  [@inline_let] let pname_len_v = normalize_term(List.length protocol_name_v) in
  [@inline_let] let pname_len = size pname_len_v in
  let pname = if pname_len_v > 0 then createL protocol_name_v else null in
  [@inline_let] let prlg_len_v = normalize_term(List.length prologue_v) in
  [@inline_let] let prlg_len = size prlg_len_v in
  let prlg = if prlg_len_v > 0 then createL prologue_v else null in
  (**) let h1 = HST.get () in
  (**) hash_max_input_norm_lem (get_config nc);
  let r = initialize_m initialize_handshake_state_impl hsk initiator pname_len pname
                       prlg_len prlg spriv spub epriv epub psk st in
  (**) let h2 = HST.get () in
  assert(h1.[|pname|] `S.equal` (of_list protocol_name_v));
  assert(h1.[|prlg|] `S.equal` (of_list prologue_v));
  assert(
    let protocol_name_v_seq = of_list protocol_name_v in
    let prologue_v_seq = of_list prologue_v in
    let smi = initialize_post_smi hsk initiator (not (g_is_null psk)) in
    let s_v = eval_opt_split_keypair h1 spriv spub in
    let e_v = eval_opt_split_keypair h1 epriv epub in
    let psk_v = eval_opt_preshared_key h1 psk in
    let st1_v = eval_handshake_state h2 st smi in
    st1_v == Spec.initialize protocol_name_v_seq prologue_v_seq s_v e_v psk_v);
  pop_frame();
  (**) let h3 = HST.get () in
  (**) assert(modifies1 st h0 h3);
  r
#pop-options


(*** csend/creceive_premessage *)
(**** Shared utilities and lemmas *)
#push-options "--fuel 3 --ifuel 2"
let wf_handshake_pattern_pre_length_lem (hsk : wf_handshake_pattern) :
  Lemma(forall ir. List.length (get_premessage hsk ir) <= 2) = ()
#pop-options

noextract
let premessage_vsv (nc : iconfig) (hsk : wf_handshake_pattern) (ir : bool) :
  size_nat =
  let pattern = get_premessage hsk ir in
  (**) wf_handshake_pattern_pre_length_lem hsk;
  (**) assert(List.length pattern * (public_key_vsv nc) <= max_size_t);
  List.length pattern * (public_key_vsv nc)

noextract
let premessage_vs (nc : iconfig) (hsk : wf_handshake_pattern) (ir : bool) :
  size_t =
  size (premessage_vsv nc hsk ir)

inline_for_extraction noextract
type premessage_t (nc : iconfig) (hsk : wf_handshake_pattern) (ir : bool) =
  lbuffer uint8 (premessage_vs nc hsk ir)

(**** csend_premessage *)
#push-options "--z3rlimit 50 --fuel 3 --ifuel 3"
let csend_premessage_pre_lem (hsk : wf_handshake_pattern) (ir has_psk : bool) :
    Lemma(
      let pattern = get_premessage hsk ir in
      let smi = csend_premessage_pre_smi hsk ir has_psk in
      has_pretokens smi pattern) =
  let pattern = get_premessage hsk ir in
  let smi = csend_premessage_pre_smi hsk ir has_psk in
  let hskf = compute_hsk_flags hsk in
  match pattern with
  | [PE; PS] -> ()
  | [PS] -> ()
  | [PE] -> ()
  | _ -> ()
#pop-options

/// Auxiliary type definition
inline_for_extraction noextract
type csend_premessage_gen_st
  (nc : iconfig)
  (hsk : wf_handshake_pattern)
  (* The premessage mustn't be None *)
  (ir : bool {normalize_term #bool (has_premessage hsk ir)})
  (* If has_psk is true, the pattern must be a PSK one *)
  (has_psk : bool {normalize_term #bool (psk_flag_premessage_cond hsk has_psk)})
  =
  st : handshake_state_t nc ->
  out : premessage_t nc hsk ir ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h -> live h st /\ live h out /\ disjoint st out /\ get_hash_pre nc))
  (ensures (fun h0 r h1 -> modifies2 (hs_gget_sym_state st) out h0 h1 /\
              begin
              let smi0 = csend_premessage_pre_smi hsk ir has_psk in
              let smi1 = csend_premessage_post_smi hsk ir has_psk in
              let st0_v = eval_handshake_state h0 st smi0 in
              let st1_v = eval_handshake_state h1 st smi1 in
              let r1_v = Spec.csend_premessage (get_config nc) hsk ir st0_v in
              match to_prim_error_code r,  r1_v with
              | CSuccess, Res (msg_v, st1'_v) ->
                S.length msg_v == length out /\
                msg_v `S.equal` h1.[|out|] /\ st1_v == st1'_v
              | _ -> False
              end))

/// Type definition for `csend_premessage` (this is the function which will be
/// manipulated by the user). We just abstract away some parameters.
inline_for_extraction noextract
type csend_premessage_st (nc : iconfig) =
  hsk : wf_handshake_pattern ->
  (* The premessage mustn't be None *)
  ir : bool {normalize_term #bool (has_premessage hsk ir)} ->
  (* If has_psk is true, the pattern must be a PSK one *)
  has_psk : bool {normalize_term #bool (psk_flag_premessage_cond hsk has_psk)} ->
  csend_premessage_gen_st nc hsk ir has_psk

/// Auxiliary ype definition for `csend_premessage_m_aux`
inline_for_extraction noextract
type csend_premessage_m_aux_st (nc : iconfig) =
  hsk : wf_handshake_pattern ->
  (* The premessage mustn't be None *)
  ir : bool {normalize_term(has_premessage hsk ir) == true} ->
  (* If has_psk is true, the pattern must be a PSK one *)
  has_psk : bool {normalize_term(psk_flag_premessage_cond hsk has_psk) == true} ->
  (* The pre-message pattern: we could retrieve it from the handshake pattern,
   * but for normalization purposes, it is better to receive it as a parameter *)
  pattern : list premessage_token{pattern = get_premessage hsk ir} ->
  csend_premessage_gen_st nc hsk ir has_psk

#push-options "--z3rlimit 50"
noextract
let csend_premessage_m_aux
    (#nc : iconfig)
    (send_premessage_tokens_impl : send_premessage_tokens_st nc) :
    csend_premessage_m_aux_st nc =
  fun hsk ir has_psk pattern st out ->
  [@inline_let] let smi : Ghost.erased meta_info = csend_premessage_pre_smi hsk ir has_psk in
  (**) csend_premessage_pre_lem hsk ir has_psk;
  (**) wf_handshake_pattern_pre_length_lem hsk;
  (**) csend_creceive_cexchange_smi_consistent_lem hsk has_psk;
  (* We need to use a small trick to ensure the tuples will be inlined by Kremlin *)
  let (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
      mremote_static, mremote_ephemeral, mpreshared =
      handshake_state_t_to_m st
  in
  [@inline_let]
  let mst : handshake_state_m nc =
    (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
    mremote_static, mremote_ephemeral, mpreshared
  in
  (**) let h0 = HST.get () in
  (**) handshake_state_t_to_m_impl_hsm_inv h0 mst st smi;
  (**) assert(hsm_inv h0 mst smi);
  (**) handshake_state_t_to_m_disjoint_impl mst st out;
  (**) assert(hsm_disjoint mst out);
  (**) eval_handshake_state_eq h0 mst st smi;
  (**) eval_handshake_state_eq h0 mst st (csend_premessage_post_smi hsk ir has_psk);
  let r = send_premessage_tokens_impl smi pattern mst out in
  (**) let h1 = HST.get () in
  (**) assert(modifies2 (hs_gget_sym_state st) out h0 h1);
  r
#pop-options

noextract
let csend_premessage_m
    (#nc : iconfig)
    (send_premessage_tokens_impl : send_premessage_tokens_st nc) :
    csend_premessage_st nc =
  fun hsk ir has_psk ->
  csend_premessage_m_aux send_premessage_tokens_impl hsk ir has_psk (get_premessage hsk ir)

(**** creceive_premessage *)
#push-options "--z3rlimit 25 --fuel 3 --ifuel 3"
let creceive_premessage_pre_lem (hsk : wf_handshake_pattern)
                                (ir : bool{has_premessage hsk ir})
                                (has_psk : bool) :
  Lemma(
    let pattern = get_premessage hsk ir in
    let smi = creceive_premessage_pre_smi hsk ir has_psk in
    no_remote_pretokens smi pattern) =
  let pattern = get_premessage hsk ir in
  let smi = creceive_premessage_pre_smi hsk ir has_psk in
  let hskf = compute_hsk_flags hsk in
  match pattern with
  | [PE; PS] -> ()
  | [PS] -> ()
  | [PE] -> ()
  | _ -> () (* impossible *)
#pop-options

/// Auxiliary type definition
inline_for_extraction noextract
type creceive_premessage_gen_st
  (nc : iconfig)
  (hsk : wf_handshake_pattern)
  (* The premessage mustn't be None *)
  (ir : bool {normalize_term #bool (has_premessage hsk ir)})
  (* If has_psk is true, the pattern must be a PSK one *)
  (has_psk : bool {normalize_term #bool (psk_flag_premessage_cond hsk has_psk)}) =
  st : handshake_state_t nc ->
  input : premessage_t nc hsk ir ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h -> live h st /\ live h input /\ disjoint st input /\ get_hash_pre nc))
  (ensures (fun h0 r h1 -> modifies1 st h0 h1 /\
              begin
              let smi0 = creceive_premessage_pre_smi hsk ir has_psk in
              let smi1 = creceive_premessage_post_smi hsk ir has_psk in
              let st0_v = eval_handshake_state h0 st smi0 in
              let st1_v = eval_handshake_state h1 st smi1 in
              let input_v = h0.[|input|] in (* TODO: pb if [<:]: do a minimal repro *)
              let r1_v = Spec.creceive_premessage (get_config nc) hsk ir input_v st0_v in
              match to_prim_error_code r, r1_v with
              | CSuccess, Res st1'_v -> st1_v == st1'_v
              | _ -> False
              end))

/// Type definition for `creceive_premessage` (this is the function which will be
/// manipulated by the user). We just abstract away some parameters.
inline_for_extraction noextract
type creceive_premessage_st (nc : iconfig) =
  hsk : wf_handshake_pattern ->
  (* The premessage mustn't be None *)
  ir : bool {normalize_term #bool (has_premessage hsk ir)} ->
  (* If has_psk is true, the pattern must be a PSK one *)
  has_psk : bool {normalize_term #bool (psk_flag_premessage_cond hsk has_psk)} ->
  creceive_premessage_gen_st nc hsk ir has_psk

/// Auxilary type definition for `creceive_premessage_m_aux`
inline_for_extraction noextract
type creceive_premessage_m_aux_st (nc : iconfig) =
  hsk : wf_handshake_pattern ->
  (* The premessage mustn't be None *)
  ir : bool {normalize_term #bool (has_premessage hsk ir)} ->
  (* If has_psk is true, the pattern must be a PSK one *)
  has_psk : bool {normalize_term #bool (psk_flag_premessage_cond hsk has_psk)} ->
  (* The pre-message pattern: we could retrieve it from the handshake pattern,
   * but for normalization purposes, it is better to receive it as a parameter *)
  pattern : list premessage_token{pattern = get_premessage hsk ir} ->
  creceive_premessage_gen_st nc hsk ir has_psk

#push-options "--z3rlimit 100"
noextract
let creceive_premessage_m_aux
    (#nc : iconfig)
    (receive_premessage_tokens_impl : receive_premessage_tokens_st nc) :
    creceive_premessage_m_aux_st nc =
 fun hsk ir has_psk pattern st input ->
  [@inline_let] let smi = creceive_premessage_pre_smi hsk ir has_psk in
  (**) creceive_premessage_pre_lem hsk ir has_psk;
  (**) wf_handshake_pattern_pre_length_lem hsk;
  (**) csend_creceive_cexchange_smi_consistent_lem hsk has_psk;
  (* We need to use a small trick to ensure the tuples will be inlined by Kremlin *)
  let (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
      mremote_static, mremote_ephemeral, mpreshared =
      handshake_state_t_to_m st
  in
  [@inline_let]
  let mst : handshake_state_m nc =
    (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
    mremote_static, mremote_ephemeral, mpreshared
  in
  (**) let h0 = HST.get () in
  (**) handshake_state_t_to_m_impl_hsm_inv h0 mst st smi;
  (**) assert(hsm_inv h0 mst smi);
  (**) handshake_state_t_to_m_disjoint_impl mst st input;
  (**) assert(hsm_disjoint mst input);
  (**) eval_handshake_state_eq h0 mst st smi;
  (**) eval_handshake_state_eq h0 mst st (creceive_premessage_post_smi hsk ir has_psk);
  let r = receive_premessage_tokens_impl smi pattern mst input in
  (**) let h1 = HST.get () in
  (**) assert(modifies1 st h0 h1);
  r
#pop-options

noextract
let creceive_premessage_m
    (#nc : iconfig)
    (receive_premessage_tokens_impl : receive_premessage_tokens_st nc) :
    creceive_premessage_st nc =
 fun hsk ir has_psk ->
 creceive_premessage_m_aux receive_premessage_tokens_impl hsk ir has_psk
                           (get_premessage hsk ir)

(*** csend/creceive_message *)
(**** Shared utilities and lemmas *)

[@ (strict_on_arguments [3])]
noextract
let pat_message_vsv (nc : iconfig)
                    (hsk : wf_handshake_pattern)
                    (payload_len : size_nat{payload_len + aead_tag_size +
                                            hash_size (get_config nc) <= max_size_t})
                    (i : nat{i < List.length hsk.messages}) : nat =
  let is_psk = chskf_check_is_psk hsk in
  let smi = csend_message_pre_smi hsk true i in
  let msg = List.Tot.index hsk.messages i in
  let length = message_vsv nc smi is_psk msg payload_len in
  length

[@ (strict_on_arguments [3])]
noextract
let pat_message_vs (nc : iconfig)
                   (hsk : wf_handshake_pattern)
                   (payload_len : size_nat{payload_len + aead_tag_size +
                                            hash_size (get_config nc) <= max_size_t})
                   (i : nat{i < List.length hsk.messages}) :
  Pure size_t
  (requires (pat_message_vsv nc hsk payload_len i <= max_size_t))
  (ensures (fun _ -> True)) =
  size (pat_message_vsv nc hsk payload_len i)

inline_for_extraction noextract
type pat_message_t (nc : iconfig)
                   (hsk : wf_handshake_pattern)
                   (payload_len : size_nat{payload_len + aead_tag_size +
                                            hash_size (get_config nc) <= max_size_t})
                   (i : nat{i < List.length hsk.messages /\
                           pat_message_vsv nc hsk payload_len i <= max_size_t}) =
  lbuffer uint8 (pat_message_vs nc hsk payload_len i)

(* Condition on the psk flag for the premessages *)
[@ (strict_on_arguments [2])]
noextract
let psk_flag_message_cond (hsk : handshake_pattern) (psk : bool)
                          (i : nat{i < List.length hsk.messages}) : bool =
  (* [psk ==> hsk is psk] *)
  psk_flag_premessage_cond hsk psk &&
  (* [PSK is in hsk.messages[i] ==> psk] *)
  (if List.mem PSK (List.Tot.index hsk.messages i) then psk else true)

(**** csend_message *)
let csend_message_pre_lem
    (nc : iconfig)
    (hsk : wf_handshake_pattern)
    (i : nat{i < List.length hsk.messages})
    (has_psk : bool{List.mem PSK (List.Tot.index hsk.messages i) ==> has_psk})
    (payload_len : plain_message_len_t nc) :
    Lemma(
      let smi = csend_message_pre_smi hsk has_psk i in
      let initiator = is_even i in
      let is_psk = chskf_check_is_psk hsk in
      let pattern = List.Tot.index hsk.messages i in
      let outlen = pat_message_vsv nc hsk (size_v payload_len) i in
      outlen == message_vsv nc smi is_psk pattern (size_v payload_len) /\
      check_send_message_smi smi initiator is_psk pattern)
  =
  let smi = csend_message_pre_smi hsk has_psk i in
  let initiator = is_even i in
  let is_psk = chskf_check_is_psk hsk in
  let pattern = List.Tot.index hsk.messages i in
  let outlen = pat_message_vsv nc hsk (size_v payload_len) i in
  (* For outlen: the initial psk value makes no difference *)
  csend_creceive_message_pre_smi_psk_frame_lem hsk i;
  assert(outlen == message_vsv nc smi is_psk pattern (size_v payload_len));
  (* Condition on the tokens of the pattern *)
  check_hsk_wf_csend_creceive_message_smi_precond_psk_no_diff_lem hsk has_psk i

let csend_message_pre_post_smi_lem
    (nc : iconfig)
    (hsk : wf_handshake_pattern)
    (i : nat{i < List.length hsk.messages})
    (has_psk : bool) :
    Lemma(
      let smi0 = csend_message_pre_smi hsk has_psk i in
      let smi1 = csend_message_post_smi hsk has_psk i in
      let is_psk = chskf_check_is_psk hsk in
      let pattern = List.Tot.index hsk.messages i in
      let smi1' = send_message_update_smi is_psk pattern smi0 in
      smi1' == smi1) =
  let ismi0, rsmi0, is_psk = compute_premessages_post_smi hsk has_psk in
  handshake_messages_pre_smi_step_lem is_psk true ismi0 rsmi0 hsk.messages i

inline_for_extraction noextract
let csend_message_return_type (nc : iconfig) (hsk : wf_handshake_pattern)
                              (i : nat{i < List.length hsk.messages})
                              (has_psk : bool) : return_type =
  let smi0 = with_norm(csend_message_pre_smi hsk has_psk i) in
  let is_psk = with_norm(chskf_check_is_psk hsk) in
  let pat = with_norm(get_message hsk i) in
  with_norm(send_message_return_type smi0 is_psk pat)

#push-options "--z3rlimit 25 --fuel 1 --ifuel 1"
inline_for_extraction noextract
let to_csend_message_rtype
  (nc : iconfig) (hsk : wf_handshake_pattern) (i : nat{i < List.length hsk.messages})
  (has_psk : bool)
  (smi : meta_info{smi == csend_message_pre_smi hsk has_psk i})
  (is_psk : bool{is_psk == chskf_check_is_psk hsk})
  (r : rtype (send_message_return_type smi is_psk (List.Tot.Base.index hsk.messages i))) :
  r':rtype (csend_message_return_type nc hsk i has_psk) {
    to_prim_error_code r == to_prim_error_code r' } =
  convert_type #(rtype (send_message_return_type smi is_psk (List.Tot.Base.index hsk.messages i)))
               #(rtype (csend_message_return_type nc hsk i has_psk))
               r
#pop-options

/// Auxiliary type definition
#push-options "--z3rlimit  25"
inline_for_extraction noextract
type csend_message_gen_st
  (nc : iconfig)
  (hsk : wf_handshake_pattern)
  (i : nat{i < List.length hsk.messages})
  (* If has_psk is true, the pattern must be a PSK one *)
  (has_psk : bool {
     normalize_term #bool (psk_flag_message_cond hsk has_psk i)}) =
  payload_len : plain_message_len_t nc {
     normalize_term(pat_message_vsv nc hsk (size_v payload_len) i) <= max_size_t} ->
  payload : lbuffer uint8 payload_len ->
  st : handshake_state_t nc ->
  out : pat_message_t nc hsk (size_v payload_len) i ->
  Stack (rtype (csend_message_return_type nc hsk i has_psk))
  (requires (
    fun h -> live h st /\ live h out /\ live h payload /\
           disjoint st out /\ disjoint st payload /\ disjoint payload out /\
           get_pres nc))
  (ensures (
    fun h0 r h1 ->
    modifies2 st out h0 h1 /\
    begin
    let smi0 = csend_message_pre_smi hsk has_psk i in
    let smi1 = csend_message_post_smi hsk has_psk i in
    let st0_v = eval_handshake_state h0 st smi0 in
    let st1_v = eval_handshake_state h1 st smi1 in
    let payload_v = h0.[|payload|] in
    begin match to_prim_error_code r,
                Spec.csend_message (get_config nc) hsk i payload_v st0_v with
    | CDH_error, Fail DH -> True
    | CSuccess, Res (out_v, st1'_v) ->
      st1_v == st1'_v /\ length out == S.length out_v /\
      h1.[|out|] `S.equal` out_v
    | _ -> False
    end end))
#pop-options

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
type csend_message_st (nc : iconfig) =
  hsk : wf_handshake_pattern ->
  i : nat{i < normalize_term #nat (List.length hsk.messages)} ->
  (* If has_psk is true, the pattern must be a PSK one *)
  has_psk : bool {
     normalize_term #bool (psk_flag_message_cond hsk has_psk i)} ->
  csend_message_gen_st nc hsk i has_psk
#pop-options

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
type csend_message_m_aux_st (nc : iconfig) =
  hsk : wf_handshake_pattern ->
  i : nat{i < normalize_term #nat (List.length hsk.messages)} ->
  (* If has_psk is true, the pattern must be a PSK one *)
  has_psk : bool {
     normalize_term #bool (psk_flag_message_cond hsk has_psk i)} ->
  (* The message pattern: we could retrieve it from the handshake pattern,
   * but for normalization purposes, it is better to receive it as a parameter *)
  pattern : list message_token{pattern = List.Tot.index hsk.messages i} ->
  csend_message_gen_st nc hsk i has_psk
#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
noextract
let csend_message_m_aux
    (#nc : iconfig)
    (send_message_tokens_with_payload_impl : send_message_tokens_with_payload_st nc) :
    csend_message_m_aux_st nc =
  fun hsk i has_psk pattern payload_len payload st out ->
  [@inline_let] let smi_nn = csend_message_pre_smi hsk has_psk i in
  [@inline_let] let smi = with_norm(smi_nn) in
  [@inline_let] let initiator_nn = is_even i in
  [@inline_let] let initiator = with_norm(initiator_nn) in
  [@inline_let] let is_psk_nn = chskf_check_is_psk hsk in
  [@inline_let] let is_psk = with_norm(is_psk_nn) in
  [@inline_let] let outlen_nn = pat_message_vs nc hsk (size_v payload_len) i in
  [@inline_let] let outlen = with_norm(outlen_nn) in
  (**) csend_message_pre_lem nc hsk i has_psk payload_len;
  (**) csend_message_pre_post_smi_lem nc hsk i has_psk;
  let (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
      mremote_static, mremote_ephemeral, mpreshared =
      handshake_state_t_to_m st
  in
  [@inline_let]
  let mst : handshake_state_m nc =
    (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
    mremote_static, mremote_ephemeral, mpreshared
  in
  (**) let h0 = HST.get () in
  (**) handshake_state_t_to_m_impl_hsm_inv h0 mst st smi;
  (**) assert(hsm_inv h0 mst smi);
  (**) handshake_state_t_to_m_disjoint_impl mst st out;
  (**) assert(hsm_disjoint mst out);
  (**) handshake_state_t_to_m_disjoint_impl mst st payload;
  (**) assert(hsm_disjoint mst payload);
  (**) eval_handshake_state_eq h0 mst st smi;
  (**) eval_handshake_state_eq h0 mst st (csend_message_post_smi hsk has_psk i);
  let r = send_message_tokens_with_payload_impl smi initiator is_psk
                                                pattern
                                                payload_len payload mst outlen out in
  (**) let h1 = HST.get () in
  (**) hsm_modifies1_to_modifies2 mst st out h0 h1;
  to_csend_message_rtype nc hsk i has_psk smi is_psk r
#pop-options

#push-options "--fuel 1"
noextract
let csend_message_m
    (#nc : iconfig)
    (send_message_tokens_with_payload_impl : send_message_tokens_with_payload_st nc) :
    csend_message_st nc =
  fun hsk i has_psk ->
  csend_message_m_aux send_message_tokens_with_payload_impl hsk i has_psk
                      (List.Tot.index hsk.messages i)
#pop-options

(**** creceive_message *)
let creceive_message_pre_lem
    (nc : iconfig)
    (hsk : wf_handshake_pattern)
    (i : nat{i < List.length hsk.messages})
    (has_psk : bool{List.mem PSK (List.Tot.index hsk.messages i) ==> has_psk})
    (payload_outlen : plain_message_len_t nc) :
    Lemma(
      let smi = creceive_message_pre_smi hsk has_psk i in
      let initiator = not (is_even i) in
      let is_psk = chskf_check_is_psk hsk in
      let pattern = List.Tot.index hsk.messages i in
      let inlen = pat_message_vsv nc hsk (size_v payload_outlen) i in
      inlen == message_vsv nc smi is_psk pattern (size_v payload_outlen) /\
      check_receive_message_smi smi initiator is_psk pattern)
    =
  let smi = creceive_message_pre_smi hsk has_psk i in
  let initiator = not (is_even i) in
  let is_psk = chskf_check_is_psk hsk in
  let pattern = List.Tot.index hsk.messages i in
  let inlen = pat_message_vsv nc hsk (size_v payload_outlen) i in
  (* For inlen: the initial psk value makes no difference. Moreover,
   * the sk flag is the same for the pre smi of csend_message and
   * creceive_message *)
  csend_creceive_message_pre_smi_same_sk_lem hsk i has_psk;
  csend_creceive_message_pre_smi_psk_frame_lem hsk i;
  assert(inlen == message_vsv nc smi is_psk pattern (size_v payload_outlen));
  (* Condition on the tokens of the pattern *)
  check_hsk_wf_csend_creceive_message_smi_precond_psk_no_diff_lem hsk has_psk i

let creceive_message_pre_post_smi_lem
    (hsk : wf_handshake_pattern)
    (i : nat{i < List.length hsk.messages})
    (has_psk : bool) :
    Lemma(
      let is_psk = chskf_check_is_psk hsk in
      let pattern = List.Tot.index hsk.messages i in
      let smi0 = creceive_message_pre_smi hsk has_psk i in
      let smi1 = creceive_message_post_smi hsk has_psk i in
      let smi1' = receive_message_update_smi is_psk pattern smi0 in
      smi1' == smi1)
    =
  let ismi0, rsmi0, is_psk = compute_premessages_post_smi hsk has_psk in
  handshake_messages_pre_smi_step_lem is_psk true ismi0 rsmi0 hsk.messages i

inline_for_extraction noextract
let creceive_message_return_type (nc : iconfig) (hsk : wf_handshake_pattern)
                                 (i : nat{i < List.length hsk.messages})
                                 (has_psk : bool) :
  return_type =
  let smi0 = with_norm(creceive_message_pre_smi hsk has_psk i) in
  let is_psk = with_norm(chskf_check_is_psk hsk) in
  let pat = with_norm(get_message hsk i) in
  with_norm(receive_message_return_type smi0 is_psk pat)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
inline_for_extraction noextract
let to_creceive_message_rtype
  (nc : iconfig) (hsk : wf_handshake_pattern) (i : nat{i < List.length hsk.messages})
  (has_psk : bool)
  (smi : meta_info{smi == creceive_message_pre_smi hsk has_psk i})
  (is_psk : bool{is_psk == chskf_check_is_psk hsk})
  (r : rtype (receive_message_return_type smi is_psk (List.Tot.Base.index hsk.messages i))) :
  r':rtype (creceive_message_return_type nc hsk i has_psk) {
    to_prim_error_code r == to_prim_error_code r' } =
  convert_type #(rtype (receive_message_return_type smi is_psk (List.Tot.Base.index hsk.messages i)))
               #(rtype (creceive_message_return_type nc hsk i has_psk))
               r
#pop-options

/// Auxiliary type definition
#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
type creceive_message_gen_st
  (nc : iconfig)
  (hsk : wf_handshake_pattern)
  (i : nat{i < normalize_term #nat (List.length hsk.messages)})
  (* If has_psk is true, the pattern must be a PSK one *)
  (has_psk : bool {normalize_term #bool (psk_flag_message_cond hsk has_psk i)}) =
  payload_outlen : plain_message_len_t nc {
      normalize_term #nat (pat_message_vsv nc hsk (size_v payload_outlen) i) <= max_size_t} ->
  payload_out : lbuffer uint8 payload_outlen ->
  st : handshake_state_t nc ->
  input : pat_message_t nc hsk (size_v payload_outlen) i ->
  Stack (rtype (creceive_message_return_type nc hsk i has_psk))
  (requires (
    fun h -> live h st /\ live h payload_out /\ live h input /\
           disjoint st payload_out /\ disjoint st input /\ disjoint payload_out input /\
           get_pres nc))
  (ensures (
    fun h0 r h1 ->
    modifies2 payload_out st h0 h1 /\
    begin
    let smi0 = creceive_message_pre_smi hsk has_psk i in
    let smi1 = creceive_message_post_smi hsk has_psk i in
    let st0_v = eval_handshake_state h0 st smi0 in
    let st1_v = eval_handshake_state h1 st smi1 in
    let input_v = h0.[|input|] in
    let payload_out_v = h1.[|payload_out|] in
    begin match to_prim_error_code r,
                Spec.creceive_message (get_config nc) hsk i input_v st0_v with
    | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
    | CSuccess, Res (payload_out_v', st1'_v) ->
      st1_v == st1'_v /\ S.length payload_out_v' == S.length payload_out_v /\
      payload_out_v' `S.equal` payload_out_v
    | _ -> False
    end end))
#pop-options

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
type creceive_message_st (nc : iconfig) =
  hsk : wf_handshake_pattern ->
  i : nat{i < normalize_term #nat (List.length hsk.messages)} ->
  (* If has_psk is true, the pattern must be a PSK one *)
  has_psk : bool {normalize_term #bool (psk_flag_message_cond hsk has_psk i)} ->
  creceive_message_gen_st nc hsk i has_psk
#pop-options

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
type creceive_message_m_aux_st (nc : iconfig) =
  hsk : wf_handshake_pattern ->
  i : nat{i < List.length hsk.messages} ->
  (* If has_psk is true, the pattern must be a PSK one *)
  has_psk : bool {psk_flag_message_cond hsk has_psk i} ->
  (* The message pattern: we could retrieve it from the handshake pattern,
   * but for normalization purposes, it is better to receive it as a parameter *)
  pattern : list message_token{pattern = List.Tot.index hsk.messages i} ->
  creceive_message_gen_st nc hsk i has_psk
#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
noextract
let creceive_message_m_aux
    (#nc : iconfig)
    (receive_message_tokens_with_payload_impl : receive_message_tokens_with_payload_st nc) :
    creceive_message_m_aux_st nc =
  fun hsk i has_psk pattern payload_outlen payload_out st input ->
  [@inline_let] let smi_nn = creceive_message_pre_smi hsk has_psk i in
  [@inline_let] let smi = with_norm(smi_nn) in
  [@inline_let] let initiator_nn = not (is_even i) in
  [@inline_let] let initiator = with_norm(initiator_nn) in
  [@inline_let] let is_psk_nn = chskf_check_is_psk hsk in
  [@inline_let] let is_psk = with_norm(is_psk_nn) in
  [@inline_let] let inlen_nn = pat_message_vs nc hsk (size_v payload_outlen) i in
  [@inline_let] let inlen = with_norm(inlen_nn) in
  (**) creceive_message_pre_lem nc hsk i has_psk payload_outlen;
  (**) creceive_message_pre_post_smi_lem hsk i has_psk;
  (* We need to use a small trick to ensure the tuples will be inlined by Kremlin *)
  let (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
      mremote_static, mremote_ephemeral, mpreshared =
      handshake_state_t_to_m st
  in
  [@inline_let]
  let mst : handshake_state_m nc =
    (mc_state, ms_ck, ms_h), (mspriv, mspub), (mepriv, mepub),
    mremote_static, mremote_ephemeral, mpreshared
  in
  (**) let h0 = HST.get () in
  (**) handshake_state_t_to_m_impl_hsm_inv h0 mst st smi;
  (**) assert(hsm_inv h0 mst smi);
  (**) handshake_state_t_to_m_disjoint_impl mst st input;
  (**) assert(hsm_disjoint mst input);
  (**) handshake_state_t_to_m_disjoint_impl mst st payload_out;
  (**) assert(hsm_disjoint mst payload_out);
  (**) eval_handshake_state_eq h0 mst st smi;
  (**) eval_handshake_state_eq h0 mst st (creceive_message_post_smi hsk has_psk i);
  let r = receive_message_tokens_with_payload_impl smi initiator is_psk
                                                   pattern
                                                   payload_outlen payload_out mst
                                                   inlen input in
  (**) let h1 = HST.get () in
  (**) hsm_modifies1_to_modifies2 mst st payload_out h0 h1;
  to_creceive_message_rtype nc hsk i has_psk smi is_psk r
#pop-options

#push-options "--fuel 1"
noextract
let creceive_message_m
    (#nc : iconfig)
    (receive_message_tokens_with_payload_impl : receive_message_tokens_with_payload_st nc) :
    creceive_message_st nc =
  fun hsk i has_psk ->
  creceive_message_m_aux receive_message_tokens_with_payload_impl hsk i has_psk
                         (List.Tot.index hsk.messages i)
#pop-options

(*** cset_psk *)
(*
 * In order for the pre/postconditions of the send/receive message token
 * functions to match, the user has to indicate when the psk is set, and
 * instanciate the [cset_psk] function properly if the psk is not set at
 * initiation.
 *)

inline_for_extraction noextract
type cset_psk_st (nc : iconfig) =
  hsk : wf_handshake_pattern {normalize_term #bool (chskf_check_is_psk hsk)} ->
  i : nat{i < normalize_term #nat (List.length hsk.messages)} ->
  initiator : bool ->
  psk : preshared_key_t ->
  st : handshake_state_t nc ->
  Stack unit
  (requires (
    fun h -> live h st /\ live h psk /\ disjoint st psk))
  (ensures (
    fun h0 _ h1 ->
    (**) normalize_term_spec(List.length hsk.messages);
    modifies1 st h0 h1 /\
    begin
    (* Find if the next function to execute is a send or a receive function *)
    let next_is_send = normalize_term(if initiator then is_even i else not (is_even i)) in
    let smi_pre_fun : bool -> GTot meta_info =
      if next_is_send then (fun pskb -> csend_message_pre_smi hsk pskb i)
                      else (fun pskb -> creceive_message_pre_smi hsk pskb i) in
    (* The smi is the same at the exception that the psk is now set *)
    let smi0 = smi_pre_fun false in
    let smi1 = smi_pre_fun true in
    let st0_v = eval_handshake_state h0 st smi0 in
    let st1_v = eval_handshake_state h1 st smi1 in
    let psk_v = h0.[|psk|] in
    let st1'_v = Spec.Noise.Base.set_psk psk_v st0_v in
    st1_v == st1'_v
    end))

#push-options "--z3rlimit 200"
inline_for_extraction noextract
let cset_psk_m (nc : iconfig) :
    cset_psk_st nc =
  fun hsk i initiator psk st ->
  (**) normalize_term_spec(chskf_check_is_psk hsk);
  (**) normalize_term_spec(i < List.length hsk.messages);
  (**) normalize_term_spec(if initiator then is_even i else not (is_even i));
  let st_psk = hs_get_preshared st in
  (**) csend_creceive_message_pre_smi_psk_frame_lem hsk i;
  update_sub st_psk 0ul preshared_key_vs psk
#pop-options


(*** Instanciation utilities *)
(**** Composed meta functions *)
/// 'cm': composed meta
let csend_premessage_cm (#nc : iconfig) (ssi : ss_impls nc) =
  csend_premessage_m (send_premessage_tokens_m (send_premessage_token_m ssi))

let creceive_premessage_cm (#nc : iconfig) (ssi : ss_impls nc) =
  creceive_premessage_m (receive_premessage_tokens_m (receive_premessage_token_m ssi))

let csend_message_cm (#nc : iconfig) (ssi : ss_impls nc)
                     (send_message_token : send_message_token_st nc) =
  csend_message_m (send_message_tokens_with_payload_m ssi
                    (send_message_tokens_m send_message_token))  

let creceive_message_cm (#nc : iconfig) (ssi : ss_impls nc)
                        (receive_message_token : receive_message_token_st nc) =
  creceive_message_m (receive_message_tokens_with_payload_m
                        (receive_message_tokens_nout_with_payload_m ssi
                          (receive_message_tokens_nout_m receive_message_token)))

(**** Functions containers *)

inline_for_extraction noextract
let hs_impls (nc : iconfig) =
  ssdh_impls nc &
  initialize_handshake_state_st nc &
  send_premessage_tokens_st nc &
  receive_premessage_tokens_st nc &
  send_message_tokens_with_payload_st nc &
  receive_message_tokens_with_payload_st nc

inline_for_extraction noextract
let hsi_get_ssdhi (#nc : iconfig) (hsi : hs_impls nc) :
  Tot (ssdh_impls nc) =
  norm [] (let (ssdhi, init, send_pre, rcv_pre, send_msg, rcv_msg) = hsi in ssdhi)

inline_for_extraction noextract
let hsi_get_initialize_handshake_state (#nc : iconfig) (hsi : hs_impls nc) :
  Tot (initialize_handshake_state_st nc) =
  norm [] (let (ssdhi, init, send_pre, rcv_pre, send_msg, rcv_msg) = hsi in init)

inline_for_extraction noextract
let hsi_get_send_premessage_tokens (#nc : iconfig) (hsi : hs_impls nc) :
  Tot (send_premessage_tokens_st nc) =
  norm [] (let (ssdhi, init, send_pre, rcv_pre, send_msg, rcv_msg) = hsi in send_pre)

inline_for_extraction noextract
let hsi_get_receive_premessage_tokens (#nc : iconfig) (hsi : hs_impls nc) :
  Tot (receive_premessage_tokens_st nc) =
  norm [] (let (ssdhi, init, send_pre, rcv_pre, send_msg, rcv_msg) = hsi in rcv_pre)

inline_for_extraction noextract
let hsi_get_send_message_tokens_with_payload (#nc : iconfig) (hsi : hs_impls nc) :
  Tot (send_message_tokens_with_payload_st nc) =
  norm [] (let (ssdhi, init, send_pre, rcv_pre, send_msg, rcv_msg) = hsi in send_msg)

inline_for_extraction noextract
let hsi_get_receive_message_tokens_with_payload (#nc : iconfig) (hsi : hs_impls nc) :
  Tot (receive_message_tokens_with_payload_st nc) =
  norm [] (let (ssdhi, init, send_pre, rcv_pre, send_msg, rcv_msg) = hsi in rcv_msg)

inline_for_extraction noextract
let compile_hs_impls (#nc : iconfig) (ssdhi : ssdh_impls nc) :
  Tot (hs_impls nc) =
  [@inline_let] let ssi = ssdhi_get_ssi ssdhi in
  [@inline_let] let send_message_token_impl = send_message_token_m ssdhi in
  [@inline_let] let send_message_tokens_impl = send_message_tokens_m send_message_token_impl in
  [@inline_let] let receive_message_token_impl = receive_message_token_m ssdhi in
  [@inline_let] let receive_message_tokens_nout_impl =
    receive_message_tokens_nout_m receive_message_token_impl in
  [@inline_let] let receive_message_tokens_nout_with_payload_impl =
    receive_message_tokens_nout_with_payload_m ssi receive_message_tokens_nout_impl in
  ssdhi,
  initialize_handshake_state_m ssi,
  send_premessage_tokens_m (send_premessage_token_m ssi),
  receive_premessage_tokens_m (receive_premessage_token_m ssi),
  send_message_tokens_with_payload_m ssi send_message_tokens_impl,
  receive_message_tokens_with_payload_m receive_message_tokens_nout_with_payload_impl

type handshake_functions_impls (nc : iconfig) =
  initialize_st nc &
  initialize_from_lists_st nc &
  csend_premessage_st nc &
  creceive_premessage_st nc &
  csend_message_st nc &
  creceive_message_st nc &
  cset_psk_st nc

inline_for_extraction noextract
let compile_handshake_functions_impls (#nc : iconfig) (hsi : hs_impls nc) :
  Tot (handshake_functions_impls nc) =
  initialize_m (hsi_get_initialize_handshake_state hsi),
  initialize_from_lists_m (hsi_get_initialize_handshake_state hsi),
  csend_premessage_m (hsi_get_send_premessage_tokens hsi),
  creceive_premessage_m (hsi_get_receive_premessage_tokens hsi),
  csend_message_m (hsi_get_send_message_tokens_with_payload hsi),
  creceive_message_m (hsi_get_receive_message_tokens_with_payload hsi),
  cset_psk_m nc

inline_for_extraction noextract
let initialize (#nc : iconfig) (hsi : handshake_functions_impls nc) :
  initialize_st nc =
  norm [] (let (init, initl, sp, rp, sm, rm, spsk) = hsi in init)

inline_for_extraction noextract
let initialize_from_lists (#nc : iconfig) (hsi : handshake_functions_impls nc) :
  initialize_from_lists_st nc =
  norm [] (let (init, initl, sp, rp, sm, rm, spsk) = hsi in initl)

inline_for_extraction noextract
let csend_premessage (#nc : iconfig) (hsi : handshake_functions_impls nc) :
  csend_premessage_st nc =
  norm [] (let (init, initl, sp, rp, sm, rm, spsk) = hsi in sp)

inline_for_extraction noextract
let creceive_premessage (#nc : iconfig) (hsi : handshake_functions_impls nc) :
  creceive_premessage_st nc =
  norm [] (let (init, initl, sp, rp, sm, rm, spsk) = hsi in rp)

inline_for_extraction noextract
let csend_message (#nc : iconfig) (hsi : handshake_functions_impls nc) :
  csend_message_st nc =
  norm [] (let (init, initl, sp, rp, sm, rm, spsk) = hsi in sm)

inline_for_extraction noextract
let creceive_message (#nc : iconfig) (hsi : handshake_functions_impls nc) :
  creceive_message_st nc =
  norm [] (let (init, initl, sp, rp, sm, rm, spsk) = hsi in rm)

inline_for_extraction noextract
let cset_psk (#nc : iconfig) (hsi : handshake_functions_impls nc) :
  cset_psk_st nc =
  norm [] (let (init, initl, sp, rp, sm, rm, spsk) = hsi in spsk)
