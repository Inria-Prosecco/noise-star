module Impl.Noise.API.State.Base

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

open Lib.Sequence
module S = Lib.Sequence
module L = FStar.List
module Seq = FStar.Seq

open Lib.Buffer
open LowStar.BufferOps

module LB = Lib.Buffer
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module G = FStar.Ghost

open Spec.Noise
open Spec.Noise.API
open Spec.Noise.API.State.Definitions
open Spec.Noise.API.State.Lemmas
module Spec = Spec.Noise.API.State
open Spec.Noise.API.MetaInfo

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
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate

module UInt64 = FStar.UInt64

open Meta.Noise

module Streaming = Hacl.Streaming.Interface
module St = Impl.Noise.Stateful

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// In the specification, we use different types to encode the error codes for
/// the different levels of the API. In the implementation, to prevent useless
/// conversions and in order not to clutter the code, we use one type [error_code],
/// which is the union of all the possible errors.
/// However, we define some refined types to implement the spec error codes as subsets
/// of this low-level error-code. Below is the refinement for [s_error_code].
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type s_error_code_or_success =
  e:error_code{
    (**) let _ = allow_inversion error_code in
    match e with
    | CSuccess
    | CIncorrect_transition
    | CPremessage
    | CNo_key
    | CAlready_key
    | CRs_rejected_by_policy -> True
    | CRs_not_certified -> False
    | CAlready_peer -> False
    | CPeer_conflict -> False
    | CUnknown_peer_id -> False
    | CInput_size
    | CDH_error
    | CDecrypt_error
    | CSaturated_nonce -> True
    | CEphemeral_generation -> False
    | CSecurity_level -> False
  }

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type s_error_code =
  e:s_error_code_or_success{e <> CSuccess}

[@@ noextract_to "Kremlin"] noextract
let s_error_code_v (e : s_error_code) : Spec.s_error =
  match e with
  | CIncorrect_transition -> Incorrect_transition
  | CPremessage -> Premessage
  | CNo_key -> No_key
  | CAlready_key -> Already_key
  | CRs_rejected_by_policy -> Rs_not_valid
  | CInput_size -> Input_size
  | CDH_error -> DH_error
  | CDecrypt_error -> Decryption
  | CSaturated_nonce -> Saturated_nonce

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let s_result_code a = result a s_error_code

(*** Type definitions *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let handshake_pattern_is_valid (pattern : handshake_pattern) : Tot bool =
  (pattern.premessage_ir = None || pattern.premessage_ir = Some [PS]) &&
  (pattern.premessage_ri = None || pattern.premessage_ri = Some [PS]) &&
  Cons? pattern.messages

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type stateful_peer_info = St.stateful unit//Streaming.stateful unit

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
noeq type stateful_validation_state (nc : iconfig)
                                    (peer_info : stateful_peer_info) =
| Stateful_vstate:

  vst : St.stateful unit ->

  recv_psk: bool ->

  // Pure operations
  validate_spec : validation_function (get_config nc) (vst.St.t ()) (peer_info.St.t ()) ->

  // Stateful operations
  validate: (
    state:vst.St.s () ->
    rs:public_key_t nc ->
    pinfo:(peer_info.St.s ()) -> // TODO: move to return value?
    psk:preshared_key_t_or_unit recv_psk ->
    ST bool
    (requires (fun h0 ->
      vst.St.invariant h0 state /\
      live h0 rs /\
      peer_info.St.invariant h0 pinfo /\
      lbuffer_or_unit_live h0 psk /\
      
      begin
      let state_loc = vst.St.footprint state in
      let rs_loc = B.loc_buffer (rs <: buffer uint8) in
      let pinfo_loc = peer_info.St.footprint pinfo in
      let psk_loc = if recv_psk then B.loc_buffer (psk <: buffer uint8) else B.loc_none in
      B.all_disjoint [state_loc; rs_loc; pinfo_loc; psk_loc]
      end
      ))
    (ensures (fun h0 res h1 ->
      let psk_loc = if recv_psk then B.loc_buffer (psk <: buffer uint8) else B.loc_none in
      // Note that the validation state CAN'T be modified. Allowing the validation
      // state to be modified makes things a lot more complex, because we can't
      // exactly link the spec to the implementation (because of the static analyses),
      // meaning we later on have trouble linking the updated validation state to the
      // original one in case of failure.
      B.(modifies (loc_union (peer_info.St.footprint pinfo) psk_loc) h0 h1) /\
    
      vst.St.invariant h1 state /\
      peer_info.St.invariant h1 pinfo /\
      lbuffer_or_unit_live h1 psk /\

      peer_info.St.footprint pinfo == peer_info.St.footprint pinfo /\
      (peer_info.St.freeable h0 pinfo ==> peer_info.St.freeable h1 pinfo) /\
      
      begin
      let state_v0 = vst.St.v () h0 state in
      let rs_v = B.as_seq h0 (rs <: buffer uint8) in
      let res_v = validate_spec state_v0 rs_v in
      begin match res_v with
      | None -> not res
      | Some (pinfo_v, psk_v) ->
        res /\
        pinfo_v == peer_info.St.v () h1 pinfo /\
        psk_v == lbuffer_or_unit_to_opt_lseq h1 psk
      end
      end /\
      
      True))) ->

  stateful_validation_state nc peer_info

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let vst_s (#nc : iconfig) (#peer_info : stateful_peer_info)
          (vst : stateful_validation_state nc peer_info) : Type0 =
  vst.vst.St.s ()

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let vst_t (#nc : iconfig) (#peer_info : stateful_peer_info)
          (vst : stateful_validation_state nc peer_info) : Type0 =
  vst.vst.St.t ()

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let vst_footprint (#nc : iconfig) (#peer_info : stateful_peer_info)
                  (#vst : stateful_validation_state nc peer_info)
                  (st : vst_s vst) =
  vst.vst.St.footprint st

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let vst_freeable (#nc : iconfig) (#peer_info : stateful_peer_info)
                 (#vst : stateful_validation_state nc peer_info)
                 (h : mem)
                 (st : vst_s vst) =
  vst.vst.St.freeable h st

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let vst_invariant (#nc : iconfig) (#peer_info : stateful_peer_info)
                  (#vst : stateful_validation_state nc peer_info)
                  (h : mem)
                  (st : vst_s vst) =
  vst.vst.St.invariant h st

/// Configurations
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
noeq type isconfig : Type u#1 = {
  isc_nc : iconfig;
  isc_sc : sc:sconfig{sc_get_config sc = get_config isc_nc};
  isc_pattern : wf_handshake_pattern; // TODO: in the spec, stored directly in the state
  isc_ks : key_slots;
  isc_pinfo : pi:stateful_peer_info{pi.St.t () == sc_get_pinfo isc_sc};
  isc_lookups_psk : bool;
}

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_nc : isconfig -> Tot iconfig =
  fun isc -> match isc with Mkisconfig nc sc pat ks pi lpsk -> nc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_config (isc : isconfig) = get_config (isc_get_nc isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_pinfo : isconfig -> Tot stateful_peer_info =
  fun isc -> match isc with Mkisconfig nc sc pat ks pi lpsk -> pi

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_sc : isc:isconfig ->
  Tot (sc:sconfig{isc_get_config isc == sc_get_config sc /\
                  (isc_get_pinfo isc).St.t () == sc_get_pinfo sc}) =
  fun isc -> match isc with Mkisconfig nc sc pat ks pi lpsk -> sc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_ks : isconfig -> Tot key_slots =
  fun isc -> match isc with Mkisconfig nc sc pat ks pi lpsk -> ks
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_pattern : isconfig -> Tot wf_handshake_pattern =
  fun isc -> match isc with Mkisconfig nc sc pat ks pi lpsk -> pat

/// Returns true if we lookup the psk when calling the validation function
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_lookups_psk (isc : isconfig) : bool =
  match isc with Mkisconfig nc sc pat ks pi lpsk -> lpsk

// We don't put [isc_validate] as a field inside [isconfig], because it leaves
// more flexibility for instanciation: later on, we can define [idconfig]
// monolitically, then define a maker function for [lookup_peer_by_id], declare
// it to preserve it in the call graph, then use this definition to generate
// an [isc_validate] instance that we give to [handshake_read]
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type isc_validate (isc : isconfig) =
    v:stateful_validation_state (isc_get_nc isc) (isc_get_pinfo isc){
      v.vst.St.t () == sc_get_vstate (isc_get_sc isc) /\
      Stateful_vstate?.validate_spec v == sc_get_validate (isc_get_sc isc) /\
      v.recv_psk == isc_lookups_psk isc}

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_s isc = ks_get_s (isc_get_ks isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_psk isc = ks_get_psk (isc_get_ks isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_rs isc = ks_get_rs (isc_get_ks isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_e isc = ks_get_e (isc_get_ks isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_re isc = ks_get_re (isc_get_ks isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_send isc = ks_get_send (isc_get_ks isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_get_receive isc = ks_get_receive (isc_get_ks isc)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let sprivate_key_t (isc : isconfig) = private_key_t_or_unit (isc_get_nc isc) (isc_get_s isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let spublic_key_t (isc : isconfig) = public_key_t_or_unit (isc_get_nc isc) (isc_get_s isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let eprivate_key_t (isc : isconfig) = private_key_t_or_unit (isc_get_nc isc) (isc_get_e isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let epublic_key_t (isc : isconfig) = public_key_t_or_unit (isc_get_nc isc) (isc_get_e isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let rspublic_key_t (isc : isconfig) = public_key_t_or_unit (isc_get_nc isc) (isc_get_rs isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let republic_key_t (isc : isconfig) = public_key_t_or_unit (isc_get_nc isc) (isc_get_re isc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let psk_t (isc : isconfig) = preshared_key_t_or_unit (isc_get_psk isc)

// TODO: move and use more
let mk_keypair_from_keys_or_unit (#isc : isconfig) (#b : bool) (h : mem)
                                 (priv : private_key_t_or_unit (isc_get_nc isc) b)
                                 (pub : public_key_t_or_unit (isc_get_nc isc) b) :
  GTot (option (keypair (isc_get_config isc))) =
  let priv = lbuffer_or_unit_to_opt_lseq h priv in
  let pub = lbuffer_or_unit_to_opt_lseq h pub in
  if b then Some (mk_keypair (Some?.v pub) (Some?.v priv)) else None

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_keypair_m_from_keys_or_unit (#isc : isconfig) (#b : bool)
                                   (priv : private_key_t_or_unit (isc_get_nc isc) b)
                                   (pub : public_key_t_or_unit (isc_get_nc isc) b) :
  Tot (keypair_m (isc_get_nc isc)) =
  [@inline_let]
  let priv = lbuffer_or_unit_to_lbuffer_or_null priv in
  let pub = lbuffer_or_unit_to_lbuffer_or_null pub in
  mk_keypair_m priv pub

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let step_to_status (initiator : bool) (step : nat) : status =
  if initiator then
    if step % 2 = 0 then Handshake_send step else Handshake_receive step
  else
    if step % 2 = 0 then Handshake_receive step else Handshake_send step

// We need to define [state_t] in two steps to ensure proper monomorphisation at
// extraction time
[@CAbstractStruct]
inline_for_extraction // inline the projectors
noeq type state_t_raw
  (nc : iconfig)
  (ks : key_slots)
  (recv_transport_message_t : Type0)
  (spriv_t spub_t epriv_t epub_t rs_t re_t psk_t
   send_key_t send_nonce_t receive_key_t receive_nonce_t : Type0)
  =
| IMS_Handshake :
     step:UInt32.t
  -> cipher_key:aead_key_t
  -> chaining_key:chaining_key_t nc
  -> h:hash_t nc
  // We keep pointers to the static keys. It removes an indirection and,
  // most importantly, doesn't force us to use a stateful operation to
  // have access to those keys (it would make the proofs much more cumbersome
  // otherwise).
  -> spriv:spriv_t // might be a pointer to a device owned key
  -> spub:spub_t // might be a pointer to a device owned key
  -> epriv:epriv_t
  -> epub:epub_t
  -> rs:rs_t
  -> re:re_t
  -> psk:psk_t // might be a pointer to a device owned key
  -> state_t_raw nc ks recv_transport_message_t
                 spriv_t spub_t epriv_t epub_t rs_t re_t psk_t
                 send_key_t send_nonce_t receive_key_t receive_nonce_t
| IMS_Transport :
     h:hash_t nc
  -> recv_transport_message : recv_transport_message_t
  -> send_key:send_key_t
  -> send_nonce:send_nonce_t
  -> receive_key:receive_key_t
  -> receive_nonce:receive_nonce_t
  -> state_t_raw nc ks recv_transport_message_t
                 spriv_t spub_t epriv_t epub_t rs_t re_t psk_t
                 send_key_t send_nonce_t receive_key_t receive_nonce_t

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type recv_transport_message_t (isc : isconfig) (initiator : bool) : Type0 =
  bool_or_gbool (save_received_transport initiator (isc_get_pattern isc))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let recv_transport_message_t_to_bool
  (#isc : isconfig) (#initiator : bool) (b : recv_transport_message_t isc initiator) :
  Tot bool =
  bool_or_gbool_to_bool b false

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_t (isc : isconfig) (initiator : bool) =
  state_t_raw (isc_get_nc isc)
  (isc_get_ks isc)
  (bool_or_gbool (save_received_transport initiator (isc_get_pattern isc)))
  (sprivate_key_t isc)
  (spublic_key_t isc)
  (eprivate_key_t isc)
  (epublic_key_t isc)
  (rspublic_key_t isc)
  (republic_key_t isc)
  (psk_t isc)
  (type_or_unit aead_key_t (isc_get_send isc))
  (type_or_unit aead_nonce_t (isc_get_send isc))
  (type_or_unit aead_key_t (isc_get_receive isc))
  (type_or_unit aead_nonce_t (isc_get_receive isc))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_t_is_handshake
  (#isc : isconfig) (#initiator : bool)
  (st : state_t isc initiator) : Tot bool = // IMS_Handshake? st
  match st with
  | IMS_Handshake _ _ _ _ _ _ _ _ _ _ _ -> true
  | _ -> false

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_t_is_transport (#isc:isconfig) (#initiator : bool) (st:state_t isc initiator) =
  not (state_t_is_handshake st)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_t_handshake_get_step :
     #isc:isconfig
  -> #initiator:bool
  -> st:state_t isc initiator{state_t_is_handshake st}
  -> UInt32.t =
  fun #isc #initiator st ->
  [@inline_let]
  let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk = st in
  step

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_t_handshake_get_static :
     #isc:isconfig
  -> #initiator:bool
  -> st:state_t isc initiator{state_t_is_handshake st}
  -> (sprivate_key_t isc & spublic_key_t isc) =
  fun #isc #initiator st ->
  [@inline_let]
  let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk = st in
  st_spriv, st_spub


val state_t_core_footprint (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator) : GTot B.loc

val state_t_footprint (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator) : GTot B.loc

val state_t_handshake_footprint_inclusion_lem (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator{state_t_is_handshake st}) :
  Lemma (
    let spriv, spub = state_t_handshake_get_static st in
    let l1 = B.(loc_union (state_t_core_footprint st)
                          (loc_union (lbuffer_or_unit_to_loc spriv)
                                     (lbuffer_or_unit_to_loc spub))) in
    let l2 = state_t_footprint st in
    B.loc_includes l1 l2 /\ B.loc_includes l2 l1)

val state_t_transport_footprint_inclusion_lem (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator{state_t_is_transport st}) :
  Lemma (
    let l1 = state_t_core_footprint st in
    let l2 = state_t_footprint st in
    l2 == l1)

val state_t_footprint_full_inclusion_lem (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator) :
  Lemma (
    let l1 = state_t_core_footprint st in
    let l2 = state_t_footprint st in
    if state_t_is_handshake st then
      let spriv, spub = state_t_handshake_get_static st in
      let l1 = B.(loc_union (state_t_core_footprint st)
                            (loc_union (lbuffer_or_unit_to_loc spriv)
                                       (lbuffer_or_unit_to_loc spub))) in
      let l2 = state_t_footprint st in
      B.loc_includes l1 l2 /\ B.loc_includes l2 l1
    else
      let l1 = state_t_core_footprint st in
      let l2 = state_t_footprint st in
      l2 == l1)

val state_t_footprint_inclusion_lem (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator) :
  Lemma (
    let l1 = state_t_core_footprint st in
    let l2 = state_t_footprint st in
    B.loc_includes l2 l1)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val state_t_handshake_get_rs :
     #isc:isconfig
  -> #initiator:bool
  -> st:state_t isc initiator{state_t_is_handshake st}
  -> rs:rspublic_key_t isc{
       B.loc_includes (state_t_core_footprint st) (lbuffer_or_unit_to_loc rs)}

val state_t_invariant_stateful (#isc : isconfig) (#initiator : bool) (m : mem) (st : state_t isc initiator) : GTot Type0

val state_t_handshake_invariant_stateful_live_rs
  (#isc : isconfig) (#initiator : bool) (m : mem) (st : state_t isc initiator{state_t_is_handshake st}) :
  Lemma
  (requires (state_t_invariant_stateful m st))
  (ensures (lbuffer_or_unit_live m (state_t_handshake_get_rs st)))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val isc_valid_meta_info (isc : isconfig) (smi : meta_info) : bool

val isc_valid_meta_info_lem (isc : isconfig) (smi : meta_info) :
  Lemma (isc_valid_meta_info isc smi = ks_valid_meta_info (isc_get_ks isc) smi)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let isc_has_valid_pattern (isc : isconfig) : Tot bool =
  let pattern = isc_get_pattern isc in
  handshake_pattern_is_valid pattern

#push-options "--ifuel 1"
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_t_get_received_transport_message
  (#isc : isconfig) (#initiator : bool)
  (st : state_t isc initiator) :
  GTot bool =
  match st with
  | IMS_Handshake _ _ _ _ _ _ _ _ _ _ _ -> false
  | IMS_Transport _ b _ _ _ _ -> bool_or_gbool_to_gbool b
#pop-options

#push-options "--ifuel 1"
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_t_get_hash (#isc : isconfig) (#initiator : bool)
                     (st : state_t isc initiator) :
  hash_t (isc_get_nc isc) =
  match st with
  | IMS_Handshake _ _ _ h _ _ _ _ _ _ _ -> h
  | IMS_Transport h _ _ _ _ _ -> h
#pop-options

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val state_t_get_hash_lem (#isc : isconfig) (#initiator : bool)
                         (st : state_t isc initiator)
                         (h : mem) :
  Lemma
  (requires (state_t_invariant_stateful h st))
  (ensures (
    let hash = state_t_get_hash st in
    B.loc_includes (state_t_core_footprint st) (loc hash) /\
    live h hash))

// TODO: this has grown quite big - maybe we should reveal the definition
val handshake_state_t_v_with_smi (#isc : isconfig) (#initiator : bool) (m : mem)
                                 (st : state_t isc initiator{state_t_is_handshake st})
                                 (smi : meta_info) :
  Ghost (state (isc_get_sc isc))
  (requires (isc_valid_meta_info isc smi))
  (ensures (fun st_v ->
    let step = UInt32.v (state_t_handshake_get_step st) in
    let pattern = isc_get_pattern isc in
    let rs = state_t_handshake_get_rs st in
    state_is_initiator st_v = initiator /\
    state_is_handshake st_v /\
    state_get_status st_v = step_to_status initiator step /\
    pattern == state_get_pattern st_v /\
    as_seq m (state_t_get_hash st) == state_get_hash st_v /\
    (Some? (state_get_s st_v) = smi.hsf.s) /\
    (smi.hsf.s ==>
     begin
     let spriv, spub = state_t_handshake_get_static st in
     state_get_s st_v == keys_t_or_unit_to_keypair m spriv spub
     end) /\
    (Some? (state_get_rs st_v) = smi.hsf.rs) /\ // We could link all the boolean flags, but we only need two for now
    (smi.hsf.rs ==>
     state_get_rs st_v == lbuffer_or_unit_to_opt_lseq m (state_t_handshake_get_rs st)) /\
    (Some? (state_get_psk st_v) = smi.hsf.psk) /\  // We could link all the boolean flags, but we only need two for now
    (Some? (state_get_psk st_v) ==> isc_get_psk isc)))

// TODO: this has grown quite big - maybe we should reveal the definition
val transport_state_t_v (#isc : isconfig) (#initiator : bool) (m : mem)
                        (st : state_t isc initiator{not (state_t_is_handshake st)}) :
  Ghost (state (isc_get_sc isc))
  (requires True)
  (ensures (fun st_v ->
    let pattern = isc_get_pattern isc in
    state_is_initiator st_v = initiator /\
    state_is_transport st_v /\
    pattern == state_get_pattern st_v /\
    as_seq m (state_t_get_hash st) == state_get_hash st_v /\
    state_t_get_received_transport_message st = state_received_transport_message st_v))

val handshake_state_t_frame_invariant :
     #isc:isconfig
  -> l:B.loc
  -> #initiator:bool
  -> st:state_t isc initiator{state_t_is_handshake st}
  -> smi:meta_info
  -> h0:HS.mem
  -> h1:HS.mem ->
    Lemma
  (requires (
    state_t_invariant_stateful h0 st /\
    isc_valid_meta_info isc smi /\
    B.loc_disjoint l (state_t_footprint st) /\
    B.modifies l h0 h1))
  (ensures (
    state_t_invariant_stateful h1 st /\
    handshake_state_t_v_with_smi h1 st smi ==
      handshake_state_t_v_with_smi h0 st smi))

val transport_state_t_frame_invariant :
     #isc:isconfig
  -> l:B.loc
  -> #initiator:bool
  -> st:state_t isc initiator{state_t_is_transport st}
  -> h0:HS.mem
  -> h1:HS.mem ->
    Lemma
  (requires (
    state_t_invariant_stateful h0 st /\
    B.loc_disjoint l (state_t_core_footprint st) /\
    B.modifies l h0 h1))
  (ensures (
    state_t_invariant_stateful h1 st /\
    transport_state_t_v h1 st ==
      transport_state_t_v h0 st))

(*** Create *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let create_state_smi_compute (ks : key_slots) (rsb pskb : bool) :
  meta_info =
  let hsf =
  {
    sk = false;
    s = ks_get_s ks;
    e = ks_get_e ks;
    rs = rsb && ks_get_rs ks;
    re = false;
    psk = pskb && ks_get_psk ks
  } in
  let smi = { hsf = hsf; nonce = 0 } in
  smi

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_state_smi (isc : isconfig) (rsb pskb : bool) :
  smi:meta_info{isc_valid_meta_info isc smi}

val create_state_smi_lem (isc : isconfig) (rsb pskb : bool) :
  Lemma(create_state_smi isc rsb pskb = create_state_smi_compute (isc_get_ks isc) rsb pskb)
  [SMTPat(create_state_smi isc rsb pskb)]

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let create_state_smi_pre_aux
  (pattern : handshake_pattern)
  (has_s has_rs initiator rsb : bool) : Tot bool =
  let send_pre, recv_pre = get_send_recv_premsgs pattern initiator in
  (has_s || None? send_pre) && ((has_rs && rsb) = Some? recv_pre)

// This definition MUSTN'T be revealed, because otherwise some subsequent
// lax-checkings take huge amount of time
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_state_smi_pre
  (isc:isconfig{isc_has_valid_pattern isc})
  (initiator rsb pskb : bool) : Tot bool

val create_state_smi_pre_lem
  (isc:isconfig{isc_has_valid_pattern isc})
  (initiator rsb pskb : bool) :
  Lemma (
    create_state_smi_pre isc initiator rsb pskb =
    begin
    let pattern = isc_get_pattern isc in
    let send_pre, recv_pre = get_send_recv_premsgs pattern initiator in
    let has_s = isc_get_s isc in
    let has_rs = isc_get_rs isc in
    create_state_smi_pre_aux pattern has_s has_rs initiator rsb
    end)

val create_state_smi_valid_lem (isc : isconfig{isc_has_valid_pattern isc})
                               (initiator rsb pskb : bool) :
  Lemma
  (requires (create_state_smi_pre isc initiator rsb pskb))
  (ensures (
    isc_valid_meta_info isc (create_state_smi isc rsb pskb)))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_create_state :
     #isc:isconfig{isc_has_valid_pattern isc}
  -> ssi:ss_impls (isc_get_nc isc)
  -> initialize:initialize_handshake_state_st (isc_get_nc isc)
  -> r:HS.rid
  -> initiator:bool
  -> prlg_len:hashable_size_t (isc_get_nc isc)
  -> prlg:hashable_t (isc_get_nc isc) prlg_len
  -> spriv:sprivate_key_t isc
  -> spub:spublic_key_t isc
  -> epriv:eprivate_key_t isc
  -> epub:epublic_key_t isc
  -> #rsb:bool
  -> rs:public_key_t_or_unit (isc_get_nc isc) (rsb && isc_get_rs isc)
  -> #pskb:bool
  -> psk:preshared_key_t_or_unit (pskb && isc_get_psk isc) ->
  ST (st:state_t isc initiator{state_t_is_handshake st})
  (requires (fun h0 ->
    let pattern = isc_get_pattern isc in

    ST.is_eternal_region r /\
    lbuffer_or_unit_live h0 spriv /\
    lbuffer_or_unit_live h0 spub /\
    lbuffer_or_unit_live h0 epriv /\
    lbuffer_or_unit_live h0 epub /\
    lbuffer_or_unit_live h0 rs /\
    lbuffer_or_unit_live h0 psk /\
    live h0 prlg /\

    begin
    let r_loc = region_to_loc r in
    let spriv_loc = lbuffer_or_unit_to_loc spriv in
    let spub_loc = lbuffer_or_unit_to_loc spub in
    let epriv_loc = lbuffer_or_unit_to_loc epriv in
    let epub_loc = lbuffer_or_unit_to_loc epub in
    let rs_loc = lbuffer_or_unit_to_loc rs in
    let psk_loc = lbuffer_or_unit_to_loc psk in
    let prlg_loc = (B.loc_buffer (prlg <: buffer uint8)) in
    B.all_disjoint [r_loc; spriv_loc; spub_loc; epriv_loc; epub_loc;
                    rs_loc; psk_loc; prlg_loc]
    end /\

    create_state_smi_pre isc initiator rsb pskb /\
    get_hash_pre (isc_get_nc isc)))

  (ensures (fun h0 st h1 ->
    B.(modifies loc_none h0 h1) /\
    state_t_invariant_stateful h1 st /\
    region_includes r (state_t_core_footprint st) /\
    state_t_handshake_get_static st == (spriv, spub) /\
    begin
    let s_v = mk_keypair_from_keys_or_unit h0 spriv spub in
    let e_v = mk_keypair_from_keys_or_unit h0 epriv epub in
    let prlg_v = as_seq h0 prlg in
    let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
    let psk_v = lbuffer_or_unit_to_opt_lseq h0 psk in
    match create_state (isc_get_pattern isc) prlg_v initiator s_v e_v rs_v psk_v with
    | Res st'_v ->
      let smi = create_state_smi isc rsb pskb in
      (**) create_state_smi_valid_lem isc initiator rsb pskb;
      handshake_state_t_v_with_smi h1 st smi == st'_v /\
      UInt32.v (state_t_handshake_get_step st) = 0 /\ // not necessary, but makes proofs easier
      (spriv, spub) == state_t_handshake_get_static st
    | _ -> False
    end))

(*** Free *)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_free :
     #isc:isconfig
  -> #initiator:bool
  -> st:state_t isc initiator ->
  ST unit
  (requires (fun h0 ->
    state_t_invariant_stateful h0 st))
  (ensures (fun h0 res h1 ->
    B.(modifies (state_t_core_footprint st) h0 h1)))

(*** Handshake read/write utilities *)

// JP: looking at the extracted code, max_size_t (from Lib.IntTypes) is defined
// with pow2 which doesn't reduce, hence blocking reduction of a large number of
// subterms -- use our own definition for max_size_t
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let max_size_t: s: nat { s == max_size_t } =
  assert_norm (4294967295 == max_size_t);
  4294967295

// TODO: move those utilities
// Definining the maximum possible lengths of hashes, AEADs, etc.
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let hashable_check_max (nc : iconfig) :
  s:size_nat {
    s + hash_vsv nc <= max_size_t /\
    s + hash_vsv nc <= hash_max_input (get_config nc)
  } =
  // The maximum hash lengths are greater than the maximum size of a buffer,
  // so we only need to check that it is possible to concatenate a hash
  (**) assert(max_size_t <= hash_max_input_norm (get_config nc));
  max_size_t - hash_vsv nc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let is_hashable_len (nc : iconfig) (l : size_t) :
  Pure bool (requires True)
  (ensures (fun b ->
    b = is_hashable_size (get_config nc) (size_v l))) =
  FStar.UInt32.(l <=^ size (hashable_check_max nc))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let hashable_with_tag_check_max (nc : iconfig) :
  s:size_nat {
    s + hash_vsv nc + aead_tag_size <= max_size_t /\
    s + hash_vsv nc + aead_tag_size  <= hash_max_input (get_config nc)
  } =
  // The maximum hash lengths are greater than the maximum size of a buffer,
  // so we only need to check that it is possible to concatenate a hash
  (**) assert(max_size_t <= hash_max_input_norm (get_config nc));
  max_size_t - hash_vsv nc - aead_tag_size

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let is_hashable_with_tag_len (nc : iconfig) (l : size_t) :
  Pure bool (requires True)
  (ensures (fun b ->
    b = is_hashable_size (get_config nc) (size_v l + aead_tag_size))) =
  // The maximum hash lengths are greater than the maximum size of a buffer,
  // so we only need to check that it is possible to concatenate a hash
  (**) assert(max_size_t <= hash_max_input_norm (get_config nc));
  FStar.UInt32.(l <=^ size (hashable_with_tag_check_max  nc))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let aead_check_max (nc : iconfig) :
  s:size_nat{
    s <= aead_max_input (get_config nc) /\
    s <= max_size_t - aead_tag_size
  } =
  (**) assert(aead_max_input (get_config nc) + aead_tag_size <= max_size_t);
  aead_max_input_norm (get_config nc)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let is_aead_len (nc : iconfig) (l : size_t) :
  Pure bool (requires True)
  (ensures (fun b ->
    b =
    ((size_v l <= aead_max_input (get_config nc)) &&
     (size_v l + aead_tag_size <= max_size_t)))) =
  assert(aead_max_input (get_config nc) + aead_tag_size <= max_size_t);
  FStar.UInt32.(l <=^ size (aead_check_max nc))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let min2 (x y : nat) : n:nat{n <= x /\ n <= y} =
  if x <= y then x else y

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let min3 (x y z : nat) : n:nat{n <= x /\ n <= y /\ n <= z} =
  min2 x (min2 y z)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let plain_message_check_max (nc : iconfig) :
  s:size_nat {
    forall l. l <= s ==> is_plain_message_length (get_config nc) l
  } =
  min2 (aead_check_max nc) (hashable_with_tag_check_max nc)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let is_plain_message_len (nc : iconfig) (l : size_t) :
  Pure bool (requires True)
  (ensures (fun b ->
    b = is_plain_message_length (get_config nc) (size_v l))) =
  FStar.UInt32.(l <=^ size (plain_message_check_max nc))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let check_payload_len (nc : iconfig) (l : size_t) :
  Pure bool (requires True)
  (ensures (fun b -> b = (size_v l + aead_tag_size + hash_vsv nc <= max_size_t))) =
  FStar.UInt32.(l <=^ size (max_size_t - aead_tag_size - hash_vsv nc))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let check_payload_msg_len (nc : iconfig) (smi : meta_info)
                          (is_psk : bool)
                          (pat : list message_token)
                          (payload_len msg_len : size_t) :
  Pure bool
  (requires (
    tokens_message_size (get_config nc) smi.hsf.sk is_psk pat <= max_size_t /\
    check_payload_len nc payload_len))
  (ensures (fun b ->
    b = (size_v msg_len = (message_vsv nc smi is_psk pat (size_v payload_len) <: nat)))) =
  [@inline_let] let has_sym_key = with_onorm(smi.hsf.sk) in
  [@inline_let]
  let l1 = with_onorm(tokens_message_size (get_config nc) has_sym_key is_psk pat) in
  [@inline_let]
  let has_sym_key' = with_onorm(tokens_update_sym_key_flag has_sym_key is_psk pat) in
  (**) assert(size_v payload_len + aead_tag_size <= max_size_t);
  [@inline_let]
  let l2 = if has_sym_key' then FStar.UInt32.(payload_len +^ aead_tag_vs) else payload_len in
  if FStar.UInt32.(size (max_size_t - l1) >=^ l2) then
    FStar.UInt32.(msg_len =^ size l1 +^ l2)
  else false

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let check_outlen = check_payload_msg_len

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let check_inlen = check_payload_msg_len

/// The following function replaces:
/// - is_plain_message_len
/// - check_payload_len
/// - check_outlen/check_inlen
/// by merging them. It leads to better code at extraction time.
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val check_input_output_len
  (nc : iconfig) (smi : meta_info) (is_psk : bool) (pat : list message_token)
  (payload_len msg_len : size_t) :
  Pure bool
  (requires (
    tokens_message_size (get_config nc) smi.hsf.sk is_psk pat <= max_size_t))
  (ensures (fun b ->
    b = (is_plain_message_len nc payload_len &&
         check_payload_len nc payload_len &&
         check_payload_msg_len nc smi is_psk pat payload_len msg_len)))

// Given a payload length, return the length of the next message to receive/send.
// If we are in the handshake phase, it depends on the current step.
// In transport phase, it is always payload_len + aead_tag (note that the state
// can't necessarily send/receive a message).
#push-options "--ifuel 1"
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_compute_next_message_len
  (#isc:isconfig) (#initiator:bool) (st : state_t isc initiator)
  (payload_len : size_t) (out : B.pointer size_t) :
  Stack bool
  (requires (fun h0 ->
    B.live h0 out /\
    state_t_invariant_stateful h0 st))
  (ensures (fun h0 b h1 ->
    B.(modifies (loc_buffer out) h0 h1) /\
    begin
    let nc = isc_get_config isc in
    let pat = isc_get_pattern isc in
    (**) normalize_term_spec(List.Tot.length pat.messages);
    if b then
      match st with
      | IMS_Handshake step _ _ _ _ _ _ _ _ _ _ ->
        size_v step < List.Tot.length pat.messages /\
        size_v (B.deref h1 out) =
          size_v payload_len + compute_message_length nc pat (size_v step)
      | IMS_Transport _ _ _ _ _ _ ->
        size_v (B.deref h1 out) = size_v payload_len + aead_tag_vsv
    else True
    end))
#pop-options

// Given an message length, return the length of the decrypted payload/
#push-options "--ifuel 1"
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_compute_next_decrypted_payload_length
  (#isc:isconfig) (#initiator:bool) (st : state_t isc initiator)
  (message_len : size_t) (payload_len : B.pointer size_t) :
  Stack bool
  (requires (fun h0 ->
    B.live h0 payload_len /\
    state_t_invariant_stateful h0 st))
  (ensures (fun h0 b h1 ->
    B.(modifies (loc_buffer payload_len) h0 h1) /\
    begin
    let nc = isc_get_config isc in
    let pat = isc_get_pattern isc in
    (**) normalize_term_spec(List.Tot.length pat.messages);
    if b then
      match st with
      | IMS_Handshake step _ _ _ _ _ _ _ _ _ _ ->
        size_v step < List.Tot.length pat.messages /\
        size_v (B.deref h1 payload_len) + compute_message_length nc pat (size_v step) =
          size_v message_len
      | IMS_Transport _ _ _ _ _ _ ->
        size_v (B.deref h1 payload_len) + aead_tag_vsv = size_v message_len
    else True
    end))
#pop-options

// Same as previous function, but no pointers - for internal use.
#push-options "--ifuel 1"
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_compute_next_decrypted_payload_length_option
  (#isc:isconfig) (#initiator:bool) (st : state_t isc initiator)
  (message_len : size_t) :
  Pure (option size_t)
  (requires (True))
  (ensures (fun res ->
    begin
    let nc = isc_get_config isc in
    let pat = isc_get_pattern isc in
    (**) normalize_term_spec(List.Tot.length pat.messages);
    match res with
    | Some payload_len ->
      begin match st with
      | IMS_Handshake step _ _ _ _ _ _ _ _ _ _ ->
        size_v step < List.Tot.length pat.messages /\
        size_v payload_len + compute_message_length nc pat (size_v step) =
          size_v message_len
      | IMS_Transport _ _ _ _ _ _ ->
        size_v payload_len + aead_tag_vsv = size_v message_len
      end
    | _ -> True
    end))
#pop-options

[@@ noextract_to "Kremlin"] noextract
let handshake_state_t_valid_values (#isc : isconfig)
                                   (initiator : bool) (i : nat)
                                   (st : state_t isc initiator{state_t_is_handshake st})
                                   (send : bool) : Type0 =
  i = UInt32.v (state_t_handshake_get_step st) /\
  (if send then Handshake_send? (step_to_status initiator i)
   else Handshake_receive? (step_to_status initiator i))

let state_t_handshake_shared_props (#isc : isconfig) (#initiator : bool)
                                   (st1 : state_t isc initiator{state_t_is_handshake st1})
                                   (st2 : state_t isc initiator{state_t_is_handshake st2}) : GTot Type0 =
  state_t_handshake_get_static st1 == state_t_handshake_get_static st2 /\
  state_t_core_footprint st1 == state_t_core_footprint st2

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_t_is_stuck
  (#isc : isconfig{List.Tot.length (isc_get_pattern isc).messages + 1 <= max_size_t})
  (#initiator : bool)
  (st : state_t isc initiator) : bool =
  [@inline_let] let n = List.Tot.length (isc_get_pattern isc).messages in
  [@inline_let] let state_is_handshake = state_t_is_handshake st in
  state_is_handshake && UInt32.eq (state_t_handshake_get_step st) (size (n + 1))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val state_t_set_stuck
  (#isc : isconfig{List.Tot.length (isc_get_pattern isc).messages + 1 <= max_size_t})
  (#initiator : bool)
  (st : state_t isc initiator) :
  Pure (state_t isc initiator)
  (requires True)
  (ensures (fun st1 ->
    if state_t_is_handshake st then
      state_t_is_handshake st1 /\
      state_t_handshake_shared_props st st1 /\
      state_t_core_footprint st1 == state_t_core_footprint st /\
      state_t_footprint st1 == state_t_footprint st /\
      state_t_is_stuck st1
    else st1 == st))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val state_t_set_stuck_with_invariant
  (#isc : isconfig{List.Tot.length (isc_get_pattern isc).messages + 1 <= max_size_t})
  (#initiator : bool)
  (h : mem)
  (st : state_t isc initiator) :
  Pure (state_t isc initiator)
  (requires (state_t_invariant_stateful h st))
  (ensures (fun st1 ->
    if state_t_is_handshake st then
      state_t_invariant_stateful h st1 /\
      state_t_is_handshake st1 /\
      state_t_handshake_shared_props st st1 /\
      state_t_core_footprint st1 == state_t_core_footprint st /\
      state_t_footprint st1 == state_t_footprint st /\
      state_t_is_stuck st1
    else st1 == st))

(*** Handshake write message *)

/// If we don't abstract those pre/postconditions, we later have problems because
/// F* takes a huge time to process some type definitions. In order to solve this
/// problem, we initially had abstracted [send_message_st], but it causes other
/// issues.
/// Because we need to "reveal" some definitions (by not hiding them in the .fst)
/// so that we can later post-process them, we also need to provide lemmas to
/// reveal how those pre/postconditions are actually defined.
val send_message_pre
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
    (st : valid_hsm nc smi)
    (outlen : size_t) (out : lbuffer uint8 outlen)
    (h : mem) : GTot Type0

val send_message_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
    (st : valid_send_message_hsm nc is_psk pattern smi)
    (outlen : size_t) (out : lbuffer uint8 outlen) 
    (h0 : mem) (r : rtype (send_message_return_type smi is_psk pattern)) (h1 : mem) : GTot Type0

val send_message_pre_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
  (st : valid_hsm nc smi)
  (outlen : size_t) (out : lbuffer uint8 outlen)
  (h : mem) : Lemma (
    send_message_pre #nc smi initiator is_psk pattern payload_len payload
                     st outlen out h ==
    send_message_tokens_with_payload_pre #nc smi initiator is_psk pattern payload_len payload
                                         st outlen out h)

val send_message_post_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
  (st : valid_send_message_hsm nc is_psk pattern smi)
  (outlen : size_t) (out : lbuffer uint8 outlen) 
  (h0 : mem) (r : rtype (send_message_return_type smi is_psk pattern)) (h1 : mem) :
  Lemma (
    send_message_post #nc smi initiator is_psk pattern payload_len payload
                                          st outlen out h0 r h1 ==
    send_message_tokens_with_payload_post #nc smi initiator is_psk pattern payload_len payload
                                          st outlen out h0 r h1)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let send_message_st_aux (nc : iconfig) (smi : meta_info) (initiator : bool)
                        (is_psk : bool)
                        (pattern : list message_token) :
  Type0 =
  payload_len : plain_message_len_t nc ->
  payload : plain_message_t nc payload_len ->
  st : valid_send_message_hsm nc is_psk pattern smi ->
  outlen : size_t ->
  out : lbuffer uint8 outlen ->
  Stack (rtype (send_message_return_type smi is_psk pattern))
  (requires (send_message_pre smi initiator is_psk pattern
                                            payload_len payload st outlen out))
  (ensures (send_message_post smi initiator is_psk
                                      pattern payload_len payload st outlen out))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let send_message_st (isc : isconfig) (smi : meta_info)
                    (initiator : bool)
                    (i : nat{i < List.Tot.length (isc_get_pattern isc).messages}) :
  Type0 =
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let is_psk = with_onorm (check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let] let pattern = with_onorm(isc_get_pattern isc) in
  [@inline_let] let pattern = with_onorm(List.Tot.index pattern.messages i) in
  send_message_st_aux nc smi initiator is_psk pattern

let mk_state_t_handshake_write_stateful_pre :
     #isc:isconfig
  -> #initiator:bool
  -> payload_len: size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t isc initiator{state_t_is_handshake st}
  -> outlen: size_t
  -> out: lbuffer uint8 outlen
  -> h0:mem -> GTot Type0 =
  fun #isc #initiator payload_len payload st outlen out h0 ->
  state_t_invariant_stateful h0 st /\
  live h0 payload /\
  live h0 out /\
  LB.disjoint payload out /\
  B.loc_disjoint (state_t_footprint st) (B.loc_buffer (payload <: buffer uint8)) /\
  B.loc_disjoint (state_t_footprint st) (B.loc_buffer (out <: buffer uint8))

let mk_state_t_handshake_write_smi_pre :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> GTot Type0 =
  fun #isc smi i ->
  let nc = isc_get_nc isc in
  let pattern = isc_get_pattern isc in
  let pat = List.Tot.index pattern.messages i in
  let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  let post_smi = send_message_update_smi is_psk pat smi in
  let initiator = i%2=0 in
  isc_valid_meta_info isc post_smi /\
  check_send_message_smi smi initiator is_psk pat /\
  tokens_message_size (get_config nc) smi.hsf.sk is_psk pat <= max_size_t

let mk_state_t_handshake_write_pre :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t isc (i%2=0){state_t_is_handshake st}
  -> outlen : size_t
  -> out : lbuffer uint8 outlen
  -> h0:mem -> GTot Type0 =
  fun #isc smi i payload_len payload st outlen out h0 ->

  mk_state_t_handshake_write_stateful_pre #isc #(i%2=0) payload_len payload st outlen out h0 /\
  mk_state_t_handshake_write_smi_pre #isc smi i /\

  get_aead_pre (isc_get_nc isc) /\
  get_dh_pre (isc_get_nc isc) /\
  get_hash_pre (isc_get_nc isc) /\

  handshake_state_t_valid_values (i%2=0) i st true

let mk_state_t_handshake_write_post :
     #isc:isconfig
  -> #initiator:bool
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> post_smi:meta_info{isc_valid_meta_info isc post_smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t isc initiator{state_t_is_handshake st}
  -> outlen : size_t
  -> out : lbuffer uint8 outlen
  -> h0:mem
  -> res:s_result_code (st:state_t isc initiator{state_t_is_handshake st})
  -> h1:mem ->
  Ghost Type0
  (requires (
    // We need this for check_input_output_len
    let pattern = isc_get_pattern isc in
    let tokens = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    tokens_message_size (get_config (isc_get_nc isc)) smi.hsf.sk is_psk tokens <= max_size_t))
  (ensures (fun _ -> True))
  =
  fun #isc #initiator smi post_smi i payload_len payload st outlen out h0 res h1 ->
  B.(modifies (loc_union (state_t_core_footprint st) (loc_buffer (out <: buffer uint8))) h0 h1) /\

  begin
  let pattern = isc_get_pattern isc in
  let tokens = List.Tot.index pattern.messages i in
  let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  let st0_v = handshake_state_t_v_with_smi h0 st smi in
  let payload_v = as_seq h0 payload in
  let res_v = handshake_write payload_v st0_v in
  match res with
  | Res st1 ->
    Res? res_v /\
    begin
    let Res (out'_v, st1'_v) = res_v in
    handshake_state_t_v_with_smi h1 st1 post_smi == st1'_v /\
    as_seq h1 out == out'_v /\
    state_t_handshake_shared_props st st1 /\
    state_t_invariant_stateful h1 st1
    end
  | Fail _ ->
    (check_input_output_len (isc_get_nc isc) smi is_psk tokens payload_len outlen ==> Fail? res_v) /\
    state_t_invariant_stateful h1 st
  | _ -> False // Needed because we don't have ifuel
  end

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_handshake_write :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> send_message:send_message_st isc smi (i%2=0) i
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t isc (i%2=0){state_t_is_handshake st}
  -> outlen : size_t
  -> out : lbuffer uint8 outlen ->

  Stack (s_result_code (st:state_t isc (i%2=0){state_t_is_handshake st}))
  (requires (fun h0 ->
    mk_state_t_handshake_write_pre #isc smi i
                                   payload_len payload st outlen out h0))
  (ensures (fun h0 res h1 ->
    let pattern = isc_get_pattern isc in
    let tokens = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    let post_smi = send_message_update_smi is_psk tokens smi in
    mk_state_t_handshake_write_post
      #isc smi post_smi i payload_len payload st outlen out h0 res h1))

(*** Handshake read message *)

/// See the comments for [send_message_st]

val receive_message_pre
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_outlen : plain_message_len_t nc)
  (payload_out : plain_message_t nc payload_outlen)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h : mem) : GTot Type0

val receive_message_post
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_outlen : plain_message_len_t nc)
  (payload_out : plain_message_t nc payload_outlen)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h0 : mem) (r : rtype (receive_message_return_type smi is_psk pattern))
  (h1 : mem) : GTot Type0

val receive_message_pre_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_outlen : plain_message_len_t nc)
  (payload_out : plain_message_t nc payload_outlen)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h : mem) :
  Lemma (
    receive_message_pre
      #nc smi initiator is_psk pattern payload_outlen payload_out st inlen input h ==
    receive_message_tokens_with_payload_pre
      #nc smi initiator is_psk pattern payload_outlen payload_out st inlen input h)

val receive_message_post_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_outlen : plain_message_len_t nc)
  (payload_out : plain_message_t nc payload_outlen)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h0 : mem) (r : rtype (receive_message_return_type smi is_psk pattern))
  (h1 : mem) :
  Lemma (
    receive_message_post
      #nc smi initiator is_psk pattern payload_outlen payload_out st inlen input h0 r h1 ==
    receive_message_tokens_with_payload_post
      #nc smi initiator is_psk pattern payload_outlen payload_out st inlen input h0 r h1)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let receive_message_st_aux (nc : iconfig) (smi : meta_info) (initiator : bool)
                           (is_psk : bool)
                           (tokens : list message_token) :
  Type0 =
  payload_len : plain_message_len_t nc ->
  payload : plain_message_t nc payload_len ->
  st : valid_receive_message_hsm nc is_psk tokens smi ->
  inlen : size_t ->
  input : lbuffer uint8 inlen ->
  Stack (rtype (receive_message_return_type smi is_psk tokens))
  (requires (receive_message_pre smi initiator is_psk tokens
                                     payload_len payload st inlen input))
  (ensures (receive_message_post smi initiator is_psk
                                     tokens payload_len payload st inlen input))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let receive_message_st (isc : isconfig) (smi : meta_info)
                       (i : nat{i < List.Tot.length (isc_get_pattern isc).messages}) :
  Type0 =
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let is_psk = with_onorm (check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let] let pattern = isc_get_pattern isc in
  [@inline_let] let tokens = with_onorm(List.Tot.index pattern.messages i) in
  receive_message_st_aux nc smi (i%2=1) is_psk tokens

val receive_message_tokens_nout_pre
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (st : valid_hsm nc smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h : mem) : GTot Type0

val receive_message_tokens_nout_post
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t)
  (input : lbuffer uint8 inlen)
  (h0 : mem) (r : rtype (receive_tokens_return_type smi is_psk pattern))
  (h1 : mem) : GTot Type0

val receive_message_tokens_nout_pre_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (st : valid_hsm nc smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h : mem) :
  Lemma (
    receive_message_tokens_nout_pre
      #nc smi initiator is_psk pattern st inlen input h ==
    Impl.Noise.SendReceive.receive_message_tokens_nout_pre
      #nc smi initiator is_psk pattern st inlen input h)

val receive_message_tokens_nout_post_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t)
  (input : lbuffer uint8 inlen)
  (h0 : mem) (r : rtype (receive_tokens_return_type smi is_psk pattern))
  (h1 : mem) :
  Lemma (
    receive_message_tokens_nout_post
      #nc smi initiator is_psk pattern st inlen input h0 r h1 ==
    Impl.Noise.SendReceive.receive_message_tokens_nout_post
      #nc smi initiator is_psk pattern st inlen input h0 r h1)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let receive_message_tokens_nout_st_aux (nc : iconfig) (smi : meta_info) (initiator : bool)
                                       (is_psk : bool)
                                       (tokens : list message_token) :
  Type0 =
  st : valid_receive_message_hsm nc is_psk tokens smi ->
  inlen : size_t ->
  input : lbuffer uint8 inlen ->
  Stack (rtype (receive_tokens_return_type smi is_psk tokens))
  (requires (receive_message_tokens_nout_pre smi initiator is_psk tokens
                                             st inlen input))
  (ensures (fun h0 r h1 -> receive_message_tokens_nout_post smi initiator is_psk
                                                          tokens st inlen input h0 r h1))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let receive_split_message_impls_aux
  (nc : iconfig) (smi : meta_info) (initiator : bool)
  (is_psk recv_psk : bool) (tokens_beg tokens_end : list message_token) :
  Type0 =
  [@inline_let] let smi1 = with_onorm(receive_tokens_update_smi is_psk tokens_beg smi) in
  receive_message_tokens_nout_st_aux nc smi initiator is_psk tokens_beg &
  receive_message_st_aux nc (smi_or_set_psk recv_psk smi1)
                           initiator is_psk tokens_end

/// Note that we don't request as a precondition that the list of tokens contains [S]:
/// there is no point in enforcing it now.
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let receive_split_message_impls
  (isc : isconfig) (smi : meta_info)
  (i : nat{i < List.Tot.length (isc_get_pattern isc).messages}) :
  Type0 =
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let initiator = i%2=1 in
  [@inline_let] let is_psk = with_onorm (check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let] let recv_psk = isc_lookups_psk isc in
  [@inline_let] let pattern = isc_get_pattern isc in
  [@inline_let] let tokens = with_onorm(List.Tot.index pattern.messages i) in
  // We use [fst] and [snd] to split the tokens because otherwise it is difficult
  // to use this dependent type
  [@inline_let] let tokens_beg = with_onorm(fst(splitAtFirstElem S tokens)) in
  [@inline_let] let tokens_end = with_onorm(snd(splitAtFirstElem S tokens)) in
  receive_split_message_impls_aux nc smi initiator is_psk recv_psk tokens_beg tokens_end

let mk_state_t_handshake_read_no_S_smi_pre :
     isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> GTot Type0 =
  fun isc smi i ->
  let nc = isc_get_nc isc in
  let pattern = isc_get_pattern isc in
  let pat = List.Tot.index pattern.messages i in
  let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  let post_smi = receive_message_update_smi is_psk pat smi in
  not (List.Tot.mem S pat) /\
  isc_valid_meta_info isc post_smi /\
  check_receive_message_smi smi (i%2=1) is_psk pat /\
  tokens_message_size (get_config nc) smi.hsf.sk is_psk pat <= max_size_t

let mk_state_t_handshake_read_with_S_smi_pre :
     isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> GTot Type0 =
  fun isc smi i ->
  let initiator = i%2=1 in
  let recv_psk = isc_lookups_psk isc in
  let nc = isc_get_nc isc in
  let pattern = isc_get_pattern isc in
  let tokens = List.Tot.index pattern.messages i in
  let tokens_beg, tokens_end = splitAtFirstElem S tokens in
  let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  let post_smi = smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi) in
  let smi1 = receive_tokens_update_smi is_psk tokens_beg smi in
  let smi2 = smi_or_set_psk recv_psk smi1 in

  (recv_psk ==> isc_get_psk isc) /\
  List.Tot.mem S tokens /\
  isc_valid_meta_info isc post_smi /\
  check_receive_message_smi smi initiator is_psk tokens_beg /\
  check_receive_message_smi smi2 initiator is_psk tokens_end /\
  tokens_message_size (get_config nc) smi.hsf.sk is_psk tokens <= max_size_t /\

  not smi1.hsf.psk /\
  smi1.hsf.rs

(**** No S *)

[@@ noextract_to "Kremlin"] noextract unfold
let mk_state_t_handshake_read_no_S_pre :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){state_t_is_handshake st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem -> GTot Type0 =
  fun #isc smi i vfunct vst payload_outlen payload_out st inlen input h0 ->
  let initiator = i%2=1 in
  let vst_footprint = vfunct.vst.St.footprint vst in

  vfunct.vst.St.invariant h0 vst /\
  state_t_invariant_stateful h0 st /\

  live h0 payload_out /\
  live h0 input /\

  LB.disjoint payload_out input /\
  B.loc_disjoint (state_t_footprint st) (B.loc_buffer (payload_out <: buffer uint8)) /\
  B.loc_disjoint (state_t_footprint st) (B.loc_buffer (input <: buffer uint8)) /\
  B.loc_disjoint (state_t_footprint st) vst_footprint /\
  B.loc_disjoint vst_footprint (B.loc_buffer (payload_out <: buffer uint8)) /\
  B.loc_disjoint vst_footprint (B.loc_buffer (input <: buffer uint8)) /\

  get_aead_pre (isc_get_nc isc) /\
  get_dh_pre (isc_get_nc isc) /\
  get_hash_pre (isc_get_nc isc) /\

  mk_state_t_handshake_read_no_S_smi_pre isc smi i /\

  handshake_state_t_valid_values initiator i st false

[@@ noextract_to "Kremlin"] noextract unfold
let mk_state_t_handshake_read_no_S_post :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> post_smi:meta_info{isc_valid_meta_info isc post_smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){state_t_is_handshake st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem
  -> res : s_result_code (s:state_t isc (i%2=1){state_t_is_handshake s})
  -> h1 : mem
  -> Ghost Type0
  (requires (
    // for check_input_output_len
    // We need this for check_input_output_len
    let pattern = isc_get_pattern isc in
    let tokens = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    tokens_message_size (get_config (isc_get_nc isc)) smi.hsf.sk is_psk tokens <= max_size_t))
  (ensures (fun _ -> True)) =
  fun #isc smi post_smi i vfunct vst payload_outlen payload_out st inlen input h0 res h1 ->
  
  B.(modifies (loc_union (state_t_core_footprint st)
                         (loc_buffer (payload_out <: buffer uint8))) h0 h1) /\

  // I don't understand why we need those - probably comes from the use of loc_buffer in
  // the disjointness conditions in the pre - TODO: fix that (note that the input/output
  // buffers may be NULL, so we can't just take loc_addr_of_buffer)
  live h1 payload_out /\ live h1 input /\

  (* This equality is an immediate consequence of the framing rules,
   * but we add it here for convenience *)
  vfunct.vst.St.v () h1 vst ==
    vfunct.vst.St.v () h0 vst /\

  state_t_invariant_stateful h1 st /\
  vfunct.vst.St.v () h1 vst == vfunct.vst.St.v () h0 vst /\ // Sanity check

  begin
  let pattern = isc_get_pattern isc in
  let tokens = List.Tot.index pattern.messages i in
  let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  let vst0_v = vfunct.vst.St.v () h0 vst in
  let st0_v = handshake_state_t_v_with_smi h0 st smi in
  let input_v = as_seq h0 input in
  let res_v' = handshake_read #(isc_get_sc isc) input_v st0_v vst0_v in
  begin match res with
  | Res st' ->
    Res? res_v' /\
    begin
    let Res (pinfo, payload'_v, st1'_v) = res_v' in
    handshake_state_t_v_with_smi h1 st' post_smi == st1'_v /\
    as_seq h1 payload_out == payload'_v /\
    pinfo == None /\
    state_t_invariant_stateful h1 st' /\
    state_t_handshake_shared_props st st'
    end
  | Fail _ ->
    check_input_output_len (isc_get_nc isc) smi is_psk tokens payload_outlen inlen ==>
    Fail? res_v'
  | _ -> False // Needed because we don't have ifuel
  end
  end

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_handshake_read_no_S :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> receive_message:receive_message_st isc smi i
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){state_t_is_handshake st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->

  Stack (s_result_code (s:state_t isc (i%2=1){state_t_is_handshake s}))
  (requires (fun h0 ->
    mk_state_t_handshake_read_no_S_pre
      #isc smi i vfunct vst payload_outlen payload_out st inlen input h0))

  (ensures (fun h0 res h1 ->
    let pattern = isc_get_pattern isc in
    let tokens = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    let post_smi = receive_message_update_smi is_psk tokens smi in
    mk_state_t_handshake_read_no_S_post
      #isc smi post_smi i vfunct vst payload_outlen payload_out st inlen input h0 res h1))

(**** With S *)

[@@ noextract_to "Kremlin"] noextract unfold
let mk_state_t_handshake_read_with_S_pre_stateful :
     #isc:isconfig
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){state_t_is_handshake st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem
  -> GTot Type0 =
  fun #isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 ->
  let initiator = (i%2 = 1) in
  let recv_psk = isc_lookups_psk isc in

  state_t_invariant_stateful h0 st /\
  vfunct.vst.St.invariant h0 vst /\
  (isc_get_pinfo isc).St.invariant h0 pinfo /\

  live h0 payload_out /\
  live h0 input /\

  begin
  let payload_out_loc = B.loc_buffer (payload_out <: buffer uint8) in
  let input_loc = B.loc_buffer (input <: buffer uint8) in
  let vst_footprint = vfunct.vst.St.footprint vst in
  let st_loc = state_t_footprint st in
  let pinfo_loc = (isc_get_pinfo isc).St.footprint pinfo in
  B.all_disjoint [payload_out_loc; input_loc; vst_footprint; st_loc; pinfo_loc]
  end /\

  get_aead_pre (isc_get_nc isc) /\
  get_dh_pre (isc_get_nc isc) /\
  get_hash_pre (isc_get_nc isc)

[@@ noextract_to "Kremlin"] noextract unfold
let mk_state_t_handshake_read_with_S_pre :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){state_t_is_handshake st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem
  -> GTot Type0 =
  fun #isc smi i vfunct vst pinfo payload_outlen payload_out st inlen input h0 ->
  let initiator = (i%2 = 1) in
  mk_state_t_handshake_read_with_S_pre_stateful
    #isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 /\
  mk_state_t_handshake_read_with_S_smi_pre isc smi i /\
  handshake_state_t_valid_values initiator i st false

[@@ noextract_to "Kremlin"] noextract unfold
let mk_state_t_handshake_read_with_S_post :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> post_smi:meta_info{isc_valid_meta_info isc post_smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){state_t_is_handshake st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem
  -> res : s_result_code (s:state_t isc (i%2=1){state_t_is_handshake s})
  -> h1 : mem
  -> Ghost Type0
  (requires (
    // For check_input_output_lem
    // We need this for check_input_output_len
    let pattern = isc_get_pattern isc in
    let tokens = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    tokens_message_size (get_config (isc_get_nc isc)) smi.hsf.sk is_psk tokens <= max_size_t))
  (ensures (fun _ -> True)) =
  fun #isc smi post_smi i vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1 ->
  B.(modifies (loc_union (state_t_core_footprint st)
              (loc_union (loc_buffer (payload_out <: buffer uint8))
                         ((isc_get_pinfo isc).St.footprint pinfo))) h0 h1) /\

  // TODO: see comment in mk_state_t_handshake_read_no_S_post
  live h1 payload_out /\ live h1 input /\

  vfunct.vst.St.invariant h1 vst /\
  (isc_get_pinfo isc).St.invariant h1 pinfo /\

  ((isc_get_pinfo isc).St.freeable h0 pinfo ==>
   (isc_get_pinfo isc).St.freeable h1 pinfo) /\

  state_t_invariant_stateful h1 st /\
  vfunct.vst.St.v () h1 vst == vfunct.vst.St.v () h0 vst /\ // sanity check

  begin
  let recv_psk = isc_lookups_psk isc in
  let pattern = isc_get_pattern isc in
  let tokens = List.Tot.index pattern.messages i in
  let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  let vst0_v = vfunct.vst.St.v () h0 vst in
  let st0_v = handshake_state_t_v_with_smi h0 st smi in
  let input_v = as_seq h0 input in
  let res_v' = handshake_read #(isc_get_sc isc) input_v st0_v vst0_v in

  begin match res with
  | Res st' ->
    Res? res_v' /\
    begin
    let Res (pinfo_v, payload'_v, st1'_v) = res_v' in
    handshake_state_t_v_with_smi h1 st' post_smi == st1'_v /\
    as_seq h1 payload_out == payload'_v /\
    Some ((isc_get_pinfo isc).St.v () h1 pinfo) == pinfo_v /\
    state_t_invariant_stateful h1 st' /\
    state_t_handshake_shared_props st st'
    end
  | Fail _ ->
    check_input_output_len (isc_get_nc isc) smi is_psk tokens payload_outlen inlen ==>
    Fail? res_v'
  | _ -> False // Needed because we don't have ifuel
  end
  end

// Note that this function is ST and not Stack because the pinfo copy may
// be stateful.
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_handshake_read_with_S :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> impls:receive_split_message_impls isc smi i
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){state_t_is_handshake st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->
  ST (s_result_code (s:state_t isc (i%2=1){state_t_is_handshake s}))
  (requires (fun h0 ->
    mk_state_t_handshake_read_with_S_pre
      #isc smi i vfunct vst pinfo payload_outlen payload_out st inlen input h0))
  (ensures (fun h0 res h1 ->
    let recv_psk = isc_lookups_psk isc in
    let pattern = isc_get_pattern isc in
    let tokens = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    let post_smi = smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi) in
    mk_state_t_handshake_read_with_S_post
      #isc smi post_smi i vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1))

(*** Split *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_split :
     #isc:isconfig
  -> #initiator:bool
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> split:split_st (isc_get_nc isc)
  -> r:HS.rid
  -> st:state_t isc initiator{state_t_is_handshake st} ->
  ST (st:state_t isc initiator{not (state_t_is_handshake st)})
  (requires (fun h0 ->
    ST.is_eternal_region r /\

    state_t_invariant_stateful h0 st /\
    B.loc_disjoint (region_to_loc r) (state_t_core_footprint st) /\
    
    get_hash_pre (isc_get_nc isc) /\
    
    begin
    let step = state_t_handshake_get_step st in
    UInt32.v step = List.Tot.length (isc_get_pattern isc).messages /\
    isc_get_send isc = Spec.can_send initiator (isc_get_pattern isc) /\
    isc_get_receive isc = Spec.can_receive initiator (isc_get_pattern isc)
    end))

  (ensures (fun h0 st' h1 ->
    B.(modifies (state_t_core_footprint st) h0 h1) /\
    state_t_invariant_stateful h1 st' /\
    begin
    let st0_v = handshake_state_t_v_with_smi h0 st smi in
    let st1_v = transport_state_t_v h1 st' in
    match Spec.split st0_v with
    | Res st1'_v ->
      st1_v == st1'_v /\
      B.loc_includes (B.loc_union (region_to_loc r) (state_t_core_footprint st))
                     (state_t_footprint st')
    | _ -> False
    end))

(*** Transport *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_transport_write :
     #isc:isconfig
  -> #initiator:bool
  -> encrypt : iaead_encrypt_type (isc_get_nc isc)
  -> plen : size_t
  -> p : lbuffer uint8 plen
  -> clen : size_t
  -> c : lbuffer uint8 clen
  -> st:state_t isc initiator{not (state_t_is_handshake st)} ->
  Stack (s_result_code (st:state_t isc initiator{not (state_t_is_handshake st)}))
  (requires (fun h0 ->
    state_t_invariant_stateful h0 st /\

    live h0 p /\ live h0 c /\
  
    B.loc_disjoint (state_t_footprint st) (B.loc_buffer (p <: buffer uint8)) /\
    B.loc_disjoint (state_t_footprint st) (B.loc_buffer (c <: buffer uint8)) /\
    B.loc_disjoint (B.loc_buffer (p <: buffer uint8))
                   (B.loc_buffer (c <: buffer uint8)) /\
    get_aead_pre (isc_get_nc isc) /\
    isc_get_send isc))

  (ensures (fun h0 res h1 ->
    B.(modifies (B.loc_buffer (c <: buffer uint8)) h0 h1) /\
    state_t_invariant_stateful h1 st /\
    begin
    let st0_v = transport_state_t_v h0 st in
    let p_v = as_seq h0 p in
    match res, Spec.transport_write st0_v p_v with
    | Res st', Res (c_v, st1_v) ->
      transport_state_t_v h1 st' == st1_v /\
      state_t_invariant_stateful h1 st' /\
      as_seq h1 c == c_v /\
      state_t_footprint st' == state_t_footprint st
    | Fail _, r ->
      // Note that following the modifies clause, the state is left unchanged.
      (size_v clen = size_v plen + aead_tag_size ==> Fail? r)
    | _ -> False
    end))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_state_t_transport_read :
     #isc:isconfig
  -> #initiator:bool
  -> decrypt : iaead_decrypt_type (isc_get_nc isc)
  -> plen : size_t
  -> p : lbuffer uint8 plen
  -> clen : size_t
  -> c : lbuffer uint8 clen
  -> st:state_t isc initiator{not (state_t_is_handshake st)} ->
  Stack (s_result_code (st:state_t isc initiator{not (state_t_is_handshake st)}))
  (requires (fun h0 ->
    state_t_invariant_stateful h0 st /\

    live h0 p /\ live h0 c /\
  
    B.loc_disjoint (state_t_footprint st) (B.loc_buffer (p <: buffer uint8)) /\
    B.loc_disjoint (state_t_footprint st) (B.loc_buffer (c <: buffer uint8)) /\
    B.loc_disjoint (B.loc_buffer (p <: buffer uint8))
                   (B.loc_buffer (c <: buffer uint8)) /\
    get_aead_pre (isc_get_nc isc) /\
    isc_get_receive isc))

  (ensures (fun h0 res h1 ->
    B.(modifies (B.loc_buffer (p <: buffer uint8)) h0 h1) /\
    state_t_invariant_stateful h1 st /\
    begin
    let st0_v = transport_state_t_v h0 st in
    let c_v = as_seq h0 c in
    match res, Spec.transport_read st0_v c_v with
    | Res st', Res (p_v, st1_v) ->
      transport_state_t_v h1 st' == st1_v /\
      as_seq h1 p == p_v /\
      state_t_invariant_stateful h1 st' /\
      state_t_footprint st' == state_t_footprint st
    | Fail _, r ->
      // Note that following the modifies clause, the state is left unchanged.
      (size_v clen = size_v plen + aead_tag_size ==> Fail? r)
    | _ -> False
    end))
