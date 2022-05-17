module Impl.Noise.API.State.StateMachine

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

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module G = FStar.Ghost

open Spec.Noise.API
open Spec.Noise.API.State.Definitions
open Spec.Noise.API.State.Lemmas
module Spec = Spec.Noise.API.State

open Impl.Noise.Types
open Impl.Noise.HandshakeState
open Impl.Noise.SendReceive
open Impl.Noise.RecursiveMessages
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate
open Impl.Noise.API.State.Base
open Spec.Noise
open Spec.Noise.API.MetaInfo

open Meta.Noise

module St = Impl.Noise.Stateful

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** Valid handshake patterns *)
/// We need additional conditions on the handshake patterns for them to be
/// implementable in a state machine.

/// Note that we implement the verification in a very inefficient manner. It is
/// ok because we only need to check every pattern once, and the induced compilation
/// time is not an issue so far.
/// As of now, the only good reason I see to make this simpler and nicer would be
/// to minimize the conditions we require for the patterns, if we want to apply
/// our extraction mechanism to all the valid patterns we can list, and we want to
/// make sure we don't miss meaningful ones.
[@@ noextract_to "krml"] inline_for_extraction noextract
let check_pattern_messagei (hsk : handshake_pattern)
                           (is_psk : bool)
                           (init_lookups_psk resp_lookups_psk : bool)
                           (init_ks resp_ks : key_slots)
                           (i : nat{i < List.Tot.length hsk.messages}) :
  Tot bool =
  let ir = i%2=0 in
  let msg = List.Tot.index hsk.messages i in
  let has_s = List.Tot.mem S msg in
  let recv_lookups_psk = if ir then resp_lookups_psk else init_lookups_psk in
  let send_ks, recv_ks = if ir then init_ks, resp_ks else resp_ks, init_ks in
  let send_smi = step_to_smi hsk ir i in
  let recv_smi = step_to_smi hsk (not ir) i in
  let send_post_smi = send_message_update_smi is_psk msg send_smi in
  let recv_post_smi =
    smi_or_set_psk (recv_lookups_psk && has_s) (receive_message_update_smi is_psk msg recv_smi) in
  (* Valid key slots *)
  let b1 = ks_valid_meta_info send_ks send_smi && ks_valid_meta_info send_ks send_post_smi in
  let b2 = ks_valid_meta_info recv_ks recv_smi && ks_valid_meta_info recv_ks recv_post_smi in
  (* Valid meta-infos for send/receive *)
  let b3 = check_send_message_smi send_smi ir is_psk msg in
  let b4 =
    if has_s then
      let tokens_beg, tokens_end = splitAtFirstElem S msg in
      let smi1 = receive_tokens_update_smi is_psk tokens_beg recv_smi in
      let smi2 = smi_or_set_psk recv_lookups_psk smi1 in
      check_receive_message_smi recv_smi (not ir) is_psk tokens_beg &&
      check_receive_message_smi smi2 (not ir) is_psk tokens_end &&
      (not smi1.hsf.psk) &&
      (smi1.hsf.rs)
    else check_receive_message_smi recv_smi (not ir) is_psk msg
  in
  (* Updated smis are consistent *)
  let b5 = send_post_smi = step_to_smi hsk ir (i+1) in
  let b6 = recv_post_smi = step_to_smi hsk (not ir) (i+1) in
  (* Message lengths *)
  let b7 = max_tokens_message_size send_smi.hsf.sk is_psk msg <= max_size_t in
  let b8 = max_tokens_message_size recv_smi.hsf.sk is_psk msg <= max_size_t in
  // This condition is not strictly necessary, but makes out life easier in
  // Impl.Noise.API.Session, because we don't need to check whether
  // the output is NULL or not when allocating buffers.
  let b9 = compute_min_message_length hsk i > 0 in
  (* If there is S and is_psk is true, then we lookup a psk *)
  let b10 = not (has_s && is_psk) || recv_lookups_psk in
  (* Remote static key update - used for the peer information - not used in this file *)
  let b11 = send_post_smi.hsf.rs = send_smi.hsf.rs in
  let b12 =
    if has_s then (not (knows_remote hsk (not ir) i)) && (knows_remote hsk (not ir) (i+1)) else
    recv_post_smi.hsf.rs = recv_smi.hsf.rs
  in
  b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8 && b9 && b10 && b11 && b12

[@@ noextract_to "krml"] inline_for_extraction noextract
let rec check_pattern_aux
  (hsk : handshake_pattern)
  (is_psk : bool)
  (init_lookups_psk resp_lookups_psk : bool)
  (init_ks resp_ks : key_slots)
  (l : nat{l = List.Tot.length hsk.messages})
  (i : nat{i <= List.Tot.length hsk.messages}) :
  Tot bool (decreases (l - i)) =
  if i < l then
    check_pattern_messagei hsk is_psk init_lookups_psk resp_lookups_psk init_ks resp_ks i
    && check_pattern_aux hsk is_psk init_lookups_psk resp_lookups_psk init_ks resp_ks l (i+1)
  else true

/// The remote static and the psk must be loaded together, at the same time.
/// In particular, if both are used, if one is loaded at initialization time,
/// the other must be loaded at initialization time.
[@@ noextract_to "krml"] noextract
let rs_and_psk_loaded_together (hsk : handshake_pattern) (initiator : bool) =
  let ks = key_slots_from_pattern initiator hsk in
  let knows_rs = knows_rs_at_init hsk initiator in
  let knows_psk = knows_psk_at_init hsk initiator in
  not (knows_rs && ks.ks_psk) || knows_psk &&
  not (knows_psk && ks.ks_rs) || knows_rs

[@@ (strict_on_arguments [0]); noextract_to "krml"]
inline_for_extraction noextract
let check_pattern (hsk : handshake_pattern) =
  let is_psk = check_hsk_is_psk hsk in
  let init_lookups_psk = lookups_psk hsk true in
  let resp_lookups_psk = lookups_psk hsk false in
  let init_ks = key_slots_from_pattern true hsk in
  let resp_ks = key_slots_from_pattern false hsk in
  let init_knows_rs = knows_remote_at_init hsk true in // at initialization
  let resp_knows_rs = knows_remote_at_init hsk false in // at initialization
  let init_knows_psk = knows_psk_at_init hsk true in // at initialization
  let resp_knows_psk = knows_psk_at_init hsk false in // at initialization
  let l = List.Tot.length hsk.messages in
  check_pattern_aux hsk is_psk init_lookups_psk resp_lookups_psk init_ks resp_ks l 0 &&
  (* Additional conditions *)
  // The different ways of computing [is_psk] are compatible
  is_psk = init_ks.ks_psk && is_psk = resp_ks.ks_psk &&
  // smi precondition for state creation
  create_state_smi_pre_aux hsk init_ks.ks_s init_ks.ks_rs true init_knows_rs &&
  create_state_smi_pre_aux hsk resp_ks.ks_s resp_ks.ks_rs false resp_knows_rs &&
  // Initialization
  create_state_smi_compute init_ks init_knows_rs init_knows_psk = step_to_smi hsk true 0 && // not used in this file
  create_state_smi_compute resp_ks resp_knows_rs resp_knows_psk = step_to_smi hsk false 0 && // not used in this file
  // Load time
  rs_and_psk_loaded_together hsk true && // not used in this file
  rs_and_psk_loaded_together hsk false // not used in this file

/// Sanity check
[@@ noextract_to "krml"] inline_for_extraction noextract
let all_patterns_are_validb = List.Tot.for_all check_pattern Spec.Noise.Patterns.supported_patterns
[@@ noextract_to "krml"] inline_for_extraction noextract
let invalid_patterns = List.Tot.filter (fun (x : wf_handshake_pattern) -> not (check_pattern x)) Spec.Noise.Patterns.supported_patterns
[@@ noextract_to "krml"] inline_for_extraction noextract
let all_patterns_are_valid = check_bool all_patterns_are_validb

val check_pattern_aux_i_lem (hsk : handshake_pattern) (i : nat{i <= List.Tot.length hsk.messages}) :
  Lemma
  (requires (check_pattern hsk))
  (ensures (
    let is_psk = check_hsk_is_psk hsk in
    let init_lookups_psk = lookups_psk hsk true in
    let resp_lookups_psk = lookups_psk hsk false in
    let init_ks = key_slots_from_pattern true hsk in
    let resp_ks = key_slots_from_pattern false hsk in
    let l = List.Tot.length hsk.messages in
    check_pattern_aux hsk is_psk init_lookups_psk resp_lookups_psk init_ks resp_ks l i))
  (decreases i)

#push-options "--fuel 1"
let rec check_pattern_aux_i_lem hsk i =
  let l = List.Tot.length hsk.messages in
  if i = 0 then ()
  else if i >= l then ()
  else check_pattern_aux_i_lem hsk (i-1)
#pop-options

val check_pattern_messagei_lem (hsk : handshake_pattern) (i : nat{i < List.Tot.length hsk.messages}) :
  Lemma
  (requires (check_pattern hsk))
  (ensures (
    let is_psk = check_hsk_is_psk hsk in
    let init_lookups_psk = lookups_psk hsk true in
    let resp_lookups_psk = lookups_psk hsk false in
    let init_ks = key_slots_from_pattern true hsk in
    let resp_ks = key_slots_from_pattern false hsk in
    check_pattern_messagei hsk is_psk init_lookups_psk resp_lookups_psk init_ks resp_ks i))

#push-options "--fuel 1"
let check_pattern_messagei_lem hsk i =
  check_pattern_aux_i_lem hsk i
#pop-options

(*** Utilities *)

let state_t_handshake_invariant
  (#isc : isconfig) (#initiator : bool) (m : mem) (st : state_t isc initiator{state_t_is_handshake st}) :
  GTot Type0 =
  state_t_invariant_stateful m st

let state_t_transport_invariant
  (#isc : isconfig) (#initiator : bool) (m : mem) (st : state_t isc initiator{state_t_is_transport st}) :
  GTot Type0 =
  state_t_invariant_stateful m st

let state_t_invariant (#isc : isconfig) (#initiator : bool) (m : mem) (st : state_t isc initiator) : GTot Type0 =
  if state_t_is_handshake st then state_t_handshake_invariant m st
  else state_t_transport_invariant m st

let isc_is_valid_compute (initiator : bool) (isc : isconfig) : GTot bool =
  let pattern = isc_get_pattern isc in
  let is_psk = check_hsk_is_psk pattern in
  isc_get_ks isc = key_slots_from_pattern initiator pattern &&
  (* There is a subtelty here:
   * - [lookups_psk] controls whether the peer has to lookup the psk during the handshake
   * - [isc_lookups_psk] controls the signature of the validation function (if true, then it must provide a psk)
   * The problem is that we use the same validation function for the initiator and
   * the responder, while it is possible that only one of them has to lookup a PSK
   * DURING the handshake. We thus write the realation between [lookups_psk]
   * and [isc_lookups_psk] as an implication.
   * *)
  (not (isc_lookups_psk isc) || is_psk) && // if the validation function looks up a PSK, we must be a PSK pattern
  (not (lookups_psk pattern initiator) || isc_lookups_psk isc) &&
  handshake_pattern_is_valid pattern && // Comes from Impl.Noise.API.State.Base
  check_pattern pattern // Additional conditions introduced in this file

// If we don't control the unfolding, type inferencing goes wild because
// of the normalizer and definitions like [send_message_impls_aux] take half an hour
// to lax check, if your computer's memory doesn't explode before.
[@@ (strict_on_arguments [0; 1]); noextract_to "krml"]
inline_for_extraction noextract
let isc_is_valid (initiator : bool) (isc : isconfig) : GTot (b:bool{b==isc_is_valid_compute initiator isc}) =
  isc_is_valid_compute initiator isc

[@@ noextract_to "krml"] inline_for_extraction noextract
type valid_isc (initiator : bool) = isc:isconfig{isc_is_valid initiator isc}

[@@ noextract_to "krml"] inline_for_extraction noextract
let isc_step_to_smi_aux (initiator : bool)
                        (isc : isconfig)
                        (step :nat{step <= List.Tot.length (isc_get_pattern isc).messages}) :
  meta_info =
  with_onorm(step_to_smi (isc_get_pattern isc) initiator step)

val check_pattern_valid_meta_info_lem
  (initiator : bool)
  (isc : valid_isc initiator)
  (i : nat{i < List.Tot.length (isc_get_pattern isc).messages}) :
  Lemma(
    let smi = isc_step_to_smi_aux initiator isc i in
    let post_smi = isc_step_to_smi_aux initiator isc (i+1) in
    isc_valid_meta_info isc smi /\
    isc_valid_meta_info isc post_smi)

let check_pattern_valid_meta_info_lem initiator isc i =
  let hsk = isc_get_pattern isc in
  let smi = isc_step_to_smi_aux initiator isc i in
  let post_smi = isc_step_to_smi_aux initiator isc (i+1) in
  check_pattern_messagei_lem hsk i;
  isc_valid_meta_info_lem isc smi;
  isc_valid_meta_info_lem isc post_smi

[@@ (strict_on_arguments [1; 2]); noextract_to "krml"]
inline_for_extraction noextract
let isc_step_to_smi (#initiator : bool)
                    (isc : valid_isc initiator)
                    (step :nat{step <= List.Tot.length (isc_get_pattern isc).messages}) :
  smi:meta_info{isc_valid_meta_info isc smi} =
  [@inline_let] let smi = with_onorm(step_to_smi (isc_get_pattern isc) initiator step) in
  begin
  (**) if step < List.Tot.length (isc_get_pattern isc).messages then
  (**) check_pattern_messagei_lem (isc_get_pattern isc) step
  (**) else if step > 0 then check_pattern_messagei_lem (isc_get_pattern isc) (step - 1)
  (**) else ();
  (**) isc_valid_meta_info_lem isc smi
  end;
  smi

[@@ noextract_to "krml"] inline_for_extraction noextract
let get_proper_isc (initiator:bool) (init_isc : valid_isc true) (resp_isc : valid_isc false) :
  valid_isc initiator =
  if initiator then init_isc else resp_isc

[@@ noextract_to "krml"] inline_for_extraction noextract
let get_send_isc (i:nat) (init_isc : valid_isc true) (resp_isc : valid_isc false) :
  valid_isc (i%2=0) =
  if i%2=0 then init_isc else resp_isc

[@@ noextract_to "krml"] inline_for_extraction noextract
let get_receive_isc (i:nat) (init_isc : valid_isc true) (resp_isc : valid_isc false) :
  valid_isc (i%2=1) =
  if i%2=0 then resp_isc else init_isc

[@@ noextract_to "krml"] inline_for_extraction noextract
type valid_init_isc = valid_isc true

let resp_isc_is_valid (init_isc : valid_isc true) (resp_isc : valid_isc false) : GTot Type0 =
  isc_get_pattern init_isc == isc_get_pattern resp_isc /\
  isc_get_nc init_isc == isc_get_nc resp_isc /\
  isc_get_pinfo init_isc == isc_get_pinfo resp_isc

[@@ noextract_to "krml"] inline_for_extraction noextract
type valid_resp_isc (init_isc : valid_isc true) =
  resp_isc:valid_isc false{resp_isc_is_valid init_isc resp_isc}

/// Implementations storage.
/// We could do smarter/more precise types, but those are meta structures which
/// will only be manipulated only in F* and will disappear at extraction time:
/// we thus do something simple and handy.

[@@ noextract_to "krml"] inline_for_extraction noextract
let send_messagei_impl
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}) :
  Type0 =
  [@inline_let] let initiator = i%2 = 0 in
  [@inline_let] let smi = with_onorm(step_to_smi (isc_get_pattern init_isc) initiator i) in
  [@inline_let] let isc = get_send_isc i init_isc resp_isc in
  send_message_st isc smi initiator i

[@@ noextract_to "krml"] inline_for_extraction noextract
noeq type send_message_impls_aux
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc) :
  i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages} -> Type0 =
| Send_message_last :
  i:nat{i = List.Tot.length (isc_get_pattern init_isc).messages - 1} ->
  send:send_messagei_impl init_isc resp_isc i ->
  send_message_impls_aux init_isc resp_isc i
| Send_message_i :
  i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages - 1} ->
  send:send_messagei_impl init_isc resp_isc i ->
  sendl:send_message_impls_aux init_isc resp_isc (i+1) ->
  send_message_impls_aux init_isc resp_isc i

[@@ noextract_to "krml"] inline_for_extraction noextract
let receive_no_split_messagei_impl
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}) : Type0 =
  [@inline_let] let initiator = i%2 = 1 in
  [@inline_let] let smi = with_onorm(step_to_smi (isc_get_pattern init_isc) initiator i) in
  [@inline_let] let isc = get_receive_isc i init_isc resp_isc in
  receive_message_st isc smi i

[@@ noextract_to "krml"] inline_for_extraction noextract
let receive_split_messagei_impls
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}) : Type0 =
  [@inline_let] let initiator = i%2 = 1 in
  [@inline_let] let smi = with_onorm(step_to_smi (isc_get_pattern init_isc) initiator i) in
  [@inline_let] let isc = get_receive_isc i init_isc resp_isc in
  receive_split_message_impls isc smi i

/// This definition takes a long time to be checked by F*. It previously took
/// a huge time (spent in F*, not Z3) but we made it bearable by abstracting
/// the pre/postconditions for [receive_message_st] and [receive_message_tokens_nout_st]
[@@ noextract_to "krml"] inline_for_extraction noextract
noeq type receive_messagei_impl
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc) :
  i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages} -> Type0 =
| One_shot_receive :
  i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages &&
       not (List.Tot.mem S (get_message (isc_get_pattern init_isc) i))} ->
  receive:receive_no_split_messagei_impl init_isc resp_isc i ->
  receive_messagei_impl init_isc resp_isc i
| Split_receive :
  i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages &&
       List.Tot.mem S (get_message (isc_get_pattern init_isc) i)} ->
  receive:receive_split_messagei_impls init_isc resp_isc i ->
  receive_messagei_impl init_isc resp_isc i

[@@ noextract_to "krml"] inline_for_extraction noextract
noeq type receive_message_impls_aux
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc) :
  i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages} -> Type0 =
| Receive_message_last :
  i:nat{i = List.Tot.length (isc_get_pattern init_isc).messages - 1} ->
  receive:receive_messagei_impl init_isc resp_isc i ->
  receive_message_impls_aux init_isc resp_isc i
| Receive_message_i :
  i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages - 1} ->
  receive:receive_messagei_impl init_isc resp_isc i ->
  receivel:receive_message_impls_aux init_isc resp_isc (i+1) ->
  receive_message_impls_aux init_isc resp_isc i

#push-options "--fuel 1 --ifuel 1"
[@@ noextract_to "krml"] inline_for_extraction noextract
type receive_message_impls
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc) : Type0 =
  receive_message_impls_aux init_isc resp_isc 0

[@@ noextract_to "krml"] inline_for_extraction noextract
type send_message_impls
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc) : Type0 =
  send_message_impls_aux init_isc resp_isc 0
#pop-options

/// First, we define the "low-level" helpers. When declaring them, we have to
/// post-process them so that:
/// - all the meta parameters are normalized
/// - the function bodies get flattened to remove recursion
[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_send_messagei_impl (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
                          (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
                          (resp_isc : valid_resp_isc init_isc)
                          (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages})
                          (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  send_messagei_impl init_isc resp_isc i

let mk_send_messagei_impl pattern init_isc resp_isc i ssdhi =
  fun payload_len payload st outlen out ->
  [@inline_let] let nc = isc_get_nc init_isc in
  [@inline_let] let initiator = i%2=0 in
  [@inline_let] let send_isc = get_send_isc i init_isc resp_isc in
  [@inline_let] let smi = with_onorm(isc_step_to_smi #initiator send_isc i) in
  [@inline_let] let is_psk = with_onorm(check_hsk_is_psk pattern) in
  [@inline_let] let tokens = with_onorm(get_message pattern i) in
  (**) let h0 = ST.get () in
  (**) send_message_pre_lem #nc smi initiator is_psk tokens
  (**)   payload_len payload st outlen out h0;
  let r =
// TODO: uncomment once the normalizer works
//  with_onorm [zeta_full; primops; iota; delta_only [`%send_message_tokens_m]]
  (send_message_tokens_with_payload_m
     (ssdhi_get_ssi ssdhi) (send_message_tokens_m (send_message_token_m ssdhi))
     smi initiator is_psk
     // tokens: TODO: reinsert [tokens] once the normalizer works
     (with_norm(get_message pattern i))
     payload_len payload st outlen out) in
  (**) let h1 = ST.get () in
  (**) send_message_post_lem #nc smi initiator is_psk tokens payload_len payload
  (**)   st outlen out h0 (convert_type r) h1;
  convert_type r

[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_receive_no_split_messagei_impl
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages})
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  receive_no_split_messagei_impl init_isc resp_isc i

let mk_receive_no_split_messagei_impl pattern init_isc resp_isc i ssdhi =
  fun payload_len payload st inlen input ->
  [@inline_let] let nc = isc_get_nc init_isc in
  [@inline_let] let initiator = i%2=1 in
  [@inline_let] let recv_isc = get_receive_isc i init_isc resp_isc in
  [@inline_let] let smi = with_onorm(isc_step_to_smi #initiator recv_isc i) in
  [@inline_let] let is_psk = with_onorm(check_hsk_is_psk pattern) in
  [@inline_let] let tokens = with_onorm(get_message pattern i) in
  (**) let h0 = ST.get () in
  (**) receive_message_pre_lem #nc smi initiator is_psk tokens
  (**)   payload_len payload st inlen input h0;
  let r =
// TODO: uncomment once the normalizer works
//  with_onorm [zeta_full; primops; iota; delta_only [`%receive_message_tokens_nout_m]]
  (receive_message_tokens_with_payload_m
     (receive_message_tokens_nout_with_payload_m
       (ssdhi_get_ssi ssdhi)
       (receive_message_tokens_nout_m (receive_message_token_m ssdhi)))
     smi initiator is_psk
     // tokens: TODO: remove once we remove post-processing
     (with_norm (get_message pattern i))
     payload_len payload st inlen input) in
  (**) let h1 = ST.get () in
  (**) receive_message_post_lem #nc smi initiator is_psk tokens payload_len payload
  (**)   st inlen input h0 (convert_type r) h1;
  convert_type r

/// Unfortunately, we need to duplicate a lot of things to split the type
/// receive_split_messagei_impls_ty so that we can define the two function
/// implementations separately.

[@@ noextract_to "krml"] inline_for_extraction noextract
let receive_split_messagei_beg_impl
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}) :
  Type0 =
  [@inline_let] let initiator = i%2 = 1 in
  [@inline_let] let smi = with_onorm(step_to_smi (isc_get_pattern init_isc) initiator i) in
  [@inline_let] let isc = get_receive_isc i init_isc resp_isc in
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let is_psk = with_onorm (check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let] let recv_psk = with_onorm(isc_lookups_psk isc) in
  [@inline_let] let pattern = with_onorm(isc_get_pattern isc) in
  [@inline_let] let tokens = with_onorm(List.Tot.index pattern.messages i) in
  [@inline_let] let tokens_beg = with_onorm(fst(splitAtFirstElem S tokens)) in
  [@inline_let] let tokens_end = with_onorm(snd(splitAtFirstElem S tokens)) in
  receive_message_tokens_nout_st_aux nc smi initiator is_psk tokens_beg

[@@ noextract_to "krml"] inline_for_extraction noextract
let receive_split_messagei_end_impl
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}) :
  Type0 =
  [@inline_let] let initiator = i%2 = 1 in
  [@inline_let] let smi = with_onorm(step_to_smi (isc_get_pattern init_isc) initiator i) in
  [@inline_let] let isc = get_receive_isc i init_isc resp_isc in
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let is_psk = with_onorm (check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let] let recv_psk = with_onorm(isc_lookups_psk isc) in
  [@inline_let] let pattern = with_onorm(isc_get_pattern isc) in
  [@inline_let] let tokens = with_onorm(List.Tot.index pattern.messages i) in
  [@inline_let] let tokens_beg = with_onorm(fst(splitAtFirstElem S tokens)) in
  [@inline_let] let tokens_end = with_onorm(snd(splitAtFirstElem S tokens)) in
  [@inline_let] let smi = with_onorm(smi_or_set_psk recv_psk (receive_tokens_update_smi is_psk tokens_beg smi)) in
  receive_message_st_aux nc smi initiator is_psk tokens_end

/// Sanity check
let receive_split_messagei_impls_consist_lem
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}) :
  Lemma (
    receive_split_messagei_impls init_isc resp_isc i ==
    (receive_split_messagei_beg_impl init_isc resp_isc i &
     receive_split_messagei_end_impl init_isc resp_isc i)) = ()

[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_receive_split_messagei_beg_impl
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages})
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  receive_split_messagei_beg_impl init_isc resp_isc i

let mk_receive_split_messagei_beg_impl pattern init_isc resp_isc i ssdhi =
  fun st inlen input ->
  [@inline_let] let initiator = i%2 = 1 in
  [@inline_let] let smi = with_onorm(isc_step_to_smi #initiator (get_receive_isc i init_isc resp_isc) i) in
  [@inline_let] let isc = get_receive_isc i init_isc resp_isc in
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let is_psk = with_onorm (check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let] let recv_psk = with_onorm(isc_lookups_psk isc) in
// TODO: uncomment once we remove post-processing
//  [@inline_let] let pattern = with_onorm(isc_get_pattern isc) in
  [@inline_let] let tokens = with_onorm(List.Tot.index pattern.messages i) in
  [@inline_let] let tokens_beg = with_onorm(fst(splitAtFirstElem S tokens)) in
  [@inline_let] let tokens_end = with_onorm(snd(splitAtFirstElem S tokens)) in
  (**) let h0 = ST.get () in
  (**) receive_message_tokens_nout_pre_lem #nc smi initiator is_psk tokens_beg
  (**)   st inlen input h0;
  let r =
// TODO: uncomment once we remove post-processing
//  Pervasives.norm [zeta_full; primops; iota; delta_only [`%receive_message_tokens_nout_m]]
  (receive_message_tokens_nout_m (receive_message_token_m ssdhi)
     smi initiator is_psk
     // tokens_beg:
     (with_norm (fst(splitAtFirstElem S (List.Tot.index pattern.messages i))))
     st inlen input) in
  (**) let h1 = ST.get () in
  (**) receive_message_tokens_nout_post_lem #nc smi initiator is_psk tokens_beg
  (**)   st inlen input h0 (convert_type r) h1;
  convert_type r

/// Small helper. We can't use post-processing to inline [let] bindings.
/// The critical thing is that the end list of tokens has to be inlined,
/// so that we can flatten the call to the recursive
/// receive_message_tokens_nout.
[@@ noextract_to "krml"] noextract unfold
val mk_receive_split_messagei_end_impl_aux
  (init_isc : valid_init_isc)
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages})
  (ssdhi : ssdh_impls (isc_get_nc init_isc))
  (tokens_beg : list message_token{tokens_beg = fst (splitAtFirstElem S (get_message (isc_get_pattern init_isc) i))})
  (tokens_end : list message_token{tokens_end = snd (splitAtFirstElem S (get_message (isc_get_pattern init_isc) i))}) :
  receive_split_messagei_end_impl init_isc resp_isc i

let mk_receive_split_messagei_end_impl_aux init_isc resp_isc i ssdhi tokens_beg tokens_end =
  fun payload_len payload st inlen input ->
  [@inline_let] let nc = isc_get_nc init_isc in
  [@inline_let] let initiator = i%2=1 in
  [@inline_let] let is_psk = with_onorm(check_hsk_is_psk (isc_get_pattern init_isc)) in
  [@inline_let] let smi = with_onorm(step_to_smi (isc_get_pattern init_isc) initiator i) in
  [@inline_let]
  let smi = with_onorm(smi_or_set_psk (isc_lookups_psk (get_receive_isc i init_isc resp_isc))
                                      (receive_tokens_update_smi is_psk tokens_beg smi)) in
  (**) let h0 = ST.get () in
  (**) receive_message_pre_lem #nc smi initiator is_psk tokens_end
  (**)   payload_len payload st inlen input h0;
  let r =
// TODO: uncomment once we remove post-processing
//  Pervasives.norm [zeta_full; primops; iota; delta_only [`%receive_message_tokens_nout_m]]
  (receive_message_tokens_with_payload_m
     (receive_message_tokens_nout_with_payload_m
       (ssdhi_get_ssi ssdhi) (receive_message_tokens_nout_m (receive_message_token_m ssdhi)))
     smi initiator is_psk tokens_end payload_len payload st inlen input) in
  (**) let h1 = ST.get () in
  (**) receive_message_post_lem #nc smi initiator is_psk tokens_end payload_len payload
  (**)   st inlen input h0 (convert_type r) h1;
  convert_type r

[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_receive_split_messagei_end_impl
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages})
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  receive_split_messagei_end_impl init_isc resp_isc i

let mk_receive_split_messagei_end_impl pattern init_isc resp_isc i ssdhi =
  mk_receive_split_messagei_end_impl_aux
    init_isc resp_isc i ssdhi
    // TODO: We use [with_norm] so that ithe normalization is compatible with post-processing
    (with_norm (fst (splitAtFirstElem S (get_message pattern i))))
    (with_norm (snd (splitAtFirstElem S (get_message pattern i))))

[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_receive_split_messagei_impls
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages})
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  receive_split_messagei_impls init_isc resp_isc i

let mk_receive_split_messagei_impls pattern init_isc resp_isc i ssdhi =
  mk_receive_split_messagei_beg_impl pattern init_isc resp_isc i ssdhi,
  convert_type (mk_receive_split_messagei_end_impl pattern init_isc resp_isc i ssdhi)

[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_receive_messagei_impl
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  (i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages})
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  receive_messagei_impl init_isc resp_isc i

let mk_receive_messagei_impl pattern init_isc resp_isc i ssdhi =
  // TODO: below we use [with_norm] so that it is compatible with post-processing
  if with_norm (List.Tot.mem S (get_message pattern i)) then
    Split_receive i (mk_receive_split_messagei_impls pattern init_isc resp_isc i ssdhi)
  else
    One_shot_receive i (mk_receive_no_split_messagei_impl pattern init_isc resp_isc i ssdhi)

//[@@ (strict_on_arguments [3;4])] // TODO: actually blocks the normalization, probably because of the type refinements
[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_send_message_impls_aux
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  // We introduce a concrete parameter for the messages length, so that
  // we can make it strict_on_arguments and prevent unfolding if it does
  // not normalize.
  (n : nat{n = List.Tot.length (isc_get_pattern init_isc).messages})
  (i : nat{i < n})
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  Tot (send_message_impls_aux init_isc resp_isc i)
  (decreases (n - i))

let rec mk_send_message_impls_aux pattern init_isc resp_isc n i ssdhi =
  let impli = mk_send_messagei_impl pattern init_isc resp_isc i ssdhi in
  if i = n-1 then
    Send_message_last i impli
  else
    Send_message_i i impli (mk_send_message_impls_aux pattern init_isc resp_isc n (i+1) ssdhi)

#push-options "--fuel 1 --ifuel 1" // to prove that the number of messages > 0
[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_send_message_impls
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  Tot (send_message_impls init_isc resp_isc)

let mk_send_message_impls pattern init_isc resp_isc ssdhi =
// TODO: once the normalizer works again, uncomment those lines
//  [@inline_let] let n = with_onorm(List.Tot.length (isc_get_pattern init_isc).messages) in
//  with_norm_steps [zeta; delta_only [`%mk_send_message_impls_aux]]
  (mk_send_message_impls_aux pattern init_isc resp_isc
                             (with_norm(List.Tot.length pattern.messages)) // inlining is necessary for post-processing
                             0 ssdhi)
#pop-options

//[@@ (strict_on_arguments [3;4])] // TODO: actually blocks the normalization, probably because of the type refinements
[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_receive_message_impls_aux
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  // We introduce a concrete parameter for the messages length, so that
  // we can make it strict_on_arguments and prevent unfolding if it does
  // not normalize.
  (n : nat{n = List.Tot.length (isc_get_pattern init_isc).messages})
  (i : nat{i < n})
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  Tot (receive_message_impls_aux init_isc resp_isc i)
  (decreases (n - i))

let rec mk_receive_message_impls_aux pattern init_isc resp_isc n i ssdhi =
  let impli = mk_receive_messagei_impl pattern init_isc resp_isc i ssdhi in
  if i = n -1 then
    Receive_message_last i impli
  else
    Receive_message_i i impli (mk_receive_message_impls_aux pattern init_isc resp_isc n (i+1) ssdhi)

#push-options "--fuel 1 --ifuel 1" // to prove that the number of messages > 0
[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_receive_message_impls
  (pattern : wf_handshake_pattern) // TODO: remove once we remove post-processing
  (init_isc : valid_init_isc{pattern == isc_get_pattern init_isc})
  (resp_isc : valid_resp_isc init_isc)
  (ssdhi : ssdh_impls (isc_get_nc init_isc)) :
  Tot (receive_message_impls init_isc resp_isc)

#restart-solver
let mk_receive_message_impls pattern init_isc resp_isc ssdhi =
// TODO: uncomment once we remove post-processing
//  [@inline_let] let n = with_onorm(List.Tot.length (isc_get_pattern init_isc).messages) in
//  with_norm_steps [zeta; delta_only [`%mk_receive_message_impls_aux]]
  (mk_receive_message_impls_aux pattern init_isc resp_isc
    (with_norm (List.Tot.length pattern.messages)) 0 ssdhi)
#pop-options

(*** Handshake write message i *)

val mk_state_t_handshake_writei_pre :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t (get_send_isc i init_isc resp_isc) (i%2=0){state_t_is_handshake st}
  -> outlen : size_t
  -> out : lbuffer uint8 outlen
  -> h0:mem -> GTot Type0

let mk_state_t_handshake_writei_pre =
  fun init_isc resp_isc i payload_len payload st outlen out h0 ->

  let initiator = i%2=0 in
  let isc = get_send_isc i init_isc resp_isc in

  mk_state_t_handshake_write_stateful_pre #isc #initiator payload_len payload st outlen out h0 /\

  get_aead_pre (isc_get_nc isc) /\
  get_dh_pre (isc_get_nc isc) /\
  get_hash_pre (isc_get_nc isc) /\

  handshake_state_t_valid_values initiator i st true

val mk_state_t_handshake_writei_post :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t (get_send_isc i init_isc resp_isc) (i%2=0){state_t_is_handshake st}
  -> outlen : size_t
  -> out : lbuffer uint8 outlen
  -> h0:mem
  -> res:s_result_code (st:state_t (get_send_isc i init_isc resp_isc) (i%2=0){state_t_is_handshake st})
  -> h1:mem -> GTot Type0

let mk_state_t_handshake_writei_post =
  fun init_isc resp_isc i payload_len payload st outlen out h0 res h1 ->
  let initiator = i%2=0 in
  let isc = get_send_isc i init_isc resp_isc in
  let smi = isc_step_to_smi #initiator isc i in
  let post_smi = isc_step_to_smi #initiator isc (i+1) in

  begin
    // We need this for mk_state_t_handshake_write_post
  (**) let nc = isc_get_nc isc in
  (**) let pattern = isc_get_pattern isc in
  (**) let tokens = List.Tot.index pattern.messages i in
  (**) let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  (**) check_pattern_messagei_lem (isc_get_pattern isc) i;
  (**) max_tokens_message_size_lem (get_config nc) smi.hsf.sk is_psk tokens
  end;

  mk_state_t_handshake_write_post
    #isc #initiator smi post_smi i payload_len payload st outlen out h0 res h1

[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_state_t_handshake_writei :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> send_message:send_messagei_impl init_isc resp_isc i
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t (get_send_isc i init_isc resp_isc) (i%2=0){state_t_is_handshake st}
  -> outlen : size_t
  -> out : lbuffer uint8 outlen ->
  Stack (s_result_code (st:state_t (get_send_isc i init_isc resp_isc) (i%2=0){state_t_is_handshake st}))
  (requires (fun h0 ->
    mk_state_t_handshake_writei_pre
      init_isc resp_isc i payload_len payload st outlen out h0))
  (ensures (fun h0 res h1 ->
    mk_state_t_handshake_writei_post
      init_isc resp_isc i payload_len payload st outlen out h0 res h1))

let mk_state_t_handshake_write_smi_pre :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> initiator:bool
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> GTot Type0 =
  fun #isc smi initiator i ->
  let nc = isc_get_nc isc in
  let pattern = isc_get_pattern isc in
  let pat = List.Tot.index pattern.messages i in
  let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  let post_smi = send_message_update_smi is_psk pat smi in
  isc_valid_meta_info isc post_smi /\
  check_send_message_smi smi initiator is_psk pat

let mk_state_t_handshake_writei =
  fun init_isc resp_isc i send_message payload_len payload st outlen out ->
  (**) let h0 = ST.get () in
  [@inline_let] let initiator = i%2=0 in
  [@inline_let] let isc = get_send_isc i init_isc resp_isc in
  [@inline_let] let smi = isc_step_to_smi #initiator isc i  in

  (**) check_pattern_valid_meta_info_lem initiator isc i;
  (**) check_pattern_messagei_lem (isc_get_pattern isc) i;
  (**) assert(mk_state_t_handshake_write_smi_pre #isc smi initiator i);
  
  begin
  (**) let nc = isc_get_nc isc in
  (**) let post_smi = isc_step_to_smi #initiator isc (i+1) in
  (**) let pattern = isc_get_pattern isc in
  (**) let tokens = List.Tot.index pattern.messages i in
  (**) let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  (**) let post_smi' = send_message_update_smi is_psk tokens smi in
  (**) max_tokens_message_size_lem (get_config nc) smi.hsf.sk is_psk tokens;
  (**) assert(tokens_message_size (get_config nc) smi.hsf.sk is_psk tokens <= max_size_t);
  (**) assert(isc_valid_meta_info isc post_smi);
  (**) assert(post_smi' = post_smi)
  end;

  let res = mk_state_t_handshake_write #isc smi i send_message
                                     payload_len payload st outlen out <:
  s_result_code (st:state_t (get_send_isc i init_isc resp_isc) (i%2=0){state_t_is_handshake st})
  in
  (**) let h1 = ST.get () in
  // SH: Doesn't work without this assertion!?
  (**) assert(
  (**)   mk_state_t_handshake_writei_post
  (**)     init_isc resp_isc i payload_len payload st outlen out h0 res h1);
  res


(*** Handshake read message i *)

// TODO: move
[@@ noextract_to "krml"] inline_for_extraction noextract
type state_t_handshake
  (init_isc : valid_init_isc) (resp_isc : valid_resp_isc init_isc) (initiator : bool) =
  st:state_t (get_proper_isc initiator init_isc resp_isc) initiator{state_t_is_handshake st}

let state_t_handshake_shared_props
  (#isc : isconfig)
  (#initiator : bool)
  (st1 : state_t isc initiator{state_t_is_handshake st1})
  (st2 : state_t isc initiator{state_t_is_handshake st2}) : GTot Type0 =
  Impl.Noise.API.State.Base.state_t_handshake_shared_props st1 st2

[@@ noextract_to "krml"] inline_for_extraction noextract
let isc_receive_validate
  (init_isc : valid_init_isc) (resp_isc : valid_resp_isc init_isc) (initiator : bool) =
  isc_validate (get_proper_isc initiator init_isc resp_isc)

[@@ noextract_to "krml"] noextract unfold
val mk_state_t_handshake_readi_pre :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> vfunct:isc_receive_validate init_isc resp_isc (i%2=1)
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc (i%2=1)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem -> GTot Type0

let mk_state_t_handshake_readi_pre =
  fun init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 ->
  let initiator = i%2=1 in
  let isc = get_proper_isc initiator init_isc resp_isc in
  let smi = isc_step_to_smi #initiator isc i in

  mk_state_t_handshake_read_with_S_pre_stateful
    #isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 /\

  handshake_state_t_valid_values initiator i st false

[@@ noextract_to "krml"] noextract unfold
val mk_state_t_handshake_readi_post :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> vfunct:isc_receive_validate init_isc resp_isc (i%2=1)
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc (i%2=1)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem
  -> res : s_result_code (state_t_handshake init_isc resp_isc (i%2=1))
  -> h1 : mem -> GTot Type0

let mk_state_t_handshake_readi_post =
  fun init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out
    st inlen input h0 res h1 ->
  let initiator = i%2=1 in
  let isc = get_proper_isc initiator init_isc resp_isc in
  let smi = isc_step_to_smi #initiator isc i in
  let post_smi = isc_step_to_smi #initiator isc (i+1) in

  begin
  (**) let nc = isc_get_nc isc in
  (**) let pattern = isc_get_pattern isc in
  (**) let tokens = List.Tot.index pattern.messages i in
  (**) let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  (**) check_pattern_valid_meta_info_lem initiator isc i;
  (**) assert(isc_valid_meta_info isc post_smi);
    // We need this for mk_state_t_handshake_write_post
  (**) check_pattern_messagei_lem (isc_get_pattern isc) i;
  (**) max_tokens_message_size_lem (get_config nc) smi.hsf.sk is_psk tokens
  end;


  B.(modifies (loc_union (state_t_core_footprint st)
               (loc_union (loc_buffer (payload_out <: buffer uint8))
                           ((isc_get_pinfo isc).St.footprint pinfo))) h0 h1) /\

  // See the comment in mk_state_t_handshake_read_post
  live h1 payload_out /\ live h1 input /\

  vfunct.vst.St.invariant h1 vst /\
  (isc_get_pinfo isc).St.invariant h1 pinfo /\
  ((isc_get_pinfo isc).St.freeable h0 pinfo ==>
   (isc_get_pinfo isc).St.freeable h1 pinfo) /\

  state_t_handshake_invariant h1 st /\
  vfunct.vst.St.v () h1 vst == vfunct.vst.St.v () h0 vst /\ // sanity check

  begin
  let recv_psk = isc_lookups_psk isc in
  let pattern = isc_get_pattern isc in
  let tokens = List.Tot.index pattern.messages i in
  let has_s = List.Tot.mem S tokens in
  let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  let vst0_v = vfunct.vst.St.v () h0 vst in
  let st0_v = handshake_state_t_v_with_smi h0 st smi in
  let input_v = as_seq h0 input in
  let res_v' = handshake_read #(isc_get_sc isc) input_v st0_v vst0_v in
  let pinfo0_v = (isc_get_pinfo isc).St.v () h0 pinfo in
  let pinfo1_v = (isc_get_pinfo isc).St.v () h1 pinfo in

  match res with
  | Res st' ->
    Res? res_v' /\
    begin
    let Res (pinfo_v, payload'_v, st1'_v) = res_v' in
    handshake_state_t_v_with_smi h1 st' post_smi == st1'_v /\
    as_seq h1 payload_out == payload'_v /\
    // Those lines are the only difference with [mk_state_t_handshake_read_with_S_post]
    (Some? pinfo_v = has_s) /\
    (has_s ==> pinfo1_v == Some?.v pinfo_v) /\
    (not has_s ==> pinfo1_v == pinfo0_v) /\
    state_t_handshake_invariant h1 st' /\
    state_t_handshake_shared_props st st'
    end
  | Fail _ ->
    check_input_output_len (isc_get_nc isc) smi is_psk tokens payload_outlen inlen ==>
    Fail? res_v'
  | _ -> False
  end

val mk_state_t_handshake_readi_no_S_pre :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> vfunct:isc_receive_validate init_isc resp_isc (i%2=1)
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc (i%2=1)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem -> GTot Type0

let mk_state_t_handshake_readi_no_S_pre =
  fun init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 ->

  mk_state_t_handshake_readi_pre
    init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 /\
  
  begin
  let pattern = isc_get_pattern init_isc in
  let tokens = get_message pattern i in
  not (List.Tot.mem S tokens)
  end

val mk_state_t_handshake_readi_no_S_post :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> vfunct:isc_receive_validate init_isc resp_isc (i%2=1)
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc (i%2=1)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem
  -> res:s_result_code (state_t_handshake init_isc resp_isc (i%2=1))
  -> h1:mem
  -> GTot Type0

let mk_state_t_handshake_readi_no_S_post =
  fun init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out
    st inlen input h0 res h1 ->
  mk_state_t_handshake_readi_post
    init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1

[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_state_t_handshake_readi_no_S :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> receive_message:receive_no_split_messagei_impl init_isc resp_isc i
  -> vfunct:isc_receive_validate init_isc resp_isc (i%2=1)
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc (i%2=1)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->
  Stack (s_result_code (state_t_handshake init_isc resp_isc (i%2=1)))
  (requires (fun h0 ->
    mk_state_t_handshake_readi_no_S_pre
      init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0))
  (ensures (fun h0 res h1 ->
    mk_state_t_handshake_readi_no_S_post
      init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1))

let mk_state_t_handshake_readi_no_S =
  fun init_isc resp_isc i receive_message vfunct vst pinfo
    payload_outlen payload_out st inlen input ->

  (**) let h0 = ST.get () in  
  [@inline_let] let initiator = i%2=1 in
  [@inline_let] let isc = get_proper_isc initiator init_isc resp_isc in
  [@inline_let] let smi = isc_step_to_smi #initiator isc i  in
  (**) check_pattern_messagei_lem (isc_get_pattern isc) i;

  // Another problem with the SMT encoding of types
  (**) assert_norm(
  (**)   state_t_handshake init_isc resp_isc (i%2=1) ==
  (**)   st:state_t (get_proper_isc (i%2=1) init_isc resp_isc) initiator{state_t_is_handshake st});
  (**) assert(
  (**)   state_t_handshake init_isc resp_isc (i%2=1) ==
  (**)   s:state_t isc (i%2=1){state_t_is_handshake s});
  (**) assert(
  (**)   s_result_code (state_t_handshake init_isc resp_isc (i%2=1)) ==
  (**)   s_result_code (s:state_t isc (i%2=1){state_t_is_handshake s}));

  begin
  (**) let nc = isc_get_nc isc in
  (**) let post_smi = isc_step_to_smi #initiator isc (i+1) in
  (**) let pattern = isc_get_pattern isc in
  (**) let tokens = List.Tot.index pattern.messages i in
  (**) let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  (**) let post_smi' = receive_message_update_smi is_psk tokens smi in
  (**) max_tokens_message_size_lem (get_config nc) smi.hsf.sk is_psk tokens;
  (**) assert(tokens_message_size (get_config nc) smi.hsf.sk is_psk tokens <= max_size_t);
  (**) assert(mk_state_t_handshake_read_no_S_smi_pre isc smi i);
  (**) assert(isc_valid_meta_info isc post_smi);
  (**) assert(post_smi' = post_smi)
  end;

  (**) assert(mk_state_t_handshake_read_no_S_pre
  (**)   #isc smi i vfunct vst payload_outlen payload_out st inlen input h0);


  let r : s_result_code (state_t_handshake init_isc resp_isc (i%2=1)) =
  mk_state_t_handshake_read_no_S #isc smi i receive_message
                                 vfunct vst payload_outlen payload_out st inlen input
  in

  begin
  (**) let h1 = ST.get () in
  (**) state_t_footprint_inclusion_lem st;
  (**) assert(B.loc_includes (state_t_footprint st) (state_t_core_footprint st));
  (**) let l = B.(loc_union (state_t_core_footprint st) (loc_buffer (payload_out <: buffer uint8))) in
  (**) vfunct.vst.St.frame_invariant l vst h0 h1;
  (**) (isc_get_pinfo isc).St.frame_invariant l pinfo h0 h1;
  (**) St.opt_frame_freeable (isc_get_pinfo isc) l pinfo h0 h1;
  (**) assert(
  (**)  mk_state_t_handshake_readi_no_S_post
  (**)    init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 r h1)
  end;

  r

[@@ noextract_to "krml"] noextract unfold
val mk_state_t_handshake_readi_with_S_pre :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> vfunct:isc_receive_validate init_isc resp_isc (i%2=1)
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc (i%2=1)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem -> GTot Type0

let mk_state_t_handshake_readi_with_S_pre =
  fun init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 ->

  mk_state_t_handshake_readi_pre
    init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 /\

  begin
  let pattern = isc_get_pattern init_isc in
  let tokens = get_message pattern i in
  List.Tot.mem S tokens
  end

[@@ noextract_to "krml"] noextract unfold
val mk_state_t_handshake_readi_with_S_post :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> vfunct:isc_receive_validate init_isc resp_isc (i%2=1)
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc (i%2=1)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem
  -> res:s_result_code (state_t_handshake init_isc resp_isc (i%2=1))
  -> h1:mem
  -> GTot Type0

let mk_state_t_handshake_readi_with_S_post =
  fun init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1 ->
  mk_state_t_handshake_readi_post
    init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1

/// This function has effect ST and not Stack because copying the peer information
/// might require stateful operations.
[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_state_t_handshake_readi_with_S :
     init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> impls:receive_split_messagei_impls init_isc resp_isc i
  -> vfunct:isc_receive_validate init_isc resp_isc (i%2=1)
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc (i%2=1)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->
  ST (s_result_code (state_t_handshake init_isc resp_isc (i%2=1)))
  (requires (fun h0 ->
    mk_state_t_handshake_readi_with_S_pre
      init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0))
  (ensures (fun h0 res h1 ->
    mk_state_t_handshake_readi_with_S_post
      init_isc resp_isc i vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1))

/// F* used to work a very long time (60s) on this definition before sending it to Z3
/// After investigation, it was because of the impls parameter: we had to make it
/// more "abstract" (by abstracting the pre and the post)
let mk_state_t_handshake_readi_with_S =
  fun init_isc resp_isc i impls vfunct vst pinfo payload_outlen payload_out st inlen input ->
  
  [@inline_let] let initiator = i%2=1 in
  [@inline_let] let isc = get_proper_isc initiator init_isc resp_isc in
  [@inline_let] let smi = isc_step_to_smi #initiator isc i in
  
  (**) check_pattern_messagei_lem (isc_get_pattern isc) i;
  
  begin
  (**) let nc = isc_get_nc isc in
  (**) let recv_psk = isc_lookups_psk isc in
  (**) let post_smi = isc_step_to_smi #initiator isc (i+1) in
  (**) let pattern = isc_get_pattern isc in
  (**) let tokens = List.Tot.index pattern.messages i in
  (**) let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  (**) let post_smi' = smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi) in
  (**) max_tokens_message_size_lem (get_config nc) smi.hsf.sk is_psk tokens;
  (**) assert(tokens_message_size (get_config nc) smi.hsf.sk is_psk tokens <= max_size_t);
  (**) assert(is_psk ==> lookups_psk pattern initiator);
  (**) assert(mk_state_t_handshake_read_with_S_smi_pre isc smi i);
  (**) assert(isc_valid_meta_info isc post_smi);
  (**) assert(post_smi' = post_smi);
  // SMT encoding, again
  (**) assert_norm(
  (**)   state_t_handshake init_isc resp_isc (i%2=1) ==
  (**)   st:state_t (get_proper_isc (i%2=1) init_isc resp_isc) initiator{state_t_is_handshake st})
  end;

  mk_state_t_handshake_read_with_S #isc smi i impls
                                   vfunct vst pinfo payload_outlen payload_out st inlen input


(**** Transition functions *)

(**** handshake write *)
// Note that here, we don't necessarily have: initiator=(i%2=0)
// The reason is that this function is used to go through the list of all
// the send_message implementations (including those which are not valid
// for the current state, and which we ignore).
val mk_state_t_handshake_writei_rec_pre :
     initiator : bool
  -> init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> step : UInt32.t{UInt32.v step < List.Tot.length (isc_get_pattern init_isc).messages}
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t_handshake init_isc resp_isc initiator
  -> outlen : size_t
  -> out : lbuffer uint8 outlen
  -> h0:mem -> GTot Type0

let mk_state_t_handshake_writei_rec_pre =
  fun initiator init_isc resp_isc i step payload_len payload st outlen out h0 ->
  let step = UInt32.v step in
  let isc = get_proper_isc initiator init_isc resp_isc in

  mk_state_t_handshake_write_stateful_pre #isc #initiator payload_len payload st outlen out h0 /\

  get_aead_pre (isc_get_nc isc) /\
  get_dh_pre (isc_get_nc isc) /\
  get_hash_pre (isc_get_nc isc) /\

  begin
//  initiator = state_t_handshake_get_initiator st /\
  step = UInt32.v (state_t_handshake_get_step st) /\
  step >= i /\
  Handshake_send? (step_to_status initiator step)
  end

val mk_state_t_handshake_writei_rec_post :
     initiator : bool
  -> init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> step : UInt32.t{UInt32.v step < List.Tot.length (isc_get_pattern init_isc).messages}
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t_handshake init_isc resp_isc initiator
  -> outlen : size_t
  -> out : lbuffer uint8 outlen
  -> h0:mem
  -> res:s_result_code (state_t_handshake init_isc resp_isc initiator)
  -> h1:mem
  -> GTot Type0

let mk_state_t_handshake_writei_rec_post =
  fun initiator init_isc resp_isc i step payload_len payload st outlen out h0 res h1 ->
  let step = UInt32.v step in
  let isc = get_proper_isc initiator init_isc resp_isc in
  let smi = isc_step_to_smi #initiator isc step in
  let post_smi = isc_step_to_smi #initiator isc (step+1) in

  (**) check_pattern_valid_meta_info_lem initiator isc step;
  (**) assert(isc_valid_meta_info isc post_smi);

  begin
  // We need this for mk_state_t_handshake_write_post
  (**) let nc = isc_get_nc isc in
  (**) let pattern = isc_get_pattern isc in
  (**) let tokens = List.Tot.index pattern.messages step in
  (**) let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
  (**) check_pattern_messagei_lem (isc_get_pattern isc) step;
  (**) max_tokens_message_size_lem (get_config nc) smi.hsf.sk is_psk tokens
  end;

  mk_state_t_handshake_write_post
    #isc #initiator smi post_smi step payload_len payload st outlen out h0 res h1

[@@ (strict_on_arguments [5]); noextract_to "krml"]
inline_for_extraction noextract
val mk_state_t_handshake_writei_rec :
     initiator:bool
  -> init_isc:valid_init_isc
  -> resp_isc:valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> step : UInt32.t{UInt32.v step < List.Tot.length (isc_get_pattern init_isc).messages}
  -> impls:send_message_impls_aux init_isc resp_isc i
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t_handshake init_isc resp_isc initiator
  -> outlen : size_t
  -> out : lbuffer uint8 outlen ->
  Stack (s_result_code (state_t_handshake init_isc resp_isc initiator))
  (requires (fun h0 ->
    mk_state_t_handshake_writei_rec_pre initiator init_isc resp_isc i step
                                        payload_len payload st outlen out h0))
  (ensures (fun h0 res h1 ->
    mk_state_t_handshake_writei_rec_post
      initiator init_isc resp_isc i step payload_len payload st outlen out h0 res h1))
  (decreases (impls))

// Note that the control-flow below is a bit convoluted. The reason is that we
// need to make sure we don't mix function calls which take an initiator state and
// function calls which take a responder state (they don't have the same ML type)
let rec mk_state_t_handshake_writei_rec =
  fun initiator init_isc resp_isc i step impls payload_len payload st outlen out ->
  (**) let h0 = ST.get () in
  match impls with
  | Send_message_last _ send ->
    // Sanity check: we shouldn't get here if we can't call the function
    (**) assert((i%2=0) = initiator);
    let res =
      mk_state_t_handshake_writei init_isc resp_isc i send payload_len payload st outlen out <:
      s_result_code (state_t_handshake init_isc resp_isc initiator)
    in
    (**) let h1 = ST.get () in
    // Doesn't work without this assertion
    (**) assert(mk_state_t_handshake_writei_rec_post
    (**)        initiator init_isc resp_isc i step payload_len payload st outlen out h0 res h1);
    res
  | Send_message_i _ send impls' ->
    // Check if this step is compatible with the state type (initiator/responder)
    // Jump the step if it is not
    if (i%2=0)=initiator then
      // Don't do the recursive call if it is not necessary
      if i >= with_onorm #nat (List.Tot.length (isc_get_pattern init_isc).messages - 2) then
        begin
        let res =
          (mk_state_t_handshake_writei init_isc resp_isc i send payload_len payload st outlen out <:
           s_result_code (state_t_handshake init_isc resp_isc initiator))
        in
        (**) let h1 = ST.get () in
        // Doesn't work without this assertion
        (**) assert(mk_state_t_handshake_writei_rec_post
        (**)        initiator init_isc resp_isc i step payload_len payload st outlen out h0 res h1);
        res
        end
      // Otherwise: step test then recursive call
      else
        if FStar.UInt32.(step =^ size i) then
          begin
          let res =
            (mk_state_t_handshake_writei init_isc resp_isc i send payload_len payload st outlen out <:
             s_result_code (state_t_handshake init_isc resp_isc initiator))
          in
          (**) let h1 = ST.get () in
          // Doesn't work without this assertion
          (**) assert(mk_state_t_handshake_writei_rec_post
          (**)        initiator init_isc resp_isc i step payload_len payload st outlen out h0 res h1);
          res
          end
        else
          // Recursive call: note that the next step will actually be statically ignored
          mk_state_t_handshake_writei_rec initiator init_isc resp_isc (i+1) step impls' payload_len payload st outlen out <:
          s_result_code (state_t_handshake init_isc resp_isc initiator)
    else
        mk_state_t_handshake_writei_rec initiator init_isc resp_isc (i+1) step impls' payload_len payload st outlen out <:
        s_result_code (state_t_handshake init_isc resp_isc initiator)

[@@ noextract_to "krml"] inline_for_extraction noextract
type state_t_handshake_write_rec_impl
     (initiator:bool)
     (init_isc:valid_init_isc)
     (resp_isc:valid_resp_isc init_isc) =
     step : UInt32.t{UInt32.v step < List.Tot.length (isc_get_pattern init_isc).messages}
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st:state_t_handshake init_isc resp_isc initiator
  -> outlen : size_t
  -> out : lbuffer uint8 outlen ->
  Stack (s_result_code (state_t_handshake init_isc resp_isc initiator))
  (requires (fun h0 ->
    mk_state_t_handshake_writei_rec_pre initiator init_isc resp_isc 0 step
                                        payload_len payload st outlen out h0))
  (ensures (fun h0 res h1 ->
    mk_state_t_handshake_writei_rec_post
      initiator init_isc resp_isc 0 step payload_len payload st outlen out h0 res h1))

// The following function takes a state as parameter and returns a state.
// As initiator state and responder state are not the same type (because some
// fields might be present or not) we need to add a meta parameter initiator.
// This parameter will be dynamically resolved at the top-level functions by
// performing a match on the state.
[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_state_t_handshake_write_rec
     (initiator : bool)
     (init_isc:valid_init_isc)
     (resp_isc:valid_resp_isc init_isc)
     (impls:send_message_impls init_isc resp_isc) :
  state_t_handshake_write_rec_impl initiator init_isc resp_isc

let mk_state_t_handshake_write_rec =
  fun initiator init_isc resp_isc impls step payload_len payload st outlen out ->
// TODO: uncomment once we can remove post-processing
//  Pervasives.norm [zeta_full; primops; iota; iota; primops; delta_only [`%mk_state_t_handshake_writei_rec]]
  (mk_state_t_handshake_writei_rec initiator init_isc resp_isc 0 step impls payload_len payload st outlen out) <:
  s_result_code (state_t_handshake init_isc resp_isc initiator)


(**** Handshake read *)

[@@ noextract_to "krml"] noextract unfold
val mk_state_t_handshake_readi_rec_pre :
     initiator : bool
  -> init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> step : UInt32.t{UInt32.v step < List.Tot.length (isc_get_pattern init_isc).messages}
  -> vfunct:isc_receive_validate init_isc resp_isc initiator
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc initiator
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem -> GTot Type0

let mk_state_t_handshake_readi_rec_pre =
  fun initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out st inlen input h0 ->
  let step_v = UInt32.v step in
  let isc = get_proper_isc initiator init_isc resp_isc in

  initiator = (step_v % 2 = 1) /\

  mk_state_t_handshake_readi_pre
    init_isc resp_isc step_v vfunct vst pinfo payload_outlen payload_out st inlen input h0 /\

  begin
//  initiator = state_t_handshake_get_initiator st /\
  step_v = UInt32.v (state_t_handshake_get_step st) /\
  step_v >= i /\
  Handshake_receive? (step_to_status initiator step_v)
  end

[@@ noextract_to "krml"] noextract unfold
val mk_state_t_handshake_readi_rec_post :
     initiator : bool
  -> init_isc : valid_init_isc
  -> resp_isc : valid_resp_isc init_isc
  -> i : nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> step : UInt32.t{UInt32.v step < List.Tot.length (isc_get_pattern init_isc).messages /\ initiator = (UInt32.v step % 2 =1)}
  -> vfunct:isc_receive_validate init_isc resp_isc initiator
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc initiator
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem
  -> res:s_result_code (state_t_handshake init_isc resp_isc initiator)
  -> h1:mem
  -> GTot Type0

let mk_state_t_handshake_readi_rec_post =
  fun initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1 ->
  let step_v = UInt32.v step in

  mk_state_t_handshake_readi_post
    init_isc resp_isc step_v vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1

[@@ (strict_on_arguments [5]); noextract_to "krml"]
inline_for_extraction noextract
val mk_state_t_handshake_readi_rec :
     initiator:bool
  -> init_isc:valid_init_isc
  -> resp_isc:valid_resp_isc init_isc
  -> i:nat{i < List.Tot.length (isc_get_pattern init_isc).messages}
  -> step:UInt32.t{UInt32.v step < List.Tot.length (isc_get_pattern init_isc).messages}
  -> impls:receive_message_impls_aux init_isc resp_isc i
  -> vfunct:isc_receive_validate init_isc resp_isc initiator
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc initiator
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->
  ST (s_result_code (state_t_handshake init_isc resp_isc initiator))
  (requires (fun h0 ->
    mk_state_t_handshake_readi_rec_pre initiator init_isc resp_isc i step vfunct vst pinfo
                                       payload_outlen payload_out st inlen input h0))
  (ensures (fun h0 res h1 ->
    mk_state_t_handshake_readi_rec_post
      initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1))
  (decreases (impls))

// This is a bit convoluted, because we need to make sure not to mix
// function calls manipulating states with different types (initiator and responder)
// because those aren't the same ML type
let rec mk_state_t_handshake_readi_rec =
  fun initiator init_isc resp_isc i step impls vfunct vst pinfo
    payload_outlen payload_out st inlen input ->
  (**) let h0 = ST.get () in
  match impls with
  | Receive_message_last _ receive ->
    begin match receive with
    | One_shot_receive _ receive ->
      let res =
        mk_state_t_handshake_readi_no_S
          init_isc resp_isc i receive vfunct vst pinfo payload_outlen payload_out st inlen input
      in
      (**) let h1 = ST.get () in
      // Guess what? Doesn't work without this assertion
      (**) assert(mk_state_t_handshake_readi_rec_post
      (**)          initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out
      (**)          st inlen input h0 res h1);
      res
    | Split_receive _ receive ->
      let res =
        mk_state_t_handshake_readi_with_S
          init_isc resp_isc i receive vfunct vst pinfo payload_outlen payload_out st inlen input
      in
      (**) let h1 = ST.get () in
      // Doesn't work without this assertion
      (**) assert(mk_state_t_handshake_readi_rec_post
      (**)          initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out
      (**)          st inlen input h0 res h1);
      res
    end
  | Receive_message_i _ receive impls' ->
    // Statically check if this step is compatible with the state type (initiator/responder)
    // Jump the step if it is not
    if (i%2=1)=initiator then
      // Don't do the recursive call if it is not necessary
      if i >= with_onorm #nat (List.Tot.length (isc_get_pattern init_isc).messages - 2) then
        begin match receive with
        | One_shot_receive _ receive ->
          let res =
            mk_state_t_handshake_readi_no_S
              init_isc resp_isc i receive vfunct vst pinfo payload_outlen payload_out st inlen input
          in
          (**) let h1 = ST.get () in
          // Doesn't work without this assertion
          (**) assert(mk_state_t_handshake_readi_rec_post
          (**)          initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out
          (**)          st inlen input h0 res h1);
          res
        | Split_receive _ receive ->
          let res =
            mk_state_t_handshake_readi_with_S
              init_isc resp_isc i receive vfunct vst pinfo payload_outlen payload_out st inlen input
          in
          (**) let h1 = ST.get () in
          // Doesn't work without this assertion
          (**) assert(mk_state_t_handshake_readi_rec_post
          (**)          initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out
          (**)          st inlen input h0 res h1);
          res
        end
      // Otherwise: step test then recursive call
      else
        if FStar.UInt32.(step =^ size i) then
          begin match receive with
          | One_shot_receive _ receive ->
            let res =
              mk_state_t_handshake_readi_no_S
                init_isc resp_isc i receive vfunct vst pinfo payload_outlen payload_out st inlen input
            in
            (**) let h1 = ST.get () in
            // Doesn't work without this assertion
            (**) assert(mk_state_t_handshake_readi_rec_post
            (**)          initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out
            (**)          st inlen input h0 res h1);
            res
          | Split_receive _ receive ->
            let res =
              mk_state_t_handshake_readi_with_S
                init_isc resp_isc i receive vfunct vst pinfo payload_outlen payload_out st inlen input
            in
            (**) let h1 = ST.get () in
            // Doesn't work without this assertion
            (**) assert(mk_state_t_handshake_readi_rec_post
            (**)          initiator init_isc resp_isc i step vfunct vst pinfo payload_outlen payload_out
            (**)          st inlen input h0 res h1);
            res
          end
        // Recursive call: note that the next step will actually be statically ignored
        else mk_state_t_handshake_readi_rec initiator init_isc resp_isc (i+1) step impls' vfunct vst pinfo payload_outlen payload_out st inlen input
    else mk_state_t_handshake_readi_rec initiator init_isc resp_isc (i+1) step impls' vfunct vst pinfo payload_outlen payload_out st inlen input

[@@ noextract_to "krml"] inline_for_extraction noextract
type state_t_handshake_read_rec_impl
  (initiator:bool)
  (init_isc:valid_init_isc)
  (resp_isc:valid_resp_isc init_isc) =
     step:UInt32.t{UInt32.v step < List.Tot.length (isc_get_pattern init_isc).messages}
  -> vfunct:isc_receive_validate init_isc resp_isc initiator
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo init_isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t_handshake init_isc resp_isc initiator
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->
  ST (s_result_code (state_t_handshake init_isc resp_isc initiator))
  (requires (fun h0 ->
    mk_state_t_handshake_readi_rec_pre initiator init_isc resp_isc 0 step vfunct vst pinfo
                                       payload_outlen payload_out st inlen input h0))
  (ensures (fun h0 res h1 ->
    mk_state_t_handshake_readi_rec_post
      initiator init_isc resp_isc 0 step vfunct vst pinfo payload_outlen payload_out st inlen input h0 res h1))

[@@ noextract_to "krml"] inline_for_extraction noextract
val mk_state_t_handshake_read_rec
  (initiator:bool)
  (init_isc:valid_init_isc)
  (resp_isc:valid_resp_isc init_isc)
  (impls:receive_message_impls init_isc resp_isc) :
  state_t_handshake_read_rec_impl initiator init_isc resp_isc

let mk_state_t_handshake_read_rec =
  fun initiator init_isc resp_isc impls step vfunct vst pinfo payload_outlen payload_out st inlen input ->
// TODO: uncomment once we can remove post-processing
//  Pervasives.norm [zeta_full; primops; iota; delta_only [`%mk_state_t_handshake_readi_rec]]
  (mk_state_t_handshake_readi_rec initiator init_isc resp_isc 0 step impls vfunct vst pinfo payload_outlen payload_out st inlen input)
