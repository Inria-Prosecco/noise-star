module Impl.Noise.API.DState

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
module BS = Lib.ByteSequence
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module G = FStar.Ghost

open Spec.Noise.API.State.Definitions
open Spec.Noise.API.State
module M = Spec.Noise.Map
open Spec.Noise.API.Device
open Spec.Noise.API.DState
module Spec = Spec.Noise.API.DState

open Impl.Noise.Types
open Impl.Noise.HandshakeState
open Impl.Noise.SendReceive
open Impl.Noise.RecursiveMessages
open Impl.Noise.API.State
module State = Impl.Noise.API.State
open Impl.Noise.API.Device
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.BufferEquality
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate
open Spec.Noise
open Spec.Noise.API.MetaInfo

open Meta.Noise

module LL = Impl.Noise.LinkedList
module St = Impl.Noise.Stateful

open Lib.Memzero0

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

val _align_fsti : unit

(*** Types *)

/// In the specification, we use different types to encode the error codes for
/// the different levels of the API. In the implementation, to prevent useless
/// conversions and in order not to clutter the code, we use one type [error_code],
/// which is the union of all the possible errors.
/// However, we define some refined types to implement the spec error codes as subsets
/// of this low-level error-code. Below is the refinement for [ds_error_code].
[@@ noextract_to "Karamel"] inline_for_extraction noextract
type ds_error_code_or_success =
  e:error_code{
    (**) let _ = allow_inversion error_code in
    match e with
    | CSuccess
    | CIncorrect_transition
    | CPremessage
    | CNo_key
    | CAlready_key
    | CRs_rejected_by_policy
    | CRs_not_certified
    | CAlready_peer
    | CPeer_conflict
    | CUnknown_peer_id
    | CInput_size
    | CDH_error
    | CDecrypt_error
    | CSaturated_nonce -> True
    | CEphemeral_generation -> False
    | CSecurity_level -> False
  }

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type ds_error_code =
  e:ds_error_code_or_success{e <> CSuccess}

[@@ noextract_to "Karamel"] noextract
let ds_error_code_v (e : s_error_code) : Spec.ds_error =
  match e with
  | CIncorrect_transition -> Incorrect_transition
  | CPremessage -> Premessage
  | CNo_key -> Spec.No_key
  | CAlready_key -> Spec.Already_key
  | CRs_rejected_by_policy -> Rs_rejected_by_policy
  | CRs_not_certified -> Rs_not_certified
  | CAlready_peer -> Already_peer
  | CPeer_conflict -> Peer_conflict
  | CUnknown_peer_id -> Unknown_peer_id
  | CInput_size -> Spec.Input_size
  | CDH_error -> Spec.DH_error
  | CDecrypt_error -> Spec.Decryption
  | CSaturated_nonce -> Spec.Saturated_nonce

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let ds_result_code a = result a ds_error_code

(*** Configuration *)

[@@ (strict_on_arguments [1]); noextract_to "Karamel"]
inline_for_extraction noextract
let idc_get_ks (idc : valid_idc) (initiator : bool) :
  key_slots =
  key_slots_from_pattern initiator (idc_get_pattern idc)

[@@ (strict_on_arguments [1]); noextract_to "Karamel"]
inline_for_extraction noextract
val idc_get_isc (idc : valid_idc) (initiator : bool) :
  isc:valid_isc initiator{
   isc_get_nc isc == idc_get_nc idc /\
   isc_get_sc isc == dconfig_to_sconfig (idc_get_dc idc) /\
   isc_get_pattern isc == idc_get_pattern idc /\
   isc_get_ks isc == idc_get_ks idc initiator
  }

val idc_get_resp_isc_is_valid (idc : valid_idc) :
  Lemma(resp_isc_is_valid (idc_get_isc idc true) (idc_get_isc idc false))

[@@ (strict_on_arguments [1]); noextract_to "Karamel"]
inline_for_extraction noextract
val idc_get_validate (idc : valid_idc) (initiator : bool) :
  isc_validate (idc_get_isc idc initiator)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_init_isc (idc : valid_idc) : valid_init_isc = idc_get_isc idc true
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_resp_isc (idc : valid_idc) : valid_resp_isc (idc_get_init_isc idc) =
  (**) idc_get_resp_isc_is_valid idc;
  idc_get_isc idc false

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_send (idc : valid_idc) (initiator : bool) : Tot bool =
  isc_get_send (idc_get_isc idc initiator)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_receive (idc : valid_idc) (initiator : bool) : Tot bool =
  isc_get_receive (idc_get_isc idc initiator)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type sprivate_key_t (idc : valid_idc) (initiator : bool) =
  private_key_t_or_unit (idc_get_nc idc) (isc_get_s (idc_get_isc idc initiator))
[@@ noextract_to "Karamel"] inline_for_extraction noextract
type spublic_key_t (idc : valid_idc) (initiator : bool)  =
  public_key_t_or_unit (idc_get_nc idc) (isc_get_s (idc_get_isc idc initiator))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type eprivate_key_t (idc : valid_idc) (initiator : bool) =
  private_key_t_or_unit (idc_get_nc idc) (isc_get_e (idc_get_isc idc initiator))
[@@ noextract_to "Karamel"] inline_for_extraction noextract
type epublic_key_t (idc : valid_idc) (initiator : bool) =
  public_key_t_or_unit (idc_get_nc idc) (isc_get_e (idc_get_isc idc initiator))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type rspublic_key_t (idc : valid_idc) (initiator : bool) =
  public_key_t_or_unit (idc_get_nc idc) (isc_get_rs (idc_get_isc idc initiator))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_id_t (idc : valid_idc) = state_id_t idc
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let dstate_id_v (#idc : valid_idc) = fun (id : dstate_id_t idc) -> state_id_v #idc id

(*** DState *)
(**** Definitions *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t : valid_idc -> Type0

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_p_or_null (idc : valid_idc) : Type0

[@@ noextract_to "Karamel"] noextract
val dstate_p_g_is_null (#idc : valid_idc) (stp : dstate_p_or_null idc) : GTot bool

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_p (idc : valid_idc) =
  dsp:dstate_p_or_null idc{not (dstate_p_g_is_null dsp)}

[@@ noextract_to "Karamel"] noextract
type dstate_s (idc : valid_idc) = dstate (idc_get_dc idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_null (idc : valid_idc) : stp:dstate_p_or_null idc{dstate_p_g_is_null stp}

[@@ noextract_to "Karamel"] noextract
val dstate_p_g_get_device (#idc : valid_idc) (h : mem) (dst_p : dstate_p idc) : GTot (device_p idc)

// By providing an access to the state rid and revealing the fact that the
// state footprint is in this region, rather than only providing [state_p_region_of],
// we allow ourselves to write recall lemmas like [dstate_p_recall_region].
[@@ noextract_to "Karamel"] noextract
val dstate_p_rid_of (#idc : valid_idc) (stp : dstate_p idc) :
  GTot HS.rid

[@@ noextract_to "Karamel"] noextract
let dstate_p_region_of (#idc : valid_idc) (stp : dstate_p idc) : GTot B.loc =
  region_to_loc (dstate_p_rid_of stp)

[@@ noextract_to "Karamel"] noextract
let dstate_p_or_null_region_of (#idc : valid_idc) (stp : dstate_p_or_null idc) :
  GTot B.loc =
  if dstate_p_g_is_null stp then B.loc_none
  else region_to_loc (dstate_p_rid_of stp)

[@@ noextract_to "Karamel"] noextract
let dstate_p_region_with_device (#idc : valid_idc) (h : mem) (stp : dstate_p idc) : GTot B.loc =
  B.loc_union (dstate_p_region_of stp)
              (device_p_region_of (dstate_p_g_get_device h stp))

[@@ noextract_to "Karamel"] noextract
let dstate_p_or_null_region_with_device (#idc : valid_idc) (h : mem) (stp : dstate_p_or_null idc) : GTot B.loc =
  if dstate_p_g_is_null stp then B.loc_none
  else dstate_p_region_with_device h stp

[@@ noextract_to "Karamel"] noextract
val dstate_p_v (#idc : valid_idc) (h : mem) (stp : dstate_p idc) : GTot (dstate_s idc)

[@@ noextract_to "Karamel"] noextract
let dstate_p_is_gstuck (#idc : valid_idc) (h : mem) (st : dstate_p idc) :
  GTot bool =  
  let st_v = dstate_p_v h st in
  dstate_is_stuck st_v

[@@ noextract_to "Karamel"] noextract
let dstate_p_g_is_initiator (#idc : valid_idc) (h : mem) (st : dstate_p idc) : GTot bool =
  let st_v = dstate_p_v h st in
  dstate_is_initiator st_v

[@@ noextract_to "Karamel"] noextract
let dstate_p_g_is_handshake (#idc : valid_idc) (h : mem) (st : dstate_p idc) : GTot bool =
  let st_v = dstate_p_v h st in
  dstate_is_handshake st_v

[@@ noextract_to "Karamel"] noextract
let dstate_p_g_is_transport (#idc : valid_idc) (h : mem) (st : dstate_p idc) : GTot bool =
  not (dstate_p_g_is_handshake h st)

[@@ noextract_to "Karamel"] noextract
let dstate_p_g_has_static (#idc : valid_idc) (h : mem) (st : dstate_p idc) : GTot bool =
  let initiator = dstate_p_g_is_initiator h st in
  isc_get_s (idc_get_isc idc initiator)

[@@ noextract_to "Karamel"] noextract
val dstate_p_g_handshake_get_static :
     #idc:valid_idc
  -> h:mem
  -> st:dstate_p idc{dstate_p_g_is_handshake h st}
  -> GTot (
       let initiator = dstate_p_g_is_initiator h st in
       sprivate_key_t idc initiator & spublic_key_t idc initiator)

[@@ noextract_to "Karamel"] noextract
val dstate_p_invariant (#idc : valid_idc) (h : mem) (stp : dstate_p idc) : GTot Type0

[@@ noextract_to "Karamel"] noextract
val dstate_p_live (#idc : valid_idc) (h : mem) (stp : dstate_p_or_null idc) :
  GTot Type0

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_p_is_null (#idc : valid_idc) (stp : dstate_p_or_null idc) :
  Stack bool
  (requires (fun h0 ->
    dstate_p_live h0 stp))
  (ensures (fun h0 b h1 ->
    h0 == h1 /\ b == dstate_p_g_is_null stp))

// Recall lemma for the state region
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_p_recall_region (#idc : valid_idc) (stp : dstate_p idc) :
  Stack unit
  (requires (fun h0 ->
    dstate_p_invariant h0 stp))
  (ensures (
    fun h0 _ h1 ->
    h0 == h1 /\
    // The dstate region is in the current memory (note: doesn't give
    // us that all its locs are in the memory)
    dstate_p_rid_of stp `is_in` get_hmap h1 /\
    // The region is disjoint from the stack (note: gives us that all
    // is locs are disjoint from the stack)
    (is_stack_region (get_tip h0) ==>
     Monotonic.HyperHeap.disjoint (get_tip h1) (dstate_p_rid_of stp))))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_p_is_stuck (#idc : valid_idc) (st : dstate_p idc) :
  Stack bool (requires (fun h0 -> dstate_p_invariant h0 st))
  (ensures (fun h0 b h1 ->
    h1 == h0 /\
    b = dstate_p_is_gstuck h0 st))

[@@ noextract_to "Karamel"] noextract
val device_p_owns_dstate_p
  (#idc : valid_idc) (h : mem) (dvp : device_p idc) (stp : dstate_p idc) : GTot Type0

[@@ noextract_to "Karamel"] noextract
val device_p_owns_dstate_p_lem
  (#idc : valid_idc) (h : mem) (dvp : device_p idc) (stp : dstate_p idc) :
  Lemma
  (requires (device_p_owns_dstate_p h dvp stp))
  (ensures (dstate_p_g_get_device h stp == dvp))
  [SMTPat (device_p_owns_dstate_p h dvp stp)]

[@@ noextract_to "Karamel"] noextract
let dstate_p_or_null_v
  (#idc : valid_idc) (h : mem)
  (stp : dstate_p_or_null idc) :
  GTot (option (dstate_s idc)) =
  if dstate_p_g_is_null stp then None
  else Some (dstate_p_v h stp)

[@@ noextract_to "Karamel"] noextract
let dstate_p_or_null_invariant
  (#idc : valid_idc) (h : mem)
  (stp : dstate_p_or_null idc)
  (dvp  : device_p idc) : GTot Type0 =
  dstate_p_live h stp /\
  begin
  if dstate_p_g_is_null stp then True
  else
    begin
    dstate_p_invariant h stp /\
    device_p_owns_dstate_p h dvp stp
    end
  end

[@@ noextract_to "Karamel"] noextract
val dstate_p_invariant_get_device
  (#idc : valid_idc) (h : mem) (stp : dstate_p idc) :
  Lemma
  (requires (
    dstate_p_invariant h stp))
  (ensures (
    let dvp = dstate_p_g_get_device h stp in
    device_p_invariant h dvp /\
    device_p_owns_dstate_p h dvp stp))

[@@ noextract_to "Karamel"] noextract
let dstate_p_same_device
  (#idc : valid_idc) (stp : dstate_p idc) (h0 h1 : mem) : GTot Type0 =
  let dvp = dstate_p_g_get_device h0 stp in
  device_p_owns_dstate_p h1 dvp stp

[@@ noextract_to "Karamel"] noextract
val dstate_p_invariant_live_lem (#idc : valid_idc) (h : mem) (stp : dstate_p idc) :
  Lemma
  (requires (dstate_p_invariant h stp))
  (ensures (dstate_p_live h stp))
  [SMTPat (dstate_p_invariant h stp)]

/// The first, coarse grain frame lemma. Useless if the device gets modified
/// by adding/removing peers.
[@@ noextract_to "Karamel"] noextract
val dstate_p_frame_invariant :
    #idc:valid_idc
  -> l:B.loc
  -> st:dstate_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    dstate_p_invariant h0 st /\
    B.loc_disjoint l (dstate_p_region_with_device h0 st) /\
    B.modifies l h0 h1))
  (ensures (
    dstate_p_invariant h1 st /\
    dstate_p_v h0 st == dstate_p_v h1 st /\
    dstate_p_region_with_device h1 st == dstate_p_region_with_device h0 st))

/// The finer frame lemma
[@@ noextract_to "Karamel"] noextract
val dstate_p_frame_invariant_update_device
  (#idc : valid_idc) (l : B.loc) (stp : dstate_p idc) (dvp : device_p idc) (h0 h1 : mem) :
  Lemma
  (requires (
    B.loc_disjoint (dstate_p_region_of stp) l /\
    B.modifies l h0 h1 /\
    device_p_only_changed_peers_or_counters dvp h0 h1 /\
    device_p_invariant h1 dvp /\
    dstate_p_invariant h0 stp /\
    device_p_owns_dstate_p h0 dvp stp))
  (ensures (
    dstate_p_invariant h1 stp /\
    dstate_p_v h0 stp == dstate_p_v h1 stp /\
    device_p_owns_dstate_p h1 dvp stp))

/// This lemma frames the invariant in case the modified locs are disjoint
/// from both the state and the device.
[@@ noextract_to "Karamel"] noextract
val dstate_p_or_null_frame_invariant :
     #idc:valid_idc
  -> l:B.loc
  -> stp:dstate_p_or_null idc
  -> dvp:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    dstate_p_or_null_invariant h0 stp dvp /\
    B.loc_disjoint l (dstate_p_or_null_region_with_device h0 stp) /\
    B.modifies l h0 h1))
  (ensures (
    dstate_p_or_null_invariant h1 stp dvp /\
    dstate_p_or_null_v h1 stp == dstate_p_or_null_v h0 stp))

/// This lemma frames the invariant in case the device is modified.
[@@ noextract_to "Karamel"] noextract
val dstate_p_or_null_frame_invariant_update_device :
     #idc:valid_idc
  -> l:B.loc
  -> stp:dstate_p_or_null idc
  -> dvp:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    dstate_p_or_null_invariant h0 stp dvp /\
    B.modifies l h0 h1 /\
    B.loc_disjoint l (dstate_p_or_null_region_of stp) /\
    device_p_only_changed_peers_or_counters dvp h0 h1 /\
    device_p_invariant h1 dvp))
  (ensures (
    dstate_p_or_null_invariant h1 stp dvp /\
    dstate_p_or_null_v h1 stp == dstate_p_or_null_v h0 stp))

// TODO: remove
[@@ noextract_to "Karamel"] noextract
val idc_pattern_length_not_zero (idc : valid_idc) :
  Lemma(List.Tot.length (idc_get_pattern idc).messages > 0)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let send_message_impls (idc : valid_idc) : Type0 =
  send_message_impls (idc_get_init_isc idc) (idc_get_resp_isc idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let receive_message_impls (idc : valid_idc) : Type0 =
  receive_message_impls (idc_get_init_isc idc) (idc_get_resp_isc idc)

[@@ noextract_to "Karamel"] noextract
val dstate_p_g_get_device_disjoint_regions :
     #idc:valid_idc
  -> stp:dstate_p idc
  -> h0:HS.mem ->
  Lemma
  (requires (
    dstate_p_invariant h0 stp))
  (ensures (
    let dvp = dstate_p_g_get_device h0 stp in
    B.loc_disjoint (device_p_region_of dvp) (dstate_p_region_of stp)))
  [SMTPat (dstate_p_invariant h0 stp); SMTPat (dstate_p_g_get_device h0 stp)]

(**** Utilities *)
/// Return the current status.
type status =
| Handshake_read
| Handshake_write
| Transport

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_status (#idc : valid_idc) (dst_p : dstate_p idc) :
  Stack status
  (requires (fun h0 -> dstate_p_invariant h0 dst_p))
  (ensures (fun h0 r h1 ->
    h1 == h0 /\
    begin
    let dst_v = dstate_p_v h0 dst_p in
    match r, dstate_get_status dst_v with
    | Handshake_read, Spec.Noise.API.State.Handshake_receive _
    | Handshake_write, Spec.Noise.API.State.Handshake_send _
    | Transport, Spec.Noise.API.State.Transport -> True
    | _ -> False    
    end))

// Given a payload length, return the length of the next message to receive/send.
// If we are in the handshake phase, it depends on the current step.
// In transport phase, it is always payload_len + aead_tag (note that the state
// can't necessarily send/receive a message).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_compute_next_message_len
  (#idc:valid_idc) (out : B.pointer size_t)
  (dst_p : dstate_p idc) (payload_len : size_t) :
  Stack bool
  (requires (fun h0 ->
    B.live h0 out /\
    dstate_p_invariant h0 dst_p))
  (ensures (fun h0 b h1 ->
    B.(modifies (loc_buffer out) h0 h1) /\
    begin
    let nc = idc_get_config idc in
    let pat = idc_get_pattern idc in
    let dst_v = dstate_p_v h0 dst_p in
    (**) normalize_term_spec(List.Tot.length pat.messages);
    if b then
      match dstate_get_status dst_v with
      | Spec.Noise.API.State.Handshake_receive step
      | Spec.Noise.API.State.Handshake_send step ->
        step < List.Tot.length pat.messages /\
        size_v (B.deref h1 out) =
          size_v payload_len + compute_message_length nc pat step
      | Spec.Noise.API.State.Transport ->
        size_v (B.deref h1 out) = size_v payload_len + aead_tag_vsv
    else True
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_hash (#idc : valid_idc) (out: hash_t (idc_get_nc idc)) (dst : dstate_p idc) :
  Stack unit
  (requires (fun h0 ->
    dstate_p_invariant h0 dst /\
    live h0 out /\
    B.loc_disjoint (loc out) (dstate_p_region_of dst)))
  (ensures (fun h0 _ h1 ->
    B.modifies (loc out) h0 h1 /\
    begin
    let dst_v = dstate_p_v h0 dst in
    as_seq h1 out == dstate_get_hash dst_v
    end))

[@@ noextract_to "Karamel"] noextract
let dstate_p_g_get_id (#idc : valid_idc) (h : mem) (stp : dstate_p idc) : GTot state_id =
  let st_v = dstate_p_v h stp in
  dstate_get_id st_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_get_id_st (idc : valid_idc) =
  stp:dstate_p idc ->
  Stack (dstate_id_t idc)
  (requires (fun h0 -> dstate_p_invariant h0 stp))
  (ensures (fun h0 id h1 ->
    h1 == h0 /\
    dstate_id_v id = dstate_p_g_get_id h0 stp))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_id :
  #idc:valid_idc ->
  dstate_p_get_id_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let dstate_p_g_get_info (#idc : valid_idc) (h : mem) (stp : dstate_p idc) :
  GTot (idc_get_dc idc).dc_info =
  let st_v = dstate_p_v h stp in
  dstate_get_info st_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_get_info_st (idc : valid_idc) =
  // We copy the dstate information to out
  out:info_t idc ->
  stp:dstate_p idc ->
  ST unit
  (requires (fun h0 ->
    info_invariant h0 out /\
    dstate_p_invariant h0 stp /\
    B.(all_disjoint [info_footprint out; dstate_p_region_of stp])))
  (ensures (fun h0 _ h1 ->
    B.(modifies (info_footprint out) h0 h1) /\
    (info_freeable h0 out ==> info_freeable h1 out) /\
    info_invariant h1 out /\
    info_v h1 out == dstate_p_g_get_info h0 stp))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_info :
  #idc:valid_idc ->
  dstate_p_get_info_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let dstate_p_g_get_peer_id_v (#idc : valid_idc) (h : mem) (stp : dstate_p idc) :
  GTot (option peer_id) =
  let st_v = dstate_p_v h stp in
  dstate_get_peer_id st_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_get_peer_id_st (idc : valid_idc) =
  stp:dstate_p idc ->
  Stack (peer_id_opt_t idc)
  (requires (fun h0 ->
    dstate_p_invariant h0 stp))
  (ensures (fun h0 pid h1 ->
    h1 == h0 /\
    peer_id_opt_v pid = dstate_p_g_get_peer_id_v h0 stp))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_peer_id :
  #idc:valid_idc ->
  dstate_p_get_peer_id_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let dstate_p_g_get_peer_info (#idc : valid_idc) (h : mem) (stp : dstate_p idc) :
  GTot (option (idc_get_dc idc).dc_info) =
  let st_v = dstate_p_v h stp in
  dstate_get_peer_info st_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_get_peer_info_st (idc : valid_idc) =
  // We copy the dstate information to out
  out:info_t idc ->
  stp:dstate_p idc ->
  // Will fail if we don't know the remote yet
  ST bool
  (requires (fun h0 ->
    info_invariant h0 out /\
    dstate_p_invariant h0 stp /\
    B.(all_disjoint [info_footprint out; dstate_p_region_of stp])))
  (ensures (fun h0 b h1 ->
    B.(modifies (info_footprint out) h0 h1) /\
    (info_freeable h0 out ==> info_freeable h1 out) /\
    info_invariant h1 out /\
    begin match dstate_p_g_get_peer_info h0 stp with
    | Some pinfo_v -> b /\ info_v h1 out == pinfo_v
    | None -> not b /\ info_v h1 out == info_v h0 out
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_peer_info :
  #idc:valid_idc ->
  dstate_p_get_peer_info_st idc

[@@ noextract_to "Karamel"] noextract
let dstate_p_g_get_static_v (#idc : valid_idc) (h : mem)
  (stp : dstate_p idc{dstate_p_g_is_handshake h stp}) :
  GTot (option (keypair (idc_get_config idc))) =
  let st_v = dstate_p_v h stp in
  dstate_get_static st_v

[@@ noextract_to "Karamel"] noextract
let dstate_p_g_get_remote_static_v (#idc : valid_idc) (h : mem)
  (stp : dstate_p idc{dstate_p_g_is_handshake h stp}) :
  GTot (option (public_key (idc_get_config idc))) =
  let st_v = dstate_p_v h stp in
  dstate_get_remote_static st_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_get_static_priv_st (idc : valid_idc{idc_uses_s idc}) =
  // We copy the dstate static to out
  out:private_key_t (idc_get_nc idc) ->
  stp:dstate_p idc ->
  Stack bool
  (requires (fun h0 ->
    live h0 out /\
    dstate_p_invariant h0 stp /\
    B.all_disjoint [loc out; dstate_p_region_of stp]))
  (ensures (fun h0 b h1 ->
    B.modifies (loc out) h0 h1 /\
    begin if b then
      dstate_p_g_is_handshake h0 stp /\
      Some? (dstate_p_g_get_static_v h0 stp) /\
      as_seq h1 out == (Some?.v (dstate_p_g_get_static_v h0 stp)).priv
    else as_seq h1 out == as_seq h0 out
    end))

(*[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_static_priv :
  #idc:valid_idc{idc_uses_s idc} ->
  dstate_p_get_static_priv_st idc*)

/// Note that the initiator may have a key and not the responder, or the opposite.
/// We thus return a boolean to express success.
[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_get_static_pub_st (idc : valid_idc{idc_uses_s idc}) =
  // We copy the dstate static to out
  out:public_key_t (idc_get_nc idc) ->
  stp:dstate_p idc ->
  Stack bool
  (requires (fun h0 ->
    live h0 out /\
    dstate_p_invariant h0 stp /\
    B.all_disjoint [loc out; dstate_p_region_of stp]))
  (ensures (fun h0 b h1 ->
    B.modifies (loc out) h0 h1 /\
    begin if b then
      dstate_p_g_is_handshake h0 stp /\
      Some? (dstate_p_g_get_static_v h0 stp) /\
      as_seq h1 out == (Some?.v (dstate_p_g_get_static_v h0 stp)).pub
    else as_seq h1 out == as_seq h0 out
    end))

(*[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_static_pub :
  #idc:valid_idc{idc_uses_s idc} ->
  dstate_p_get_static_pub_st idc *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_get_remote_static_st (idc : valid_idc{idc_peers_have_s idc}) =
  // We copy the dstate remote static to out
  out:public_key_t (idc_get_nc idc) ->
  stp:dstate_p idc ->
  // Will fail if the state is not a handshake, or if we haven't received the
  // remote static yet
  Stack bool
  (requires (fun h0 ->
    live h0 out /\
    dstate_p_invariant h0 stp /\
    B.all_disjoint [loc out; dstate_p_region_of stp]))
  (ensures (fun h0 b h1 ->
    B.modifies (loc out) h0 h1 /\
    begin if b then
      dstate_p_g_is_handshake h0 stp /\
      Some? (dstate_p_g_get_remote_static_v h0 stp) /\
      as_seq h1 out == Some?.v (dstate_p_g_get_remote_static_v h0 stp)
    else as_seq h1 out == as_seq h0 out
    end))

(*[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_get_remote_static :
  #idc:valid_idc{idc_peers_have_s idc} ->
  dstate_p_get_remote_static_st idc*)

(*// Extraction helpers which are used to define and extract functions only if they make sense
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let mk_dstate_p_get_static_priv_or_unit :
  #idc:valid_idc ->
  type_or_unit (dstate_p_get_static_priv_st idc) (idc_uses_s idc) =
  fun #idc -> if idc_uses_s idc then mk_dstate_p_get_static_priv #idc else ()

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let mk_dstate_p_get_static_pub_or_unit :
  #idc:valid_idc ->
  type_or_unit (dstate_p_get_static_pub_st idc) (idc_uses_s idc) =
  fun #idc -> if idc_uses_s idc then mk_dstate_p_get_static_pub #idc else () *)

(*[@@ noextract_to "Karamel"] inline_for_extraction noextract
let mk_dstate_p_get_remote_static_or_unit :
  #idc:valid_idc ->
  type_or_unit (dstate_p_get_remote_static_st idc) (idc_peers_have_s idc) =
  fun #idc -> if idc_peers_have_s idc then mk_dstate_p_get_remote_static #idc else ()*)


(**** Create, free *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_create_st (idc : valid_idc) (initiator : bool)=
     r:HS.rid
  -> dvp:device_p idc // TODO: may be none in the future
  -> epriv:eprivate_key_t idc initiator
  -> epub:epublic_key_t idc initiator
  // Note that we don't use [peer_id_t idc] on purpose: the end user, not
  // working in F*, might give 0 as input.
  -> pid:opt_pid_t idc initiator ->
  ST (dstate_p_or_null idc)

  (requires (fun h0 ->
    let pattern = idc_get_pattern idc in

    device_p_invariant h0 dvp /\

    ST.is_eternal_region r /\
    lbuffer_or_unit_live h0 epriv /\
    lbuffer_or_unit_live h0 epub /\

    begin
    let r_loc = region_to_loc r in
    let dv_loc = device_p_region_of dvp in
    let epriv_loc = lbuffer_or_unit_to_loc epriv in
    let epub_loc = lbuffer_or_unit_to_loc epub in
    B.all_disjoint [dv_loc; r_loc; epriv_loc; epub_loc]
    end /\
    get_hash_pre (idc_get_nc idc)))

  (ensures (fun h0 stp h1 ->
    B.(modifies (device_p_region_of dvp) h0 h1) /\
    dstate_p_live h1 stp /\
    device_p_invariant h1 dvp /\
    device_p_get_cstate h1 dvp == device_p_get_cstate h0 dvp /\
    device_p_g_get_static h1 dvp == device_p_g_get_static h0 dvp /\
    device_p_no_removal dvp h0 h1 /\
    begin
    let dv_v = device_p_v h0 dvp in
    let e_v = mk_keypair_from_keys_or_unit #(idc_get_isc idc initiator)
                                           #(isc_get_e (idc_get_isc idc initiator))
                                           h0 epriv epub in
    let pid_v = opt_pid_v pid in
    let res_v = create_dstate dv_v initiator e_v pid_v in
    if not (dstate_p_g_is_null stp) then
      Res? res_v /\
      begin
      let Res (st'_v, dv'_v) = res_v in
      not (dstate_p_g_is_null stp) /\
      dstate_p_invariant h1 stp /\
      dstate_p_g_is_handshake h1 stp /\ // Not sure it is useful
      dstate_p_g_is_initiator h1 stp = initiator /\
      region_includes r (dstate_p_region_of stp) /\
      device_p_owns_dstate_p h1 dvp stp /\
      not (dstate_p_is_gstuck h1 stp) /\
      device_p_v h1 dvp == dv'_v /\
      dstate_p_v h1 stp == st'_v
      end
    else
      device_p_v h1 dvp == device_p_v h0 dvp
    end))

// TODO: investigate why it typechecked while initiator was always set to true
// in the body
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_create :
     #idc:valid_idc
  -> ssi:ss_impls (idc_get_nc idc)
  -> initialize:initialize_handshake_state_st (idc_get_nc idc)
  -> initiator:bool // This parameter is meta
  -> dstate_p_create_st idc initiator

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_p_free_st (idc : valid_idc) =
  stp:dstate_p idc ->
  ST unit
  (requires (fun h0 ->
    dstate_p_invariant h0 stp))
  (ensures (fun h0 res h1 ->
    B.(modifies (dstate_p_region_of stp) h0 h1)))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_free :
     #idc:valid_idc
  -> dstate_p_free_st idc

(**** Handshake *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let state_t_handshake_write_rec_impl (initiator : bool) (idc : valid_idc) =
  Impl.Noise.API.State.StateMachine.state_t_handshake_write_rec_impl
    initiator (idc_get_init_isc idc) (idc_get_resp_isc idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let state_t_handshake_read_rec_impl (initiator : bool) (idc : valid_idc) =
  Impl.Noise.API.State.StateMachine.state_t_handshake_read_rec_impl
    initiator (idc_get_init_isc idc) (idc_get_resp_isc idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let mk_state_t_handshake_write_rec (#idc : valid_idc) (initiator : bool) (impls : send_message_impls idc) :
  state_t_handshake_write_rec_impl initiator idc =
  Impl.Noise.API.State.StateMachine.mk_state_t_handshake_write_rec
    initiator (idc_get_init_isc idc) (idc_get_resp_isc idc) impls

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let mk_state_t_handshake_read_rec (#idc : valid_idc) (initiator : bool) (impls : receive_message_impls idc) :
  state_t_handshake_read_rec_impl initiator idc =
  Impl.Noise.API.State.StateMachine.mk_state_t_handshake_read_rec
    initiator (idc_get_init_isc idc) (idc_get_resp_isc idc) impls

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_handshake_write_st (idc : valid_idc) : Type0

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_p_handshake_write_st (idc : valid_idc) =
     payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  -> st : dstate_p idc
  -> outlen : size_t
  -> out : lbuffer uint8 outlen ->
  ST ds_error_code_or_success
  (requires (fun h0 ->
    dstate_p_invariant h0 st /\
    live h0 payload /\
    live h0 out /\
    begin
    let payload_loc = B.loc_buffer (payload <: buffer uint8) in
    let out_loc = B.loc_buffer (out <: buffer uint8) in
    let state_loc = dstate_p_region_with_device h0 st in
    B.all_disjoint [payload_loc; out_loc; state_loc]
    end /\
    get_aead_pre (idc_get_nc idc) /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))
  (ensures (fun h0 res h1 ->
    B.(modifies (loc_union (dstate_p_region_of st)
                (loc_buffer (out <: buffer uint8))) h0 h1) /\
    dstate_p_invariant h1 st /\
    dstate_p_same_device st h0 h1 /\
    // Adding those for security
    live h1 payload /\ live h1 out /\
    begin
    let st_v0 = dstate_p_v h0 st in
    let payload_v = as_seq h0 payload in
    let res_v = handshake_write payload_v st_v0 in
    match res with
    | CSuccess ->
      Res? res_v /\
      begin
      let Res (out'_v, st1'_v) = res_v in
      dstate_p_v h1 st == st1'_v /\
      as_seq h1 out == out'_v /\
      dstate_p_g_is_handshake h0 st /\
      // If we succeeded, it means the state was not stuck
      not (dstate_p_is_gstuck h0 st)
      end
    | _ ->
      // If we fail in the middle of a handshake message processing,
      // we update the state status so that it becomes stuck and unusable
      (dstate_p_g_is_handshake h0 st ==> dstate_p_is_gstuck h1 st)
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_handshake_write :
     #idc : valid_idc
  -> impl_init : state_t_handshake_write_rec_impl true idc
  -> impl_resp : state_t_handshake_write_rec_impl false idc
  -> split_impl : split_st (idc_get_nc idc)
  -> dstate_p_handshake_write_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_p_handshake_read_st (idc : valid_idc) =
     payload_outlen : size_t
  -> payload_out : lbuffer uint8 payload_outlen
  -> st : dstate_p idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->

  ST ds_error_code_or_success

  (requires (fun h0 ->
    let dvp = dstate_p_g_get_device h0 st in
    let cstate = device_p_get_cstate h0 dvp in  
    dstate_p_invariant h0 st /\
    live h0 payload_out /\
    live h0 input /\
    idc_get_cstate_invariant h0 cstate /\
    begin
    let cstate_loc = idc_get_cstate_footprint cstate in
    let payload_loc = B.loc_buffer (payload_out <: buffer uint8) in
    let input_loc = B.loc_buffer (input <: buffer uint8) in
    let state_loc = dstate_p_region_with_device h0 st in
    B.all_disjoint [cstate_loc; payload_loc; input_loc; state_loc]
    end /\
    get_aead_pre (idc_get_nc idc) /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))

  (ensures (fun h0 res h1 ->
    let dvp = dstate_p_g_get_device h0 st in
    let cstate = device_p_get_cstate h0 dvp in
    let l = B.(loc_union (dstate_p_region_of st)
              (loc_union (device_p_region_of dvp)
                         (loc_buffer (payload_out <: buffer uint8))))
    in
    B.(modifies l h0 h1) /\
    device_p_no_removal dvp h0 h1 /\
    dstate_p_invariant h1 st /\
    // The device invariant is actually given by the state invariant,
    // but we reveal it here
    device_p_invariant h1 dvp /\
    dstate_p_same_device st h0 h1 /\
    // Adding those for security
    live h1 payload_out /\ live h1 input /\
    begin
    let st_v0 = dstate_p_v h0 st in
    let st1_v = dstate_p_v h1 st in
    let input_v = as_seq h0 input in
    let cst_v0 = idc_get_cstate_v h0 cstate in
    let dv_v0 = device_p_v h0 dvp in
    let res_v = handshake_read cst_v0 dv_v0 input_v st_v0 in
    match res with
    | CSuccess ->
      Res? res_v /\
      begin
      let Res (dv_v1, payload'_v, st1'_v) = res_v in
      st1_v == st1'_v /\
      as_seq h1 payload_out == payload'_v /\
      device_p_v h1 dvp == dv_v1 /\
      // If we succeeded, it means the state was not stuck
      not (dstate_p_is_gstuck h0 st)
      end
    | _ ->
      device_p_v h1 dvp == device_p_v h0 dvp /\
      // If we fail in the middle of a handshake message processing,
      // we update the state status so that it becomes stuck and unusable
      (dstate_p_g_is_handshake h0 st ==> dstate_p_is_gstuck h1 st)
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_handshake_read :
     #idc : valid_idc
  -> impl_init : state_t_handshake_read_rec_impl true idc
  -> impl_resp : state_t_handshake_read_rec_impl false idc
  -> split_impl : split_st (idc_get_nc idc)
  -> add_peer : device_p_add_peer_get_st idc
  -> dstate_p_handshake_read_st idc

(**** Transport *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_p_transport_write_st (idc : valid_idc) =
     plen : size_t
  -> p : lbuffer uint8 plen
  -> clen : size_t
  -> c : lbuffer uint8 clen
  -> st:dstate_p idc ->
  Stack ds_error_code_or_success
  (requires (fun h0 ->
    dstate_p_invariant h0 st /\
    live h0 p /\ live h0 c /\

    B.all_disjoint [
      dstate_p_region_with_device h0 st;
      B.loc_buffer (p <: buffer uint8);
      B.loc_buffer (c <: buffer uint8)] /\
    get_aead_pre (idc_get_nc idc)))
  (ensures (fun h0 res h1 ->
    // Note that the modified locations don't include the state device
    let l = B.(loc_union (B.loc_buffer (c <: buffer uint8))
                         (dstate_p_region_of st))
    in
    B.(modifies l h0 h1) /\
    dstate_p_invariant h1 st /\
    dstate_p_same_device st h0 h1 /\
    begin
    let st0_v = dstate_p_v h0 st in
    let p_v = as_seq h0 p in
    let res_v = Spec.transport_write st0_v p_v in
    match res with
    | CSuccess ->
      Res? res_v /\
      begin
      let Res (c_v, st1_v) = res_v in
      dstate_p_v h1 st == st1_v /\
      as_seq h1 c == c_v /\
      // If we succeeded, it means the state was not stuck
      not (dstate_p_is_gstuck h0 st)
      end
    | _ ->
      ((idc_get_send idc (dstate_p_g_is_initiator h0 st) /\
        size_v clen = size_v plen + aead_tag_size) ==> Fail? res_v) /\
      // In case of failure, the state is left unchanged, it is thus safe to reuse it
      (not (dstate_p_is_gstuck h0 st) ==> not (dstate_p_is_gstuck h1 st)) /\
      dstate_p_v h1 st == dstate_p_v h0 st
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_transport_write :
     #idc:valid_idc
  -> encrypt : iaead_encrypt_type (idc_get_nc idc)
  -> dstate_p_transport_write_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_p_transport_read_st (idc : valid_idc) =
     plen : size_t
  -> p : lbuffer uint8 plen
  -> clen : size_t
  -> c : lbuffer uint8 clen
  -> st:dstate_p idc ->
  Stack ds_error_code_or_success
  (requires (fun h0 ->
    dstate_p_invariant h0 st /\
    live h0 p /\ live h0 c /\  
    B.all_disjoint [
      dstate_p_region_with_device h0 st;
      B.loc_buffer (p <: buffer uint8);
      B.loc_buffer (c <: buffer uint8)] /\
    get_aead_pre (idc_get_nc idc)))

  (ensures (fun h0 res h1 ->
    // Note that the modified locations don't include the state device
    let l = B.(loc_union (B.loc_buffer (p <: buffer uint8))
                         (dstate_p_region_of st))
    in
    B.(modifies l h0 h1) /\
    dstate_p_invariant h1 st /\
    dstate_p_same_device st h0 h1 /\
    begin
    let st0_v = dstate_p_v h0 st in
    let c_v = as_seq h0 c in
    let res_v = Spec.transport_read st0_v c_v in
    match res with
    | CSuccess ->
      Res? res_v /\
      begin
      let Res (p_v, st1_v) = res_v in
      dstate_p_v h1 st == st1_v /\
      as_seq h1 p == p_v /\
      // If we succeeded, it means the state was not stuck
      not (dstate_p_is_gstuck h0 st)
      end
    | _ ->
      ((idc_get_receive idc (dstate_p_g_is_initiator h0 st) /\
        size_v clen = size_v plen + aead_tag_size) ==> Fail? res_v) /\
      // In case of failure, the state is left unchanged, it is thus safe to reuse it
      (not (dstate_p_is_gstuck h0 st) ==> not (dstate_p_is_gstuck h1 st)) /\
      dstate_p_v h1 st == dstate_p_v h0 st
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_transport_read :
     #idc:valid_idc
  -> decrypt : iaead_decrypt_type (idc_get_nc idc)
  -> dstate_p_transport_read_st idc

(*** Extraction ***)

inline_for_extraction noextract
noeq type api_functions_impls (idc : valid_idc) = {
  // Initially wanted to have [idc] as a field, but doesn't type for some strange reason
  ssdh : ssdh_impls (idc_get_nc idc);
  send_impls : send_message_impls idc;
  receive_impls : receive_message_impls idc;
}

open Impl.Noise.Extraction

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type api_wf_handshake_pattern = hsk:wfs_handshake_pattern{check_pattern hsk}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let check_api_hs (hsk : wfs_handshake_pattern{normalize_term #bool (check_pattern hsk)}) :
  api_wf_handshake_pattern =
  (**) normalize_term_spec (check_pattern hsk);
  hsk

/// The proper way of using this is to wrap it in an auxiliary function
/// [unit -> idconfig_raw] strict on the first argument, to not expand the
/// body of idc as long as possible during the normalization process (see
/// the comments for Impl.Noise.API.Device.idconfig_raw)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let mk_idc
  (nc : iconfig)
  (pattern : wfs_handshake_pattern{normalize_term #bool (check_pattern pattern)})
  (info : St.stateful_malloc_from_input_clone_copy unit)
  (state_id : id_cl)
  (peer_id : id_cl)
  (policy : stateful_policy_function nc (check_hsk_is_psk pattern))
  (certification : stateful_certification_state nc info.St.smficc_stateful)
  (serialize : bool) :
  Pure valid_idc
  (requires (normalize_term #bool (check_pattern pattern)))
  (ensures (fun _ -> True))
  =
  [@inline_let] let dc : dconfig = {
    dc_nc = get_config nc;
    dc_info = info.St.smficc_stateful.St.t ();
    dc_policy = policy.apply_policy_spec;
    dc_cert_state = certification.cstate.St.t ();
    dc_certification = certification.certify_spec;
    dc_info_to_bytes = info.St.smficc_to_bytes_seq;
  } in
  [@inline_let] let idc = {
    idc_nc = nc;
    idc_dc = dc;
    idc_pattern = pattern;
    idc_sid_cl = state_id;
    idc_pid_cl = peer_id;
    idc_info = info;
    idc_policy = policy;
    idc_cert_state = certification;
    idc_serialize = serialize;
  } in
  (fun () -> idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let mk_send_message_impls
  (idc : valid_idc)
  (ssdhi : ssdh_impls (idc_get_nc idc)) :
  send_message_impls idc =
  Impl.Noise.API.State.StateMachine.mk_send_message_impls
    (with_norm (idc_get_pattern idc))
    (idc_get_init_isc idc) (idc_get_resp_isc idc)
    // I don't understand why we need [convert_type]: the type-checking seems to happen in Z3
    (convert_type ssdhi)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let mk_receive_message_impls
  (idc : valid_idc)
  (ssdhi : ssdh_impls (idc_get_nc idc)) :
  receive_message_impls idc =
  Impl.Noise.API.State.StateMachine.mk_receive_message_impls
    (with_norm (idc_get_pattern idc))
    (idc_get_init_isc idc) (idc_get_resp_isc idc)
    (convert_type ssdhi)
