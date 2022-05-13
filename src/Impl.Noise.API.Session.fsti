module Impl.Noise.API.Session

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

open Spec.Noise.API.Device.Definitions

open Spec.Noise.API.Session
module Spec = Spec.Noise.API.Session

open Impl.Noise.Types
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.API.Device
open Impl.Noise.API.State.Base
open Impl.Noise.API.DState
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate
open Spec.Noise
open Spec.Noise.PatternsSecurity
open Spec.Noise.API.MetaInfo

open Lib.RandomSequence
open Lib.RandomBuffer.System

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

// Align the .fst and the .fsti
val _align_fsti : unit

(*** Result codes *)

/// For simplicity, we divide the results into 3 different kinds:
/// * Success
/// * Error: an error happened during the processing, but the state is left
///   unchanged and can be reused. A specific code is also returned to give more
///   information about the error type
/// * Stuck: an error happened, leaving the state in an inconsistant condition.
///   It is thus stuck, and can't be manipulated anymore: the only possible action
///   left is to free it (all the other functions will fail if called with this state).
///   A specific code is also returned to give more information about the error type.
/// Also note that we need 2 bits to encode the tag, and 4 to encode the error code.
/// Because Karamel does things well, the total return result will be 16 bits in
/// memory (i.e.: less than 32 bits), so we don't need to care about using a bit
/// encoding.

#push-options "--__temp_no_proj Impl.Noise.API.Session" // Don't generate projectors
inline_for_extraction
type rcode =
| Success
| Error of error_code
| Stuck of error_code
#pop-options

(*** General Utilities *)

/// The following helper computes the length of a message, without the payload.
/// The total length of message i (starting from 0) is:
/// [> payload_length + compute_message_length ...
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let compute_message_length
  (idc : idconfig)
  (step : nat{step < List.Tot.length (idc_get_pattern idc).messages}) :
  nat =
  Spec.Noise.API.MetaInfo.compute_message_length (idc_get_config idc) (idc_get_pattern idc) step

(*** Session *)
(**** Types and predicates *)
// We reveal this definition just to allow type renaming - for better code generation
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val session_t (idc : valid_idc) : Type0

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val session_p_or_null (idc : valid_idc) : Type0

[@@ noextract_to "Karamel"] noextract
val session_p_g_is_null (#idc : valid_idc) (sn : session_p_or_null idc) : GTot bool

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type session_p (idc : valid_idc) =
  sn:session_p_or_null idc{not (session_p_g_is_null sn)}

[@@ noextract_to "Karamel"] noextract
type session_s (idc : valid_idc) = session (idc_get_dc idc)

[@@ noextract_to "Karamel"] noextract
val session_p_v (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot (session_s idc)

[@@ noextract_to "Karamel"] noextract
val session_p_invariant (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot Type0
[@@ noextract_to "Karamel"] noextract
val session_p_is_gstuck (#idc : valid_idc) (h : mem) (st : session_p idc) : GTot bool

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val session_p_is_stuck (#idc : valid_idc) (st : session_p idc) :
  Stack bool (requires (fun h0 -> session_p_invariant h0 st))
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    b = session_p_is_gstuck h0 st))

[@@ noextract_to "Karamel"] noextract
val session_p_live (#idc : valid_idc) (h : mem) (sn : session_p_or_null idc) :
  GTot Type0

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val session_p_is_null (#idc : valid_idc) (sn : session_p_or_null idc) :
  Stack bool
  (requires (fun h0 ->
    session_p_live h0 sn))
  (ensures (fun h0 b h1 ->
    h0 == h1 /\ b == session_p_g_is_null sn))

[@@ noextract_to "Karamel"] noextract
val session_p_g_get_device (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot (device_p idc)

[@@ noextract_to "Karamel"] noextract
val session_p_rid_of (#idc : valid_idc) (sn : session_p idc) : GTot HS.rid

[@@ noextract_to "Karamel"] noextract
let session_p_region_of (#idc : valid_idc) (sn : session_p idc) : GTot B.loc =
  region_to_loc (session_p_rid_of sn)

[@@ noextract_to "Karamel"] noextract
let session_p_or_null_region_of (#idc : valid_idc) (sn : session_p_or_null idc) : GTot B.loc =
  if session_p_g_is_null sn then B.loc_none
  else session_p_region_of sn

[@@ noextract_to "Karamel"] noextract
let session_p_region_with_device (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot B.loc =
  B.loc_union (session_p_region_of sn)
              (device_p_region_of (session_p_g_get_device h sn))

[@@ noextract_to "Karamel"] noextract
let session_p_or_null_region_with_device (#idc : valid_idc) (h : mem) (sn : session_p_or_null idc) :
  GTot B.loc =
  if session_p_g_is_null sn then B.loc_none
  else session_p_region_with_device h sn

[@@ noextract_to "Karamel"] noextract
let session_p_g_is_initiator (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot bool =
  let sn_v = session_p_v h sn in
  session_is_initiator sn_v

[@@ noextract_to "Karamel"] noextract
let session_p_g_is_handshake (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot bool =
  let sn_v = session_p_v h sn in
  session_is_handshake sn_v

[@@ noextract_to "Karamel"] noextract
let session_p_g_is_transport (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot bool =
  not (session_p_g_is_handshake h sn)

[@@ noextract_to "Karamel"] noextract
val device_p_owns_session_p
  (#idc : valid_idc) (h : mem) (dvp : device_p idc) (sn : session_p idc) : GTot Type0

[@@ noextract_to "Karamel"] noextract
val device_p_owns_session_p_lem
  (#idc : valid_idc) (h : mem) (dvp : device_p idc) (sn : session_p idc) :
  Lemma
  (requires (device_p_owns_session_p h dvp sn))
  (ensures (session_p_g_get_device h sn == dvp))
  [SMTPat (device_p_owns_session_p h dvp sn)]

[@@ noextract_to "Karamel"] noextract
val session_p_invariant_live_lem (#idc : valid_idc) (h : mem) (sn : session_p idc) :
  Lemma
  (requires (session_p_invariant h sn))
  (ensures (session_p_live h sn))
  [SMTPat (session_p_invariant h sn)]

[@@ noextract_to "Karamel"] noextract
let session_p_or_null_v
  (#idc : valid_idc) (h : mem)
  (sn : session_p_or_null idc) :
  GTot (option (session_s idc)) =
  if session_p_g_is_null sn then None
  else Some (session_p_v h sn)

/// In order to make the SMT patterns work smoothly, we will consistently use
/// [session_p_or_null_invariant] in the post-conditions, rather than the more
/// specific [session_p_invariant]. As the patterns are written in a forward style,
/// we will however use [session_p_invariant] in the preconditions, whenever possible.
[@@ noextract_to "Karamel"] noextract
let session_p_or_null_invariant
  (#idc : valid_idc) (h : mem)
  (sn : session_p_or_null idc)
  (dvp  : device_p idc) : GTot Type0 =
  session_p_live h sn /\
  begin
  if session_p_g_is_null sn then True
  else
    begin
    session_p_invariant h sn /\
    device_p_owns_session_p h dvp sn
    end
  end

/// The frame lemmas
/// We start by lemmas about [session_p_frame_invariant], then give the equivalent
/// lemmas for [session_p_or_null_invariant]. In practice, we will use the latter
/// ones, which is why only those have SMT patterns.

/// The first, coarse grain frame lemma. Useless if the device gets modified
/// by adding/removing peers.
[@@ noextract_to "Karamel"] noextract
val session_p_frame_invariant :
     #idc:valid_idc
  -> l:B.loc
  -> sn:session_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    session_p_invariant h0 sn /\
    B.loc_disjoint l (session_p_region_with_device h0 sn) /\
    B.modifies l h0 h1))
  (ensures (
    session_p_invariant h1 sn /\
    session_p_v h0 sn == session_p_v h1 sn /\
    session_p_region_with_device h1 sn == session_p_region_with_device h0 sn))

/// The finer frame lemma
[@@ noextract_to "Karamel"] noextract
val session_p_frame_invariant_update_device
  (#idc : valid_idc) (l : B.loc) (sn : session_p idc) (dvp : device_p idc) (h0 h1 : mem) :
  Lemma
  (requires (
    B.loc_disjoint (session_p_region_of sn) l /\
    B.modifies l h0 h1 /\
    device_p_only_changed_peers_or_counters dvp h0 h1 /\
    device_p_invariant h1 dvp /\
    session_p_invariant h0 sn /\
    device_p_owns_session_p h0 dvp sn))
  (ensures (
    session_p_invariant h1 sn /\
    session_p_v h0 sn == session_p_v h1 sn /\
    device_p_owns_session_p h1 dvp sn))

/// This lemma frames the invariant in case the modified locs are disjoint
/// from both the session and the device. The SMT patterns were carefully
/// tested.
[@@ noextract_to "Karamel"] noextract
val session_p_or_null_frame_invariant :
     #idc:valid_idc
  -> l:B.loc
  -> sn:session_p_or_null idc
  -> dvp:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    session_p_or_null_invariant h0 sn dvp /\
    B.loc_disjoint l (session_p_or_null_region_with_device h0 sn) /\
    B.modifies l h0 h1))
  (ensures (
    session_p_or_null_invariant h1 sn dvp /\
    session_p_or_null_v h1 sn == session_p_or_null_v h0 sn))
  [SMTPat (session_p_or_null_invariant h0 sn dvp);
   SMTPat (B.modifies l h0 h1)]

/// This lemma frames the invariant in case the device is modified.
[@@ noextract_to "Karamel"] noextract
val session_p_or_null_frame_invariant_update_device :
     #idc:valid_idc
  -> l:B.loc
  -> sn:session_p_or_null idc
  -> dvp:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    session_p_or_null_invariant h0 sn dvp /\
    B.modifies l h0 h1 /\
    B.loc_disjoint l (session_p_or_null_region_of sn) /\
    device_p_only_changed_peers_or_counters dvp h0 h1 /\
    device_p_invariant h1 dvp))
  (ensures (
    session_p_or_null_invariant h1 sn dvp /\
    session_p_or_null_v h1 sn == session_p_or_null_v h0 sn))
  [SMTPat (session_p_or_null_invariant h0 sn dvp);
   SMTPat (B.modifies l h0 h1);
   SMTPat (device_p_only_changed_peers_or_counters dvp h0 h1);
   SMTPat (device_p_invariant h1 dvp)]

[@@ noextract_to "Karamel"] noextract
val session_p_g_get_device_disjoint_regions :
     #idc:valid_idc
  -> sn:session_p idc
  -> h0:HS.mem ->
  Lemma
  (requires (
    session_p_invariant h0 sn))
  (ensures (
    let dvp = session_p_g_get_device h0 sn in
    B.loc_disjoint (device_p_region_of dvp) (session_p_region_of sn)))
  [SMTPat (session_p_invariant h0 sn); SMTPat (session_p_g_get_device h0 sn)]

// Recall lemma for the session region
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val session_p_recall_region (#idc : valid_idc) (sn : session_p idc) :
  Stack unit
  (requires (fun h0 ->
    is_stack_region (get_tip h0) /\
    session_p_invariant h0 sn))
  (ensures (
    fun h0 _ h1 ->
    h0 == h1 /\
    h0 == h1 /\
    // The session region is in the current memory (note: doesn't give
    // us that all its locs are in the memory)
    session_p_rid_of sn `is_in` get_hmap h1 /\
    // The region is disjoint from the stack (note: gives us that all
    // is locs are disjoint from the stack)
    (is_stack_region (get_tip h0) ==>
     Monotonic.HyperHeap.disjoint (get_tip h1) (session_p_rid_of sn))))

(**** Session utilities *)
[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_get_status_st (idc : valid_idc) =
  sn : session_p idc ->
  Stack status
  (requires (fun h0 -> session_p_invariant h0 sn))
  (ensures (fun h0 r h1 ->
    h1 == h0 /\
    begin
    let sn_v = session_p_v h0 sn in
    match r, session_get_status sn_v with
    | Handshake_read, Spec.Noise.API.State.Handshake_receive _
    | Handshake_write, Spec.Noise.API.State.Handshake_send _
    | Transport, Spec.Noise.API.State.Transport -> True
    | _ -> False    
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_get_status :
  #idc : valid_idc ->
  session_p_get_status_st idc

// Given a payload length, return the length of the next message to receive/send.
// If we are in the handshake phase, it depends on the current step.
// In transport phase, it is always payload_len + aead_tag (note that the state
// can't necessarily send/receive a message).
[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_compute_next_message_len_st (idc : valid_idc) =
     out : B.pointer size_t
  -> sn : session_p idc
  -> payload_len : size_t ->
  Stack bool
  (requires (fun h0 ->
    B.live h0 out /\
    session_p_invariant h0 sn))
  (ensures (fun h0 b h1 ->
    B.(modifies (loc_buffer out) h0 h1) /\
    begin
    let pat = idc_get_pattern idc in
    let sn_v = session_p_v h0 sn in
    if b then
      match session_get_status sn_v with
      | Spec.Noise.API.State.Handshake_receive step
      | Spec.Noise.API.State.Handshake_send step ->
        step < List.Tot.length pat.messages /\
        size_v (B.deref h1 out) =
          size_v payload_len + compute_message_length idc step
      | Spec.Noise.API.State.Transport ->
        size_v (B.deref h1 out) = size_v payload_len + aead_tag_vsv
    else True
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_compute_next_message_len :
  #idc:valid_idc ->
  session_p_compute_next_message_len_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_get_hash_st (idc : valid_idc) =
     out: hash_t (idc_get_nc idc)
  -> sn : session_p idc ->
  Stack unit
  (requires (fun h0 ->
    session_p_invariant h0 sn /\
    live h0 out /\
    B.loc_disjoint (loc out) (session_p_region_of sn)))
  (ensures (fun h0 _ h1 ->
    B.modifies (loc out) h0 h1 /\
    begin
    let sn_v = session_p_v h0 sn in
    as_seq h1 out == session_get_hash sn_v
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_get_hash :
     #idc : valid_idc
  -> session_p_get_hash_st idc

[@@ noextract_to "Karamel"] noextract
let session_p_g_get_id (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot state_id =
  let sn_v = session_p_v h sn in
  session_get_id sn_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_get_id_st (idc : valid_idc) =
  sn:session_p idc ->
  Stack (session_id_t idc)
  (requires (fun h0 -> session_p_invariant h0 sn))
  (ensures (fun h0 id h1 ->
    h1 == h0 /\
    session_id_v id = session_p_g_get_id h0 sn))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_get_id :
  #idc:valid_idc ->
  session_p_get_id_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let session_p_g_get_info (#idc : valid_idc) (h : mem) (sn : session_p idc) :
  GTot (idc_get_dc idc).dc_info =
  let sn_v = session_p_v h sn in
  session_get_info sn_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_get_info_st (idc : valid_idc) =
  // We copy the session information to out
  out:info_t idc ->
  sn:session_p idc ->
  ST unit
  (requires (fun h0 ->
    info_invariant h0 out /\
    session_p_invariant h0 sn /\
    B.(all_disjoint [info_footprint out; session_p_region_of sn])))
  (ensures (fun h0 _ h1 ->
    B.(modifies (info_footprint out) h0 h1) /\
    (info_freeable h0 out ==> info_freeable h1 out) /\
    info_invariant h1 out /\
    info_v h1 out == session_p_g_get_info h0 sn))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_get_info :
  #idc:valid_idc ->
  session_p_get_info_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let session_p_g_get_peer_id_v (#idc : valid_idc) (h : mem) (sn : session_p idc) :
  GTot (option peer_id) =
  let sn_v = session_p_v h sn in
  session_get_peer_id sn_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_get_peer_id_st (idc : valid_idc) =
  sn:session_p idc ->
  Stack (peer_id_opt_t idc)
  (requires (fun h0 ->
    session_p_invariant h0 sn))
  (ensures (fun h0 pid h1 ->
    h1 == h0 /\
    peer_id_opt_v pid = session_p_g_get_peer_id_v h0 sn))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_get_peer_id :
  #idc:valid_idc ->
  session_p_get_peer_id_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let session_p_g_get_peer_info (#idc : valid_idc) (h : mem) (sn : session_p idc) :
  GTot (option (idc_get_dc idc).dc_info) =
  let sn_v = session_p_v h sn in
  session_get_peer_info sn_v

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_get_peer_info_st (idc : valid_idc) =
  // We copy the session information to out
  out:info_t idc ->
  sn:session_p idc ->
  // Will fail if we don't know the remote yet
  ST bool
  (requires (fun h0 ->
    info_invariant h0 out /\
    session_p_invariant h0 sn /\
    B.(all_disjoint [info_footprint out; session_p_region_of sn])))
  (ensures (fun h0 b h1 ->
    B.(modifies (info_footprint out) h0 h1) /\
    (info_freeable h0 out ==> info_freeable h1 out) /\
    info_invariant h1 out /\
    begin match session_p_g_get_peer_info h0 sn with
    | Some pinfo_v -> b /\ info_v h1 out == pinfo_v
    | None -> not b /\ info_v h1 out == info_v h0 out
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_get_peer_info :
  #idc:valid_idc ->
  session_p_get_peer_info_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_reached_max_security_st (idc : valid_idc) =
  sn:session_p idc ->
  Stack bool
  (requires (fun h0 ->
    session_p_invariant h0 sn))
  (ensures (fun h0 b h1 ->
    h1 == h0 /\
    b == session_reached_max_security (session_p_v h0 sn)))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_reached_max_security :
  #idc:valid_idc ->
  session_p_reached_max_security_st idc


(**** Encapsulated messages *)

type conf_level_t = s:UInt8.t{UInt8.v s <= max_conf_level}
type auth_level_t = s:UInt8.t{UInt8.v s <= max_auth_level}

[@CMacro] let auth_zero : auth_level_t = UInt8.uint_to_t 0
[@CMacro] let auth_known_sender : auth_level_t = UInt8.uint_to_t 1
[@CMacro] let auth_known_sender_no_kci : auth_level_t = UInt8.uint_to_t 2
[@CMacro] let max_auth_level : auth_level_t = UInt8.uint_to_t max_auth_level

[@CMacro] let conf_zero : conf_level_t = UInt8.uint_to_t 0
[@CMacro] let conf_known_receiver : conf_level_t = UInt8.uint_to_t 2
[@CMacro] let conf_known_receiver_non_replayable : conf_level_t = UInt8.uint_to_t 3
[@CMacro] let conf_strong_forward_secrecy : conf_level_t = UInt8.uint_to_t 5
[@CMacro] let max_conf_level : conf_level_t = UInt8.uint_to_t max_conf_level

#push-options "--__temp_no_proj Impl.Noise.API.Session" // Don't generate projectors
inline_for_extraction // inline the projectors
type ac_level_t : Type0 =
| Auth_level : l:auth_level_t -> ac_level_t
| Conf_level : l:conf_level_t -> ac_level_t
| No_level : ac_level_t
#pop-options

let ac_level_t_v (lvl : ac_level_t) : GTot ac_level  =
  match lvl with
  | Auth_level l -> Spec.Auth_level (UInt8.v l)
  | Conf_level l -> Spec.Conf_level (UInt8.v l)
  | No_level -> Spec.No_level

val encap_message_p_or_null : Type0

val encap_message_p_g_is_null (emp : encap_message_p_or_null) : GTot bool
val encap_message_p_live (h : HS.mem) (emp : encap_message_p_or_null) : GTot Type0
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val encap_message_p_null : (emp:encap_message_p_or_null{encap_message_p_g_is_null emp})
val encap_message_p_null_is_live (h : mem) :
  Lemma(encap_message_p_live h encap_message_p_null)

val encap_message_p_is_null (emp : encap_message_p_or_null) :
  Stack bool
  (requires (fun h0 -> encap_message_p_live h0 emp))
  (ensures (fun h0 b h1 ->
    h1 == h0 /\
    b = encap_message_p_g_is_null emp))

type encap_message_p =
  emp:encap_message_p_or_null{not (encap_message_p_g_is_null emp)}

val encap_message_p_rid_of (emp : encap_message_p) : GTot HS.rid
let encap_message_p_region_of (emp : encap_message_p) : GTot B.loc =
  region_to_loc (encap_message_p_rid_of emp)

let encap_message_p_or_null_region_of (emp : encap_message_p_or_null) : GTot B.loc =
  if encap_message_p_g_is_null emp then B.loc_none
  else region_to_loc (encap_message_p_rid_of emp)

val encap_message_p_invariant (h : HS.mem) (emp : encap_message_p) : GTot Type0

let encap_message_p_or_null_invariant (h : mem) (emp : encap_message_p_or_null) : GTot Type0 =
  encap_message_p_live h emp /\
  begin
  if encap_message_p_g_is_null emp then True
  else encap_message_p_invariant h emp
  end

/// We need SMT patterns for the two types of encapsulated messages (the non-null
/// one and the potentially null one), becaues functions allocating encapsulated
/// messages sometimes never fail, and sometimes can fail (contrary to, say, the
/// functions allocating sessions, for which we always need to check the return
/// value).
val encap_message_p_frame_invariant (l : B.loc) (emp : encap_message_p) (h0 h1 : mem) :
  Lemma
  (requires (
    encap_message_p_invariant h0 emp /\
    B.loc_disjoint l (encap_message_p_region_of emp) /\
    B.modifies l h0 h1))
  (ensures (
    encap_message_p_invariant h1 emp))
  [SMTPat (encap_message_p_invariant h0 emp);
   SMTPat (B.modifies l h0 h1)]

val encap_message_p_or_null_frame_invariant
  (l : B.loc) (emp : encap_message_p_or_null) (h0 h1 : mem) :
  Lemma
  (requires (
    encap_message_p_or_null_invariant h0 emp /\
    B.loc_disjoint l (encap_message_p_or_null_region_of emp) /\
    B.modifies l h0 h1))
  (ensures (
    encap_message_p_or_null_invariant h1 emp))
  [SMTPat (encap_message_p_or_null_invariant h0 emp);
   SMTPat (B.modifies l h0 h1)]

val encap_message_p_invariant_implies_live
  (h : mem) (emp : encap_message_p) :
  Lemma
  (requires (encap_message_p_invariant h emp))
  (ensures (encap_message_p_live h emp))
  [SMTPat (encap_message_p_invariant h emp)]

val encap_message_p_v (h : HS.mem) (emp : encap_message_p) : GTot encap_message

val encap_message_p_free :
  emp:encap_message_p ->
  ST unit
  (requires (fun h0 -> encap_message_p_invariant h0 emp))
  (ensures (fun h0 _ h1 ->
    B.modifies (encap_message_p_region_of emp) h0 h1))

val pack_message_with_conf_level :
     r:HS.rid
  // Actually, the user might give an improver level - but it is ok,
  // because it can only protect the message more: maybe we should
  // reflect it.
  -> requested_conf_level:conf_level_t
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  ST encap_message_p
  (requires (fun h0 ->
    is_eternal_region r /\
    live h0 msg))
  (ensures (fun h0 emp h1 ->
    B.(modifies loc_none h0 h1) /\
    region_includes r (encap_message_p_region_of emp) /\
    encap_message_p_invariant h1 emp /\
    encap_message_p_v h1 emp ==
      Spec.pack_message_with_conf_level (UInt8.v requested_conf_level) (as_seq h0 msg)))

val pack_message :
     r:HS.rid
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  ST encap_message_p
  (requires (fun h0 ->
    is_eternal_region r /\
    live h0 msg))
  (ensures (fun h0 emp h1 ->
    B.(modifies loc_none h0 h1) /\
    region_includes r (encap_message_p_region_of emp) /\
    encap_message_p_invariant h1 emp /\
    encap_message_p_v h1 emp ==
      Spec.pack_message (as_seq h0 msg)))

val unpack_message_with_auth_level :
     r:HS.rid
  -> out_msg_len:B.pointer size_t
  -> out_msg:B.pointer (buffer uint8)
  // Actually, the user might give an improver level - but it is ok,
  // because it can only protect the message more: maybe we should
  // reflect it.
  -> requested_auth_level:auth_level_t
  -> emp:encap_message_p ->
  ST bool
  (requires (fun h0 ->
    is_eternal_region r /\
    B.live h0 out_msg_len /\
    B.live h0 out_msg /\
    encap_message_p_invariant h0 emp /\
    B.(all_disjoint [region_to_loc r; loc_buffer out_msg_len; loc_buffer out_msg;
                     encap_message_p_region_of emp])))
  (ensures (fun h0 res h1 ->
    B.(modifies (loc_union (loc_buffer out_msg_len) (loc_buffer out_msg)) h0 h1) /\
    begin
    match Spec.unpack_message_with_auth_level
            (UInt8.v requested_auth_level) (encap_message_p_v h0 emp) with
    | None ->
      not res /\ B.g_is_null (B.deref h1 out_msg)
    | Some msg_v ->
      let msg_len = B.deref h1 out_msg_len in
      let msg = B.deref h1 out_msg in
      res /\
      B.live h1 msg /\
      B.length msg = UInt32.v msg_len /\
      B.as_seq h1 msg == msg_v /\
      region_includes r (buffer_or_null_loc_addr msg) /\
      buffer_or_null_freeable msg
    end))

val unpack_message :
     r:HS.rid
  -> out_msg_len:B.pointer size_t
  -> out_msg:B.pointer (buffer uint8)
  -> emp:encap_message_p ->
  ST bool
  (requires (fun h0 ->
    is_eternal_region r /\
    B.live h0 out_msg_len /\
    B.live h0 out_msg /\
    encap_message_p_invariant h0 emp /\
    B.(all_disjoint [region_to_loc r; loc_buffer out_msg_len; loc_buffer out_msg;
                     encap_message_p_region_of emp])))
  (ensures (fun h0 res h1 ->
    B.(modifies (loc_union (loc_buffer out_msg_len) (loc_buffer out_msg)) h0 h1) /\
    begin
    match Spec.unpack_message (encap_message_p_v h0 emp) with
    | None -> not res
    | Some msg_v ->
      let msg_len = B.deref h1 out_msg_len in
      let msg = B.deref h1 out_msg in
      res /\
      B.live h1 msg /\
      B.length msg = UInt32.v msg_len /\
      B.as_seq h1 msg == msg_v /\
      region_includes r (buffer_or_null_loc_addr msg) /\
      buffer_or_null_freeable msg
    | _ -> False
    end))

val unsafe_unpack_message :
     r:HS.rid
  -> out_ac_level:B.pointer ac_level_t
  -> out_msg_len:B.pointer size_t
  -> out_msg:B.pointer (buffer uint8)
  -> emp:encap_message_p ->
  ST unit
  (requires (fun h0 ->
    is_eternal_region r /\
    B.live h0 out_ac_level /\
    B.live h0 out_msg_len /\
    B.live h0 out_msg /\
    encap_message_p_invariant h0 emp /\
    B.(all_disjoint [region_to_loc r; loc_buffer out_ac_level;
                     loc_buffer out_msg_len; loc_buffer out_msg;
                     encap_message_p_region_of emp])))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_union (loc_buffer out_ac_level)
                 (loc_union (loc_buffer out_msg_len) (loc_buffer out_msg))) h0 h1) /\
    begin
    let (lvl_v, msg_v) = Spec.unsafe_unpack_message (encap_message_p_v h0 emp) in
    let level = B.deref h1 out_ac_level in
    let msg_len = B.deref h1 out_msg_len in
    let msg = B.deref h1 out_msg in
    B.live h1 msg /\
    B.length msg = UInt32.v msg_len /\
    B.as_seq h1 msg == msg_v /\
    region_includes r (buffer_or_null_loc_addr msg) /\
    buffer_or_null_freeable msg
    end))

(**** Session: create/free *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let session_p_create_post :
     #idc:valid_idc
  -> initiator:bool
  -> r:HS.rid
  -> dvp:device_p idc
  -> pid:opt_pid_t idc initiator
  -> h0:mem
  -> sn:session_p_or_null idc
  -> h1:mem -> GTot Type0 =
  fun #idc initiator r dvp pid h0 sn h1 ->
  B.(modifies (loc_union (device_p_region_of dvp) (Lib.Buffer.loc entropy_p)) h0 h1) /\
  session_p_or_null_invariant h1 sn dvp /\
  device_p_invariant h1 dvp /\
  device_p_get_cstate h1 dvp == device_p_get_cstate h0 dvp /\
  device_p_g_get_static h1 dvp == device_p_g_get_static h0 dvp /\
  device_p_no_removal dvp h0 h1 /\
  begin
  let dv_v = device_p_v h0 dvp in
  let pid_v = opt_pid_v pid in
  let entr0 = B.deref h0 (entropy_p <: B.buffer (G.erased entropy)) in
  let res_v = create_session dv_v initiator entr0 pid_v in
  if not (session_p_g_is_null sn) then
    Res? (fst res_v) /\
    begin
    let Res (sn'_v, dv'_v), entr' = res_v in
    session_p_g_is_handshake h1 sn /\ // Not sure it is useful
    session_p_g_is_initiator h1 sn = initiator /\
    region_includes r (session_p_region_of sn) /\
    device_p_owns_session_p h1 dvp sn /\
    not (session_p_is_gstuck h1 sn) /\
    device_p_v h1 dvp == dv'_v /\
    session_p_v h1 sn == sn'_v /\
    G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr'
    end
  else
    let _, entr' = res_v in
    device_p_v h1 dvp == device_p_v h0 dvp /\
    G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr'
  end

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_create_st (idc : valid_idc) (initiator : bool) =
     r:HS.rid
  -> dvp:device_p idc // TODO: may be none in the future
  -> pid:opt_pid_t idc initiator ->
  ST (session_p_or_null idc)

  (requires (fun h0 ->
    let pattern = idc_get_pattern idc in

    //===================================================================
    // READ THIS:
    // This condition may seem strange but is here on purpose. The entropy
    // pointer is a global pointer, and its liveness is recallable.
    // However, if the user doesn't recall it at the very beginning
    // of his function by using [Lib.Buffer.recall], he might get
    // very strange errors later, which are a bit hard to debug,
    // and which will come from the fact that Z3 won't be able to reason
    // correctly about entropy_p. By adding this precondition and
    // this comment, we allow the user to detect the problem early and
    // without too much headaches.
    B.live h0 (entropy_p <: B.buffer (G.erased entropy)) /\
    //===================================================================

    device_p_invariant h0 dvp /\

    ST.is_eternal_region r /\

    begin
    let r_loc = region_to_loc r in
    let dv_loc = device_p_region_of dvp in
    let entr_loc = Lib.Buffer.loc entropy_p in
    B.all_disjoint [dv_loc; r_loc; entr_loc]
    end /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))

  (ensures (fun h0 sn h1 ->
   session_p_create_post #idc initiator r dvp pid h0 sn h1))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_create :
     #idc:valid_idc
  -> #initiator:bool
  -> ssi:ss_impls (idc_get_nc idc)
  -> initialize:initialize_handshake_state_st (idc_get_nc idc)
  -> session_p_create_st idc initiator

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_free_st (idc : valid_idc) =
  sn:session_p idc ->
  ST unit
  (requires (fun h0 ->
    session_p_invariant h0 sn))
  (ensures (fun h0 res h1 ->
    B.(modifies (session_p_region_of sn) h0 h1)))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_free :
     #idc:valid_idc
  -> session_p_free_st idc

(**** Session: messages *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let session_p_write_pre (idc : valid_idc) :
     payload : encap_message_p
  -> sn : session_p idc
  -> r : HS.rid
  -> out_len : B.pointer size_t
  -> out : B.pointer (buffer uint8)
  -> h0 : mem -> GTot Type0 =
  fun payload sn r out_len out h0 ->
  encap_message_p_invariant h0 payload /\
  session_p_invariant h0 sn /\
  is_eternal_region r /\
  B.live h0 (out_len <: buffer size_t) /\
  B.live h0 (out <: buffer (buffer uint8)) /\
  begin
  let payload_loc = encap_message_p_region_of payload in
  let out_len_loc = B.loc_buffer (out_len <: buffer size_t) in
  let out_loc = B.loc_buffer (out <: buffer (buffer uint8)) in
  let sn_loc = session_p_region_with_device h0 sn in
  let r_loc = region_to_loc r in
  B.all_disjoint [payload_loc; out_len_loc; out_loc; sn_loc; r_loc]
  end /\
  get_aead_pre (idc_get_nc idc) /\
  get_dh_pre (idc_get_nc idc) /\
  get_hash_pre (idc_get_nc idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let session_p_write_post (idc : valid_idc) :
     payload : encap_message_p
  -> sn : session_p idc
  -> r : HS.rid
  -> out_len : B.pointer size_t
  -> out : B.pointer (buffer uint8)
  -> h0 : mem -> res : rcode -> h1 : mem -> GTot Type0 =
  fun payload sn r out_len out h0 res h1 ->
  B.(modifies (loc_union (session_p_region_of sn)
              (loc_union
               (loc_buffer (out_len <: buffer size_t))
               (loc_buffer (out <: buffer (buffer uint8))))) h0 h1) /\
  session_p_or_null_invariant h1 sn (session_p_g_get_device h0 sn) /\
  begin
  let sn_v0 = session_p_v h0 sn in
  let payload_v = encap_message_p_v h0 payload in
  match res, write payload_v sn_v0 with
  | Success, Res (out'_v, sn1'_v) ->
    let out_len = B.deref h1 out_len in
    let out = B.deref h1 out in
    session_p_v h1 sn == sn1'_v /\
    length out == size_v out_len /\
    B.as_seq h1 (out <: buffer uint8) == out'_v /\
    B.live h1 (out <: buffer uint8) /\
    buffer_or_null_freeable out /\
    region_includes r (buffer_or_null_loc_addr out) /\
    // If we succeeded, it means the session was not stuck
    not (session_p_is_gstuck h0 sn)
  | Error _, _ ->
    B.g_is_null ((B.deref h1 out) <: buffer uint8) /\
    // The session is left unchanged
    not (session_p_is_gstuck h1 sn) /\
    session_p_v h1 sn == session_p_v h0 sn
  | Stuck _, _ ->
    B.g_is_null ((B.deref h1 out) <: buffer uint8) /\
    // The session is stuck
    session_p_is_gstuck h1 sn
  | _ -> False
  end

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type session_p_write_st (idc : valid_idc) =
     payload : encap_message_p
  -> sn : session_p idc
  -> r : HS.rid
  -> out_len : B.pointer size_t
  -> out : B.pointer (buffer uint8) ->
  ST rcode
  (requires (fun h0 ->
    session_p_write_pre idc payload sn r out_len out h0))
  (ensures (fun h0 res h1 ->
    session_p_write_post idc payload sn r out_len out h0 res h1))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_write :
     #idc : valid_idc
  -> handshake_write_impl : dstate_p_handshake_write_st idc
  -> transport_write_impl : dstate_p_transport_write_st idc
  -> session_p_write_st idc

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let session_p_read_pre (idc : valid_idc) :
     r : HS.rid
  -> payload_out : B.pointer encap_message_p_or_null
  -> sn : session_p idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem -> GTot Type0 =
  fun r payload_out sn inlen input h0 ->
  let dvp = session_p_g_get_device h0 sn in
  let cstate = device_p_get_cstate h0 dvp in
  is_eternal_region r /\
  session_p_invariant h0 sn /\
  B.live h0 payload_out /\
  live h0 input /\
  idc_get_cstate_invariant h0 cstate /\
  begin
  let cstate_loc = idc_get_cstate_footprint cstate in
  let payload_loc = B.loc_buffer (payload_out <: buffer encap_message_p_or_null) in
  let input_loc = B.loc_buffer (input <: buffer uint8) in
  let sn_loc = session_p_region_with_device h0 sn in
  let r_loc = region_to_loc r in
  B.all_disjoint [cstate_loc; payload_loc; input_loc; sn_loc; r_loc]
  end /\
  get_aead_pre (idc_get_nc idc) /\
  get_dh_pre (idc_get_nc idc) /\
  get_hash_pre (idc_get_nc idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let session_p_read_post (idc : valid_idc) :
     r : HS.rid
  -> payload_out : B.pointer encap_message_p_or_null
  -> sn : session_p idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem -> res : rcode -> h1 : mem -> GTot Type0 =
  fun r payload_out sn inlen input h0 res h1 ->
  let dvp = session_p_g_get_device h0 sn in
  let cstate = device_p_get_cstate h0 dvp in
  let l = B.(loc_union (session_p_region_of sn)
            (loc_union (device_p_region_of dvp)
                       (loc_buffer (payload_out <: buffer encap_message_p_or_null))))
  in
  B.(modifies l h0 h1) /\
  device_p_no_removal dvp h0 h1 /\
  device_p_invariant h1 dvp /\
  session_p_or_null_invariant h1 sn dvp /\
  encap_message_p_or_null_invariant h1 (B.deref h1 payload_out) /\
  region_includes r (encap_message_p_or_null_region_of (B.deref h1 payload_out)) /\
  begin
  let sn_v0 = session_p_v h0 sn in
  let sn1_v = session_p_v h1 sn in
  let input_v = as_seq h0 input in
  let cst_v0 = idc_get_cstate_v h0 cstate in
  let dv_v0 = device_p_v h0 dvp in
  let res_v = read cst_v0 dv_v0 sn_v0 input_v in
  match res, res_v with
  | Success, Res (dv_v1, payload'_v, sn1'_v) ->
    not (encap_message_p_g_is_null (B.deref h1 payload_out)) /\
    sn1_v == sn1'_v /\
    encap_message_p_v h1 (B.deref h1 payload_out) == payload'_v /\
    device_p_v h1 dvp == dv_v1 /\
    // If we succeeded, it means the session was not stuck
    not (session_p_is_gstuck h0 sn)
  | Error _, _ ->
    encap_message_p_g_is_null (B.deref h1 payload_out) /\
    device_p_v h1 dvp == device_p_v h0 dvp /\
    // The session is left unchanged
    not (session_p_is_gstuck h1 sn) /\
    session_p_v h1 sn == session_p_v h0 sn
  | Stuck _, _ ->
    encap_message_p_g_is_null (B.deref h1 payload_out) /\
    device_p_v h1 dvp == device_p_v h0 dvp /\
    // The session is stuck
    session_p_is_gstuck h1 sn
  | _ -> False
  end

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let session_p_read_st (idc : valid_idc) =
     r : HS.rid
  -> payload_out : B.pointer encap_message_p_or_null
  -> sn_p : session_p idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->
  ST rcode
  (requires (fun h0 ->
    session_p_read_pre idc r payload_out sn_p inlen input h0))
  (ensures (fun h0 res h1 ->
    session_p_read_post idc r payload_out sn_p inlen input h0 res h1))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_read :
     #idc : valid_idc
  -> handshake_read_impl : dstate_p_handshake_read_st idc
  -> transport_read_impl : dstate_p_transport_read_st idc
  -> session_p_read_st idc
