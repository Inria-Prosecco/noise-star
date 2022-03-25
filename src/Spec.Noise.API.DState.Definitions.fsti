module Spec.Noise.API.DState.Definitions

module State = Spec.Noise.API.State.Definitions
open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Spec.Noise.SPatterns
open Lib.ByteSequence
open FStar.Mul
open FStar.List.Tot

open Spec.Noise.API.Device

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** Errors *)
(* All the errors which can happen *)
type ds_error =
| Incorrect_transition (* Id function called while state did not have proper status *)
| Premessage (* Error while processing the premessages *)
| No_key (* Missing key *)
| Already_key (* Key already received *)
| Rs_rejected_by_policy (* Remote static key rejected by the validation policy *)
| Rs_not_certified (* Remote static key rejected by the payload validation function *)
| Already_peer (* We received a remote static while we already know who the remote peer is *)
| Peer_conflict (* Two peers have the same static key *)
| Unknown_peer_id (* Couldn't find a peer in the device *)
| Input_size (* If the input message doesn't have the proper size *)
| DH_error (* A DH operation failed *)
| Decryption (* An authenticated decryption failed *)
| Saturated_nonce (* Nonce is saturated *)

let ds_result (a : Type) = result a ds_error

(*** Configuration *)

/// We need a way to convert a dconfig to an sconfig
noextract
val dconfig_to_sconfig (dc : dconfig) : State.sconfig


(*** DState *)

(* DState identifier - the dstates all have a unique identifier, like the peers *)

val dstate : dconfig -> Type0

val dstate_get_pattern : #dc:dconfig -> dstate dc -> wfs_handshake_pattern
val dstate_get_status : #dc:dconfig -> dstate dc -> State.status
val dstate_is_initiator : #dc:dconfig -> dstate dc -> Tot bool
val dstate_is_handshake : #dc:dconfig -> dstate dc -> Tot bool
let dstate_is_transport : #dc:dconfig -> dstate dc -> Tot bool =
  fun #sc st -> not (dstate_is_handshake st)
val dstate_is_stuck : #dc:dconfig -> dstate dc -> bool

// Return the dstate's unique identifier
val dstate_get_id : #dc:dconfig -> dstate dc -> state_id

// The dstate contains the same kind of information as the peers (its name, usually).
// This information comes from the device which was used to create the dstate.
val dstate_get_info : #dc:dconfig -> dstate dc -> dc.dc_info

// Return the peer's unique identifier. Note that the peer may be unknown yet
// (and in some patterns like NN, we never use any peer), in which case it
// returns None.
val dstate_get_peer_id : #dc:dconfig -> dstate dc -> Tot (option peer_id)

// The peer information may be none, if we don't know who the peer is yet.
val dstate_get_peer_info : #dc:dconfig -> dstate dc -> option dc.dc_info

val dstate_get_static :
     #dc:dconfig
  -> st:dstate dc{dstate_is_handshake st} ->
  Tot (option (keypair dc.dc_nc))

val dstate_get_remote_static :
     #dc:dconfig
  -> st:dstate dc{dstate_is_handshake st} ->
  Tot (option (public_key dc.dc_nc))

val dstate_get_hash : #dc:dconfig -> dstate dc -> hash dc.dc_nc

// Return true if we have received at least one transport message from the
// remote party (this may increase the security guarantees).
val dstate_received_transport_message : #dc:dconfig -> dstate dc -> Tot bool

/// Note that we modify the device when creating a new dstate: the reason is that
/// we need to increment an internal counter.
val create_dstate :
     #dc:dconfig
  -> dv:device dc
  -> initiator:bool
  -> e:option (keypair dc.dc_nc)
  -> opt_pid:option peer_id ->
  Pure (ds_result (dstate dc & device dc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res _ | Fail Unknown_peer_id | Fail Premessage -> True
    | _ -> False))

(** Handshake *)
val handshake_write :
     #dc:dconfig
  -> payload:bytes
  -> st:dstate dc ->
  Pure (ds_result (bytes & dstate dc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res _
    | Fail Incorrect_transition
    | Fail No_key
    | Fail Input_size
    | Fail DH_error
    | Fail Saturated_nonce -> True
    | _ -> False))

val handshake_read :
     #dc:dconfig
  -> cst:dc.dc_cert_state
  -> dv:device dc (* we need the device for lookups *)
  -> msg:bytes
  -> st:dstate dc ->
  Pure (ds_result (device dc & bytes & dstate dc))
  (requires True)
  (ensures (fun r -> True))

(** Transport *)
val transport_write :
     #dc:dconfig
  -> st:dstate dc
  -> msg:bytes ->
  Pure (ds_result (bytes & dstate dc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res _
    | Fail Incorrect_transition | Fail Input_size
    | Fail Saturated_nonce -> True
    | _ -> False))

val transport_read :
     #dc:dconfig
  -> st:dstate dc
  -> cipher:bytes ->
  Pure (ds_result (bytes & dstate dc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res _
    | Fail Incorrect_transition | Fail Input_size
    | Fail Decryption | Fail Saturated_nonce -> True
    | _ -> False))
