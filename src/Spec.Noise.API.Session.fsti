/// An idiot-proof, easy-to-use API.
/// Note that only the states are manipulated differently (and renamed "session":
/// the devices are those from Spec.Noise.API.DState)

module Spec.Noise.API.Session

open Spec.Noise.API.Device.Definitions
module DState = Spec.Noise.API.DState.Definitions
open Spec.Noise.API.DState.Definitions
open Spec.Noise.Base
open Lib.ByteSequence
open FStar.Mul
open FStar.List.Tot
open Spec.Noise.CryptoPrimitives
open Spec.Noise.WellFormedness
open Spec.Noise.AuthConf
open Spec.Noise.PatternsSecurity
open Spec.Noise.SecurityFlags
open Spec.Noise.SPatterns

// We need randomness for the ephemeral keys
open Lib.RandomSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

private val _align_sti : unit

(*** Errors *)

(* All the errors which can happen *)
type serror =
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
| Ephemeral_generation (* Failed to generate an ephemeral key (because of randomness, or because DH failed) *)
| Security_level (* Security requirement not met *)

type sresult (a : Type0) = result a serror

let ds_error_to_serror (e : DState.ds_error) : serror =
  match e with
  | DState.Incorrect_transition -> Incorrect_transition
  | DState.Premessage -> Premessage
  | DState.No_key -> No_key
  | DState.Already_key -> Already_key
  | DState.Rs_rejected_by_policy -> Rs_rejected_by_policy
  | DState.Rs_not_certified -> Rs_not_certified
  | DState.Already_peer -> Already_peer
  | DState.Peer_conflict -> Peer_conflict
  | DState.Unknown_peer_id -> Unknown_peer_id
  | DState.Input_size -> Input_size
  | DState.DH_error -> DH_error
  | DState.Decryption -> Decryption
  | DState.Saturated_nonce -> Saturated_nonce

let ds_result_to_sresult (#a : Type0) (r : ds_result a) : sresult a =
  match r with
  | Res x -> Res x
  | Fail e -> Fail (ds_error_to_serror e)

(*** Encapsulated Messages *)
/// We encapsulate the messages into [sec_message]. When sending a message,
/// we check that its intended security level is smaller or equal to the
/// current payload security level. When reading a received message, we check
/// that its authentication level is greater or equal to the authentication
/// level requested by the reader.

/// Return true if confidentiality level l0 is stronger than (or equal to)
/// level l1.
let clevel_greater_than (l0 l1 : conf_level) : Tot bool =
  (l1 >= 2 && l0 >= l1) ||
  (l1 = 1 && (l0 = l1 || l0 >= 3)) ||
  (l1 = 0)

let alevel_greater_than (l0 l1 : auth_level) : Tot bool =
  l0 >= l1

/// Security levels
type ac_level : Type0 =
| Auth_level : l:auth_level -> ac_level // trustworthiness of a received message
| Conf_level : l:conf_level -> ac_level // confidentiality of a message we want to send
| No_level : ac_level // public message: no level

/// Encapsulated message
val encap_message : Type0

/// We pack messages before sending them
val pack_message_with_conf_level : requested_conf_level:conf_level -> msg:bytes -> encap_message

/// By default, we pack messages with the highest level
let pack_message msg = pack_message_with_conf_level max_conf_level msg

/// The read function returns an encapsulated message which we then unpack
val unpack_message_with_auth_level : requested_auth_level:auth_level -> msg:encap_message -> option bytes

/// By default, we unpack messages with the highest level
let unpack_message msg = unpack_message_with_auth_level max_auth_level msg

/// The messages returned by the write function are public
val unpack_public_message : msg:encap_message -> option bytes

/// Escape hatches
val unsafe_unpack_message : msg:encap_message -> ac_level & bytes

(*** Session *)

val session : dconfig -> Type0
val session_get_pattern : #dc:dconfig -> session dc -> wfs_handshake_pattern
val session_get_status : #dc:dconfig -> session dc -> Spec.Noise.API.State.Definitions.status
val session_is_initiator : #dc:dconfig -> session dc -> Tot bool
val session_is_handshake : #dc:dconfig -> session dc -> Tot bool
let session_is_transport : #dc:dconfig -> session dc -> Tot bool =
  fun #sc sn -> not (session_is_handshake sn)
val session_is_stuck : #dc:dconfig -> session dc -> Tot bool

// Return the session's unique identifier
val session_get_id : #dc:dconfig -> session dc -> Tot session_id

// The session contains the same kind of information as the peers (its name, usually).
// This information comes from the device which was used to create the session.
val session_get_info : #dc:dconfig -> session dc -> dc.dc_info

// Return the peer's unique identifier. Note that the peer may be unknown yet
// (and in some patterns like NN, we never use any peer), in which case it
// returns None.
val session_get_peer_id : #dc:dconfig -> session dc -> Tot (option peer_id)

// The peer information may be none, if we don't know who the peer is yet.
val session_get_peer_info : #dc:dconfig -> session dc -> option dc.dc_info

val session_get_static :
  #dc:dconfig -> sn:session dc{session_is_handshake sn} -> Tot (option (keypair dc.dc_nc))
val session_get_hash : #dc:dconfig -> session dc -> hash dc.dc_nc

// Return true if we have received at least one transport message from the
// remote party (this may increase the security guarantees).
val session_received_transport_message : #dc:dconfig -> session dc -> Tot bool

// Return true if we have reached the max security level we could expect.
// Note that this implies finishing the handshake, and potentially receiving
// at least one transport message from the remote.
val session_reached_max_security : #dc:dconfig -> session dc -> Tot bool


(**** Creation *)
/// Note that we modify the device when creating a new session: the reason is that
/// we need to increment an internal counter.
val create_session :
     #dc:dconfig
  -> dv:device dc
  -> initiator:bool
  -> entr:entropy
  -> opt_pid:option peer_id ->
  Pure (result (session dc & device dc) serror & entropy)
  (requires True)
  (ensures (fun r ->
    match r with
    | Res _, _
    | Fail Ephemeral_generation, _
    | Fail Unknown_peer_id, _
    | Fail Premessage, _ -> True
    | _ -> False))

(**** Read/write *)
/// Note that we merge the handshake functions and the transport functions.
/// The differences between the steps of the protocol are expressed by the
/// security levels.

val write :
     #dc:dconfig
  -> payload:encap_message
  -> sn:session dc ->
  Pure (sresult (bytes & session dc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res _
    | Fail Incorrect_transition
    | Fail No_key
    | Fail Input_size
    | Fail DH_error
    | Fail Saturated_nonce
    | Fail Security_level -> True
    | _ -> False))

val read :
     #dc:dconfig
  -> cst:dc.dc_cert_state
  -> dv:device dc (* we need the device for lookups *)
  -> sn:session dc
  -> cipher:bytes ->
  Pure (sresult (device dc & encap_message & session dc))
  (requires True)
  (ensures (fun r -> True))
