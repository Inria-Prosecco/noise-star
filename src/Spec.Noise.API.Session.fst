module Spec.Noise.API.Session

module State = Spec.Noise.API.State.Definitions
module DState = Spec.Noise.API.DState.Definitions
open Spec.Noise.API.State.Definitions
open Spec.Noise.API.Device.Definitions
open Spec.Noise.API.DState.Definitions
friend Spec.Noise.API.State.Definitions
friend Spec.Noise.API.DState.Definitions
open Spec.Noise.CryptoPrimitives
open Spec.Noise.Utils
open Spec.Noise.Base
open Lib.ByteSequence
open Spec.Noise.CryptoPrimitives
open Spec.Noise.WellFormedness
open Spec.Noise.AuthConf
open Spec.Noise.PatternsSecurity
open Spec.Noise.SecurityFlags

open FStar.Mul
open FStar.List.Tot
open Spec.Noise.API.MetaInfo

// We need randomness for the ephemeral keys
open Lib.RandomSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

let _align_sti = ()

(*** Encapsulated messages *)

noeq type encap_message = {
  em_ac_level : ac_level;
  em_message : bytes;
}

/// Helper for internal use only
val pack_message_with_auth_level : alevel:auth_level -> msg:bytes -> encap_message
let pack_message_with_auth_level alevel msg =
  {
    em_ac_level = Auth_level alevel;
    em_message = msg;
  }

/// Helper for internal use only
let pack_message_with_conf_level requested_conf_level msg =
  {
    em_ac_level = Conf_level requested_conf_level;
    em_message = msg;
  }

let unpack_message_with_auth_level requested_auth_level msg =
  let ok =
    // Don't check the security level if the message is empty
    if Seq.length msg.em_message = 0 then true
    else
      match msg.em_ac_level with
      | Auth_level auth_level -> alevel_greater_than auth_level requested_auth_level
      | _ -> false
  in
  if ok then Some msg.em_message
  else None

let unpack_public_message msg =
  match msg.em_ac_level with
  | No_level -> Some msg.em_message
  | _ -> None

let unsafe_unpack_message msg =
  msg.em_ac_level, msg.em_message

(*** Session *)

type session (dc : dconfig) =
  s:dstate dc {
    Some? (ac_levels (dstate_get_pattern s))
}

let session_get_pattern #dc sn = dstate_get_pattern #dc sn
let session_get_status #dc sn = dstate_get_status #dc sn
let session_is_initiator #dc sn = dstate_is_initiator #dc sn
let session_is_handshake #dc sn = dstate_is_handshake #dc sn
let session_is_stuck #dc sn = dstate_is_stuck #dc sn
let session_get_id #dc sn = dstate_get_id #dc sn
let session_get_info #dc sn = dstate_get_info #dc sn
let session_get_peer_id #dc sn = dstate_get_peer_id sn
let session_get_peer_info #dc sn = dstate_get_peer_info #dc sn
let session_get_static #dc sn = dstate_get_static #dc sn
let session_get_hash #dc sn = dstate_get_hash #dc sn
let session_received_transport_message #dc sn = dstate_received_transport_message sn

let session_reached_max_security #dc sn =
  let initiator = session_is_initiator sn in
  let pattern = session_get_pattern sn in
  let num_msgs = length pattern.messages in
  match session_get_status sn with
  | Transport ->
    if num_msgs > 1 then
      // Two ways handshake pattern
      // If we send the last handshake message, we have to wait for a transport
      // message before reaching the maximum level (because otherwise we don't
      // know if the other party was able to finish the handshake).
      if sends_last_handshake initiator pattern then
        session_received_transport_message sn
      else true
    else
      // If one-way: we reach the maximum level once we are in the transport phase
      true
  | _ ->
    // We are still in the middle of the handshake
    false

(**** Create *)

let uses_e (hsk : handshake_pattern) (initiator : bool) : bool =
  let ks = key_slots_from_pattern initiator hsk in
  ks.ks_e

let create_session #dc dv initiator entr opt_pid =
  let hsk = device_get_pattern dv in
  let uses_e = uses_e hsk initiator in
  if uses_e then
    let nc = dc.dc_nc in
    let entr', epriv = crypto_random entr (public_key_size nc) in
    match keypair_from_private #nc epriv with
    | Some e ->
      // We need to perform a match, because the types session and dstate are different
      begin match create_dstate dv initiator (Some e) opt_pid with
      | Fail err -> Fail (ds_error_to_serror err), entr'
      | Res sn -> Res sn, entr'
      end
    | None -> Fail Ephemeral_generation, entr'
  else
    // We need to perform a match, because the types session and dstate are different
    begin match create_dstate dv initiator None opt_pid with
    | Fail err -> Fail (ds_error_to_serror err), entr
    | Res (sn, dv) -> Res (sn, dv), entr
    end

(**** Read/write *)

/// Helpers to check if the security requirements are satisfied.
val write_transport_check_security
  (initiator : bool) (pattern : wfs_handshake_pattern)
  (recv_tpt_msg : bool) (payload : encap_message) : Tot bool
let write_transport_check_security initiator pattern recv_tpt_msg payload =
  // Don't check the security level if the message is empty
  if Seq.length payload.em_message = 0 then true
  else
    let clevel_opt = compute_transport_conf_level initiator pattern recv_tpt_msg in
    match payload.em_ac_level, clevel_opt with
    | Conf_level req_level, Some clevel -> clevel_greater_than clevel req_level
    | _ -> false

val write_handshake_check_security
  (pattern : wfs_handshake_pattern)
  (i : nat{i < length pattern.messages}) (payload : encap_message) : Tot bool
let write_handshake_check_security pattern i payload =
  // Don't check the security level if the message is empty
  if Seq.length payload.em_message = 0 then true
  else
    let ac_levels = Some?.v (ac_levels pattern) in
    let _, clevel = index ac_levels i in
    match payload.em_ac_level with
    | Conf_level req_level -> clevel_greater_than clevel req_level
    | _ -> false

let write #dc payload sn =
  let pattern = session_get_pattern sn in
  match session_get_status sn with
  | Transport ->
    let initiator = session_is_initiator sn in
    let recv_tpt_msg = session_received_transport_message sn in
    if write_transport_check_security initiator pattern recv_tpt_msg payload then
      match transport_write sn payload.em_message with
      | Fail err -> Fail (ds_error_to_serror err)
      | Res (c, sn') -> Res (c, sn')
    else Fail Security_level
  | Handshake_send i ->
    if i < length pattern.messages then
      if write_handshake_check_security pattern i payload then
        match handshake_write payload.em_message sn with
        | Fail err -> Fail (ds_error_to_serror err)
        | Res (c, sn') -> Res (c, sn')
      else Fail Security_level
    else Fail Incorrect_transition // this is actually redundant with the check in handshake_write
  | _ -> Fail Incorrect_transition // this is actually redundant with the check in handshake_write

let read #dc cst dv sn cipher =
  let pattern = session_get_pattern sn in
  let ac_levels = Some?.v (ac_levels pattern) in
  let initiator = session_is_initiator sn in
  let recv_tpt_msg = session_received_transport_message sn in
  match session_get_status sn with
  | Transport ->
    let initiator = session_is_initiator sn in
    let recv_tpt_msg = session_received_transport_message sn in
    let alevel_opt = compute_transport_auth_level initiator pattern in
    begin match alevel_opt with
    | Some alevel ->
      begin match transport_read sn cipher with
      | Fail err -> Fail (ds_error_to_serror err)
      | Res (p, sn') -> Res (dv, pack_message_with_auth_level alevel p, sn')
      end
    | _ -> Fail Security_level // This will actually be guarded by the invariant
    end
  | Handshake_receive i ->
    if i < length pattern.messages then
      let alevel, _ = index ac_levels i in
      begin match handshake_read cst dv cipher sn with
      | Fail err -> Fail (ds_error_to_serror err)
      | Res (dv', p, sn') -> Res (dv', pack_message_with_auth_level alevel p, sn')
      end
    else Fail Incorrect_transition // this is actually redundant with the check in handshake_read
  | _ -> Fail Incorrect_transition // this is actually redundant with the check in handshake_read

