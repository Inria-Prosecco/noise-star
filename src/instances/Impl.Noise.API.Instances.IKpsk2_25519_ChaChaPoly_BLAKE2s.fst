/// Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s instantiation of the NoiseAPI

module Impl.Noise.API.Instances.IKpsk2_25519_ChaChaPoly_BLAKE2s

open Lib.IntTypes

open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.API.Device
open Impl.Noise.API.DState
open Impl.Noise.API.Session
open Spec.Noise

open Meta.Noise
open Impl.Noise.API.Instances.Common

module St = Impl.Noise.Stateful
module T = FStar.Tactics

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// Aligning the .fsti
let _align_fsti = ()

(** Type abbreviations *)

type init_state_t = Impl.Noise.API.State.state_t (idc_get_init_isc idc) true
type resp_state_t = Impl.Noise.API.State.state_t (idc_get_resp_isc idc) false
type opt_peer_p = option peer_p
type cell = LowStar.Lib.LinkedList.cell peer_p

type result_unit_error = result unit error_code
type result_init_state_t = result init_state_t error_code
type result_resp_state_t = result resp_state_t error_code
type result_session_t = result session_t error_code

(** The functions *)
// Cryptographic functions
inline_for_extraction noextract
let cimpls = ssi_get_prims (ssdhi_get_ssi ssdhi)

let device_create = mk_device_p_create cimpls
let device_create_from_secret = mk_device_p_create_from_secret_or_unit cimpls
let device_free = mk_device_p_free
let serialize_device_secret = mk_device_p_serialize_device_secret_or_unit cimpls
let device_add_peer = mk_device_p_add_peer_get
let device_remove_peer = mk_device_p_remove_peer
let serialize_peer_secret = mk_device_p_serialize_peer_secret_or_unit cimpls
let deserialize_peer_secret = mk_device_p_deserialize_peer_secret_or_unit cimpls

let device_lookup_peer_by_id = mk_device_p_lookup_peer_by_id
let device_lookup_peer_by_static = mk_device_p_lookup_peer_by_static_or_unit

let device_get_info = mk_device_p_get_info
let device_get_sessions_counter = mk_device_p_get_sessions_counter
let device_sessions_counter_is_saturated = mk_device_p_sessions_counter_is_saturated
let device_get_peers_counter = mk_device_p_get_peers_counter
let device_peers_counter_is_saturated = mk_device_p_peers_counter_is_saturated
let device_get_static_priv = mk_device_p_get_static_priv_or_unit
let device_get_static_pub = mk_device_p_get_static_pub_or_unit

let peer_get_id = mk_peer_p_get_id
let peer_get_info = mk_peer_p_get_info
let peer_get_static = mk_peer_p_get_static_or_unit
let peer_get_psk = mk_peer_p_get_psk_or_unit

let session_create_initiator =
  mk_session_p_create (ssdhi_get_ssi ssdhi)
    (initialize_handshake_state_m (ssdhi_get_ssi ssdhi))
let session_create_responder =
  mk_session_p_create (ssdhi_get_ssi ssdhi)
  (initialize_handshake_state_m (ssdhi_get_ssi ssdhi))
let session_free = mk_session_p_free

[@@ (T.postprocess_with (normalize_messages_impl_list)); noextract_to "Kremlin"]
inline_for_extraction noextract
let send_messages = mk_send_message_impls idc ssdhi

[@@ (T.postprocess_with (normalize_messages_impl_list)); noextract_to "Kremlin"]
inline_for_extraction noextract
let receive_messages = mk_receive_message_impls idc ssdhi

[@@ (T.postprocess_with (normalize_read_write_message [`%send_messages; `%receive_messages]));
 noextract_to "Kremlin"]
inline_for_extraction noextract
let state_handshake_init_write_rec =
  mk_state_t_handshake_write_rec true send_messages

[@@ (T.postprocess_with (normalize_read_write_message [`%send_messages; `%receive_messages]));
 noextract_to "Kremlin"]
inline_for_extraction noextract
let state_handshake_resp_write_rec =
  mk_state_t_handshake_write_rec false send_messages

[@@ (T.postprocess_with (normalize_read_write_message [`%send_messages; `%receive_messages]));
 noextract_to "Kremlin"]
inline_for_extraction noextract
let state_handshake_init_read_rec =
  mk_state_t_handshake_read_rec true receive_messages

[@@ (T.postprocess_with (normalize_read_write_message [`%send_messages; `%receive_messages]));
 noextract_to "Kremlin"]
inline_for_extraction noextract
let state_handshake_resp_read_rec =
  mk_state_t_handshake_read_rec false receive_messages

let state_handshake_write =
  mk_dstate_p_handshake_write state_handshake_init_write_rec
                              state_handshake_resp_write_rec
                              (ssi_get_split (ssdhi_get_ssi ssdhi))

let state_handshake_read =
  mk_dstate_p_handshake_read state_handshake_init_read_rec
                             state_handshake_resp_read_rec
                             (ssi_get_split (ssdhi_get_ssi ssdhi))
                             device_add_peer

let state_transport_write : dstate_p_transport_write_st idc =
  mk_dstate_p_transport_write (iaead_encrypt (csi_get_prims (ssi_get_csi (ssdhi_get_ssi ssdhi))))
let state_transport_read : dstate_p_transport_read_st idc =
  mk_dstate_p_transport_read (iaead_decrypt (csi_get_prims (ssi_get_csi (ssdhi_get_ssi ssdhi))))

let session_write = mk_session_p_write state_handshake_write state_transport_write
let session_read = mk_session_p_read state_handshake_read state_transport_read

let session_compute_next_message_len = mk_session_p_compute_next_message_len
let session_get_status = mk_session_p_get_status
let session_get_hash = mk_session_p_get_hash
let session_get_id = mk_session_p_get_id
let session_get_info = mk_session_p_get_info
let session_get_peer_id = mk_session_p_get_peer_id
let session_get_peer_info = mk_session_p_get_peer_info
let session_reached_max_security = mk_session_p_reached_max_security

let _session_create_initiator_with_ephemeral =
  mk_dstate_p_create (ssdhi_get_ssi ssdhi)
    (initialize_handshake_state_m (ssdhi_get_ssi ssdhi)) true
let _session_create_responder_with_ephemeral =
  mk_dstate_p_create (ssdhi_get_ssi ssdhi)
    (initialize_handshake_state_m (ssdhi_get_ssi ssdhi)) false
