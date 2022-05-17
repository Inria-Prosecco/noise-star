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
open Impl.Noise.String
open Spec.Noise

open Meta.Noise
open Impl.Noise.API.Instances.Common_25519_ChaChaPoly_BLAKE2s

module St = Impl.Noise.Stateful
module T = FStar.Tactics

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// Aligning the .fsti
val _align_fsti : unit

inline_for_extraction noextract
let pattern = pattern_IKpsk2

[@@ T.postprocess_with (fun () -> T.norm [delta; zeta; iota; primops]; T.trefl())]
let num_pattern_messages = List.Tot.length pattern.messages

let _ : squash(List.Tot.length pattern.messages = num_pattern_messages) =
  normalize_term_spec(List.Tot.length pattern.messages)

inline_for_extraction noextract
let use_serialization = true

[@@ noextract_to "krml"] inline_for_extraction noextract
let idc_ : valid_idc =
  mk_idc inc pattern hstring_smficc (uint_id_cl U32) (uint_id_cl U32)
         (false_stateful_policy_function inc (with_onorm (check_hsk_is_psk pattern)))
         (false_certification_state inc hstring_smficc.St.smficc_stateful)
         use_serialization

[@@ (strict_on_arguments [0]); noextract_to "krml"]
inline_for_extraction noextract
let idc () = idc_ ()

(* Some helpers *)
let rcode_is_success (c : rcode) : bool = Success? c
let rcode_is_error (c : rcode) : bool = Error? c
let rcode_is_stuck (c : rcode) : bool = Stuck? c

// Defining some type abbreviations to make the extracted code prettier

[@@ CPrologue
"/*******************************************************************************

An instanciation of the NoiseAPI for the IKpsk2 pattern.

This instanciation uses the following features:
* uint32 for the sessions and peers counters/unique identifiers
* we don't accept unknown remote static keys: all remote keys should have been
  registered in the device by adding the proper peers.
* device/session/peer names are null-terminated strings of ANSI char

*******************************************************************************/
"]
type status = Impl.Noise.API.DState.status
type session_t = session_t idc
type session_p = session_p idc
type device_t = device_t idc
type device_p = device_p idc
type peer_t = peer_t idc
type peer_p = peer_p idc

// Device
[@@ Comment
"  Create a device.
 
  Parameters:
  * `prlg`: Prologue for session initialization
  * `info`: Device name
  * `sk`: (if present) symmetric key used to serialize/deserialize private data
  * `spriv`: (if present) static private key
 
  May fail and return NULL if provided unvalid keys." ]
val device_create : device_p_create_st idc

[@@ Comment
"  Create a device.

  Takes as arguments a symmetric key `sk` for secret data serialization/
  deserialization, and an encrypted static private key `spriv`. The device
  name `info` is used as authentication data to encrypt/decrypt the device
  private key.

  May fail and return NULL if provided unvalid keys." ]
val device_create_from_secret : device_p_create_from_secret_st_or_unit idc

[@@ Comment
"  Free a device.

  Take care to free the device **AFTER** having freed all the sessions created
  from this device." ]
val device_free : device_p_free_st idc

[@@ Comment
"  Encrypt and derialize a device's secret.

  Uses the device symmetric key to encrypt the device's secret key. Uses
  a randomly generated nonce together with the device name as authentication data." ]
val serialize_device_secret : device_p_serialize_device_secret_st_or_unit idc

[@@ Comment
"  Add a peer to the device and return a pointer to the newly created peer.

  May fail and return NULL if the device already contains a peer with the same
  public static key.

  Note that the peer is owned by the device: we don't provide any way of freeing it
  on the user side, and it might be invalidated after a removal operation.
  For this reason, we advise to immediately use the returned pointer (to retrieve
  the peer id for instance), then forget it." ]
val device_add_peer : device_p_add_peer_get_st idc

[@@ Comment
"  Remove a peer designated by its unique identifier." ]
val device_remove_peer : device_p_remove_peer_st idc

[@@ Comment
"  Encrypt and serialize a peer's key(s).

  Uses the device symmetric key to encrypt the peer's key(s). Uses
  a randomly generated nonce together with the peer name as authentication
  data." ]
val serialize_peer_secret : device_p_serialize_peer_secret_st_or_unit idc

[@@ Comment
"  Decrypt and deserialize a peer's secret data and add it to the device." ]
val deserialize_peer_secret : device_p_deserialize_peer_secret_st_or_unit idc

[@@ Comment
"  Lookup a peer by using its unique identifier.

  Return NULL is no peer was found.

  Note that the peer is owned by the device: we don't provide any way of freeing it
  on the user side, and it might be invalidated after a removal operation.
  For this reason, we advise to immediately use the returned pointer (to retrieve
  the peer name, etc.), then forget it." ]
val device_lookup_peer_by_id : device_p_lookup_peer_by_id_st idc

[@@ Comment
"  Lookup a peer by using its static public key.

  Return NULL is no peer was found.

  Note that the peer is owned by the device: we don't provide any way of freeing it
  on the user side, and it might be invalidated after a removal operation.
  For this reason, we advise to immediately use the returned pointer (to retrieve
  the peer name, etc.), then forget it." ]
val device_lookup_peer_by_static : device_p_lookup_peer_by_static_st_or_unit idc

[@@ Comment
"  Copy the peer information to the user provided pointer." ]
val device_get_info : device_p_get_info_st idc

[@@ Comment
"  Return the current value of the sessions counter.

  The device keeps track of the number of sessions created so far, in order
  to give them unique identifiers." ]
val device_get_sessions_counter : device_p_get_sessions_counter_st idc

[@@ Comment
"  Return true if the sessions counter is saturated.

  It is not possible to create any more sessions if the counter is saturated." ]
val device_sessions_counter_is_saturated : device_p_sessions_counter_is_saturated_st idc

[@@ Comment
"  Return the current value of the peers counter.

  The device keeps track of the number of peers created so far, in order
  to give them unique identifiers." ]
val device_get_peers_counter : device_p_get_peers_counter_st idc

[@@ Comment
"  Return true if the peers counter is saturated.

  It is not possible to add any more peers to the device if the counter is saturated." ]
val device_peers_counter_is_saturated : device_p_peers_counter_is_saturated_st idc

[@@ Comment
"  Copy the device static private key to the user provided buffer." ]
val device_get_static_priv : device_p_get_static_priv_st_or_unit idc

[@@ Comment
"  Copy the device static public key to the user provided buffer." ]
val device_get_static_pub : device_p_get_static_pub_st_or_unit idc

// Peer
[@@ Comment
"  Return the unique peer identifier." ]
val peer_get_id : peer_p_get_id_st idc

[@@ Comment
"  Copy the peer information to the user provided pointer." ]
val peer_get_info : peer_p_get_info_st idc

[@@ Comment
"  Copy the peer static public key to the user provided buffer." ]
val peer_get_static : peer_p_get_static_st_or_unit idc

[@@ Comment
"  Copy the peer pre-shared key to the user provided buffer." ]
val peer_get_psk : peer_p_get_psk_st_or_unit idc

// Session
[@@ Comment
"  Create an initiator session.

  May fail and return NULL in case of invalid keys, unknown peer, etc." ]
val session_create_initiator : session_p_create_st idc true

[@@ Comment
"  Create a responder session.

  May fail and return NULL in case of invalid keys, unknown peer, etc." ]
val session_create_responder : session_p_create_st idc false

[@@ Comment
"  Free a session.

  Be sure to free all sessions before freeing the device used to create
  those sessions." ]
val session_free : session_p_free_st idc

[@@ Comment
"  Write a message with the current session.

  If successful, this function will allocate a buffer of the proper length
  in `*out` and will write the length of this buffer in `*out_len`. Note that
  using `out` and `out_len` is always safe: if the function fails, it will set
  `*outlen` to 0 and `*out` to NULL." ]
val session_write : session_p_write_st idc

[@@ Comment
"  Read a message with the current session.

  If successful, this function will allocate a an encapsulated message
  in `*payload_out`. Note that using `payload_out` is always safe: if the
  function fails, it will set `*payload_out` to NULL." ]
val session_read : session_p_read_st idc

[@@ Comment
"  Compute the length of the next message, given a payload length.

  Note that the function may fail, if the length of the message is too long
  for example (though very unlikely). You thus need to check the returned value.

  Also note that the length of the next message is always equal to:
  payload length + a value depending only on the current step." ]
val session_compute_next_message_len : session_p_compute_next_message_len_st idc

[@@ Comment
"  Return the current status." ]
val session_get_status : session_p_get_status_st idc

[@@ Comment
"  Copy the session hash to the user provided buffer.

  Note that the session hash is always public.

  Using the session hash might be pertinent once the session has reached the
  transport phase." ]
val session_get_hash : session_p_get_hash_st idc

[@@ Comment
"  Return the session unique identifier."]
val session_get_id : session_p_get_id_st idc

[@@ Comment
"  Copy the session information to the user provided pointer." ]
val session_get_info : session_p_get_info_st idc

[@@ Comment
"  Return the session's peer unique identifier.

  The remote may be unknown, in which case the returned id will be 0.
  Note that you can safely use the returned peer id without testing
  it, because all the functions taking peer ids as parameters were
  written to correctly manipulate 0. In particular, looking up id 0 will return
  NULL, and trying to create a session with peer id 0 will cleanly fail
  by also returning NULL." ]
val session_get_peer_id : session_p_get_peer_id_st idc

[@@ Comment
"  Copy the session peer information, if known, to the user provided pointer.

  The remote may be unknown yet, in which case there is no peer information
  in the device and the function will return false." ]
val session_get_peer_info : session_p_get_peer_info_st idc

[@@ Comment
"  Return true if this session has reached the maximum security level for this
  pattern.

  Once the maximum security level is reached, it is not possible to have better
  confidentiality/authentication guarantees for the payloads sent/received
  with this session. Note that the guarantees provided by the maximum reachable
  level vary with the pattern, which must thus be carefully chosen.

  In order to reach the maximum level, the session must have finished the
  handshake. Moreover, in case the session sends the last handshake message,
  it must wait for the first transport message from the remote: otherwise,
  we have no way to know whether the remote was itself able to finish the
  handshake." ]
val session_reached_max_security : session_p_reached_max_security_st idc

// The user is not supposed to mix the usage of dstate and session.
// We do it only because dstate_p_create allows us to control the
// ephemeral key (which is otherwise randomly generated) and thus
// gives us an escape hatch for the tests and the benchmarks.
[@@ Comment "  DO NOT use this: for tests and benchmarks only"]
val _session_create_initiator_with_ephemeral : dstate_p_create_st idc true
[@@ Comment "  DO NOT use this: for tests and benchmarks only"]
val _session_create_responder_with_ephemeral : dstate_p_create_st idc false
