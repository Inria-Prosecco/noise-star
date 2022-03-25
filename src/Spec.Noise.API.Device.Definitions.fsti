module Spec.Noise.API.Device.Definitions

module State = Spec.Noise.API.State.Definitions
open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Lib.IntTypes
open Lib.ByteSequence
module BS = Lib.ByteSequence
open FStar.Mul
open FStar.List.Tot
open Spec.Noise.PatternsSecurity
open Spec.Noise.SPatterns
module U8 = FStar.UInt8

// We need randomness for the nonce generation for serialization
open Lib.RandomSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** Configuration *)
/// Signature for policy function: given a remote static public key, do we accept
/// it or not? In practice, will be always true or always false. Note that accepting
/// the key doesn't provide any security guarantees: policies just tell us whether
/// to accept or reject unknown keys. If a key is accepted, it is certified later
/// with the certification function, once the payload has been decrypted.
noextract
type policy_function (nc : config) = public_key nc -> bool

/// Signature for certification functions. After having received a message
/// containing a static key, if the policy doesn't reject the key, we use
/// the payload to certify it (WhatsApp and Slack use a certificate
/// contained by the payload).
noextract
type certification_function (nc : config) (peer_name cert_state : Type0) =
  cert_state -> public_key nc -> hashable nc -> option peer_name

noextract
noeq type dconfig : Type u#1 = {
  dc_nc : config;
  dc_info : Type0; // TODO: rename to dc_name
  // Conversion to bytes. Note that we want the bytes to be usable as
  // authentication data (hence the length condition).
  dc_info_to_bytes : dc_info -> b:bytes{Seq.length b <= pow2 31};
  dc_policy : policy_function dc_nc;
  dc_cert_state : Type0;
  dc_certification : certification_function dc_nc dc_info dc_cert_state;
}

(*** Additional types *)
// Encrypted private key
inline_for_extraction
let enc_private_key_size (nc : config) : size_nat = private_key_size nc + aead_tag_size
type enc_private_key (nc : config) = lbytes (enc_private_key_size nc)

inline_for_extraction
let enc_private_key_with_nonce_size (nc : config) : size_nat =
  enc_private_key_size nc + aead_nonce_size
type enc_private_key_with_nonce (nc : config) = lbytes (enc_private_key_with_nonce_size nc)

// Encrypted public key
inline_for_extraction
let enc_public_key_size (nc : config) : size_nat = public_key_size nc + aead_tag_size
type enc_public_key (nc : config) = lbytes (enc_public_key_size nc)

// Encrypted preshared key
inline_for_extraction
let enc_preshared_key_size : size_nat = preshared_key_size + aead_tag_size
type enc_preshared_key = lbytes enc_preshared_key_size

(*** Peer *)
/// The peers are all uniquely identified by an id.
type identifier = nat
type peer_id = identifier

// TODO: hide raw_peer
val raw_peer (nc : config) (name_ty : Type0) : Type0
let peer (dc : dconfig) = raw_peer dc.dc_nc dc.dc_info
val peer_get_id : #dc:dconfig -> p:peer dc -> peer_id
val peer_get_info : #dc:dconfig -> p:peer dc -> dc.dc_info
val peer_get_static : #dc:dconfig -> p:peer dc -> option (public_key dc.dc_nc)
val peer_get_psk : #dc:dconfig -> p:peer dc -> option preshared_key

(*** Device *)

/// The states generated by the device are all uniquely identified by an id,
/// like the peers
// session_id and state_id are interchangeable - we use one or the other
// depending on the context (state_id for dstate files, session id for
// session files
type state_id = identifier
type session_id = identifier
val device : dconfig -> Type0

/// Not used by dstate but by session: we use wfs_handshake_pattern, and not
/// wf_handshake_pattern, because we need stronger hypotheses on the patterns,
/// to account for security formulae. 
val device_get_pattern : #dc:dconfig -> device dc -> wfs_handshake_pattern
val device_get_peers : #dc:dconfig -> dv:device dc -> list (peer dc)
val device_get_info : #dc:dconfig -> dv:device dc -> dc.dc_info
val device_get_static : #dc:dconfig -> dv:device dc -> (option (keypair dc.dc_nc))
val device_get_states_counter : #dc:dconfig -> dv:device dc -> state_id
let device_get_sessions_counter (#dc:dconfig) (dv:device dc) : state_id =
  device_get_states_counter dv
val device_get_peers_counter : #dc:dconfig -> dv:device dc -> peer_id

(** Device creation *)
/// Create a device
val create_device :
     dc:dconfig
  -> hsk:wfs_handshake_pattern
  -> prologue:hashable dc.dc_nc
  // The device contains the same kind of information as the peers (its name, usually)
  -> info:dc.dc_info
  // We can provide an AEAD key for serialization/deserialization
  -> sk:option aead_key
  -> static_identity:option (private_key dc.dc_nc)
  // Will fail if we can't derive a valid public key from the private key
  -> (option (device dc))

/// Create a device by providing a secret AEAD key and an encrypted
/// static private key. The AEAD key will be used to decrypt the static
/// key and later for serialization/deserialization.
val create_device_from_secret :
     dc:dconfig
  -> hsk:wfs_handshake_pattern
  -> prologue:hashable dc.dc_nc
  -> info:dc.dc_info
  // We always provide a serialization/deserialization key
  -> sk:aead_key
  // The static identity is encrypted
  // TODO: the length of the encrypted static identity should be checked inside?
  -> static_identity:option (enc_private_key_with_nonce dc.dc_nc)
  -> (option (device dc))

(** Lookup *)
val lookup_peer_by_id :
     #dc:dconfig
  -> dv:device dc
  -> id:peer_id ->
  Tot (option (peer dc))

val lookup_peer_by_static :
     #dc:dconfig
  -> dv:device dc
  -> public_key dc.dc_nc ->
  Tot (option (peer dc))

(** Add/remove peer *)
(* Register a peer in the device. The new peer mustn't have the same static
 * key than another peer already in the device, otherwise the function
 * will fail. We don't enforce any conditions on the peer information.
 *)
val add_peer_get :
     #dc:dconfig
  -> dv:device dc
  -> pinfo:dc.dc_info
  -> remote_static_key:option (public_key dc.dc_nc)
  -> psk:option preshared_key
  // Will fail if there is already a peer with remote_static_key in the device
  -> option (peer dc & device dc)

(* Register a peer in the device. Rather than returning the new peer,
 * return its identifier. *)
let add_peer :
     #dc:dconfig
  -> dv:device dc
  -> pinfo:dc.dc_info
  -> remote_static_key:option (public_key dc.dc_nc)
  -> psk:option preshared_key
  // Will fail if there is already a peer with remote_static_key in the device
  -> option (peer_id & device dc) =
  fun #dc dv pinfo remote_static_key psk ->
  match add_peer_get dv pinfo remote_static_key psk with
  | None -> None
  | Some (p, dv) -> Some (peer_get_id p, dv)

(* Remove a peer by using its id. Note that the function can't fail:
 * it just does nothing if no peer has this id *)
val remove_peer :
     #dc:dconfig
  -> dv:device dc
  -> pid:peer_id
  -> device dc

(** Serialization/deserialization and long-term key storage *)

/// Encrypt the device private key by using a random nonce and the device name
/// as authentication data.
val serialize_device_secret :
     #dc:dconfig
  -> dv:device dc
  -> entr:entropy ->
  // Returns: encrypted keys, new entropy
  // Returns None if there is no AEAD key for serialization/deserialization
  option bytes & entropy

/// Serialize a peer's secret data using the device's AEAD key and the peer's
/// name as authentication data.
val serialize_peer_secret :
     #dc:dconfig
  -> dv:device dc
  -> peer:peer dc
  -> entr:entropy ->
  // Returns: encrypted keys, new entropy
  // Returns None if there is no AEAD key for serialization/deserialization
  option bytes & entropy

/// Deserialize a peer and add it to the device.
/// Might fail if the provided data doesn't have the proper length,
/// if the keys can't or if the peer is already in the device.
// TODO: add an informative return type
val deserialize_peer_secret :
     #dc:dconfig
  -> dv:device dc
  -> peer_name:dc.dc_info
  -> rs:bool // Should we extract a static key?
  -> psk:bool // Should we extract a psk?
  -> enc_keys:bytes -> // The encrypted key(s)
  option (peer dc & device dc)
