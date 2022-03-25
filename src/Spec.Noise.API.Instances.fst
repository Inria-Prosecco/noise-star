module Spec.Noise.API.Instances

open Spec.Noise
open Spec.Noise.Instances
open Spec.Noise.API.Device
open Spec.Noise.API.Session
open Spec.Noise.SPatterns
open Lib.Sequence
open Lib.ByteSequence
open Lib.RandomSequence
module S = Impl.Noise.String

#push-options "--z3rlimit 50 --ifuel 0 --fuel 0"

(*** IKpsk2*)
/// Redefining string with more constraints
type string = s:string{
  String.length s <= pow2 31 /\
  (forall (i:nat{i < String.length s}). S.char_v (String.index s i) <= 255)
  }

(** Configuration *)
/// We don't accept any unknown static key
let policy_IKpsk2 : policy_function wgc = fun k -> false

/// For IKpsk2, the certification is useless: as we don't accept any unknown keys,
/// we don't need to certify received keys by using the payload.
let certification_IKpsk2 : certification_function wgc string unit =
  fun () k h -> None

let dconfig_IKpsk2 = {
  dc_nc = wgc;
  dc_info = string;
  dc_info_to_bytes = (fun s -> S.seq_char_to_uint8 (S.string_to_seq s));
  dc_policy = policy_IKpsk2;
  dc_cert_state = unit;
  dc_certification = certification_IKpsk2;
}

(** Device *)
type device_IKpsk2 = device dconfig_IKpsk2

// Will fail if we can't derive a public key from the private key
let create_device_IKpsk2 (prologue : hashable wgc) (info : string)
                         (sk : option aead_key)
                         (static_identity : private_key wgc) :
  option (device_IKpsk2) =
  create_device dconfig_IKpsk2 pattern_IKpsk2 prologue info sk (Some static_identity)

let create_device_from_secret_IKpsk2
  (prologue : hashable wgc) (info : string)
  (sk : aead_key) (static_identity : enc_private_key_with_nonce dconfig_IKpsk2.dc_nc) :
  option (device_IKpsk2) =
  create_device_from_secret dconfig_IKpsk2 pattern_IKpsk2 prologue info sk (Some static_identity)

// The peer identifier is an arbitrary number, as opposed to the peer
// information, which should reflect a "meaningful" identity (usually the peer name).
let lookup_peer_by_id_IKpsk2 = lookup_peer_by_id #dconfig_IKpsk2
let lookup_peer_by_static_IKpsk2 = lookup_peer_by_static #dconfig_IKpsk2

// Calling this function will fail if there is already a peer in the device
// with [remote_static_key]. In the Low* implementation: it will leave the
// device unchanged.
let add_peer_IKpsk2
  (dv : device_IKpsk2) (pname : string) (remote_static_key : public_key wgc)
  (psk : preshared_key) : option (peer_id & device_IKpsk2) =
  add_peer #dconfig_IKpsk2 dv pname (Some remote_static_key) (Some psk)

// Remove a peer designated by its identifier.
// Does nothing if there is no peer with this identifier in the device.
let remove_peer_IKpsk2 = remove_peer #dconfig_IKpsk2

let serialize_device_secret_IKpsk2
  (dv : device_IKpsk2) (peer:peer dconfig_IKpsk2) (entr:entropy) :
  option bytes & entropy =
  serialize_peer_secret #dconfig_IKpsk2 dv peer entr

let serialize_peer_secret_IKpsk2 (dv : device_IKpsk2) (entr:entropy) :
  option bytes & entropy =
  serialize_device_secret #dconfig_IKpsk2 dv entr

let deserialize_device_secret_IKpsk2
  (dv : device_IKpsk2) (peer_name:string) (entr:entropy) (enc_keys : bytes) :
  option (peer dconfig_IKpsk2 & device_IKpsk2) =
  deserialize_peer_secret #dconfig_IKpsk2 dv peer_name true true enc_keys

(** Session *)
type session_IKpsk2 = session dconfig_IKpsk2

// Note that create_session might fail for several reasons
let create_initiator_IKpsk2 (dv : device_IKpsk2) (entr: entropy) (pid : peer_id) :
  sresult (session_IKpsk2 & device_IKpsk2) & entropy =
  create_session dv true entr (Some pid)
let create_responder_IKpsk2 (dv : device_IKpsk2) (entr: entropy) :
  sresult (session_IKpsk2 & device_IKpsk2) & entropy =
  create_session dv false entr None

(** Messages *)
let write_IKpsk2 (payload : encap_message) (sn : session_IKpsk2) =
  write #dconfig_IKpsk2 payload sn

let read_IKpsk2 (dv : device_IKpsk2) (msg : bytes) (sn : session_IKpsk2) =
  read #dconfig_IKpsk2 () dv sn msg

(*** XX*)
/// We may receive unknown keys during the handshake
let policy_XX : policy_function wgc = fun k -> false

/// Certification state for the remote static. We do something very simple
/// for the demo: the payload is just used to perform a lookup in an association
/// list.
/// TODO: implement a more realistic example. Maybe an id to identify a key,
/// and a signed payload?
let cstate_XX = list (bytes & string)

let certification_XX : certification_function wgc string cstate_XX =
  fun cstate k h ->
  let check_payload (p : bytes & string) =
    let h', _ = p in
    if length h' = length h then lbytes_eq #(length h) h' h else false
  in
  match List.Tot.find check_payload cstate with
  | None -> None
  | Some (_, name) -> Some name

let dconfig_XX = {
  dc_nc = wgc;
  dc_info = string;
  dc_info_to_bytes = (fun s -> S.seq_char_to_uint8 (S.string_to_seq s));
  dc_policy = policy_XX;
  dc_cert_state = cstate_XX;
  dc_certification = certification_XX;
}

(** Device *)
type device_XX = device dconfig_XX

// Will fail if we can't derive a public key from the private key
let create_device_XX (prologue : hashable wgc) (info : string)
                     (static_identity : private_key wgc) :
  option (device_XX) =
  create_device dconfig_XX pattern_XX prologue info None (Some static_identity)

let lookup_peer_by_id_XX = lookup_peer_by_id #dconfig_XX
let lookup_peer_by_static_XX = lookup_peer_by_static #dconfig_XX
// In the case of WhatsApp XX, as we exchange the keys during the handshake,
// the add_peer function may be useless.
let add_peer_XX
  (dv : device_XX) (pname : string) (remote_static_key : public_key wgc)
  (psk : preshared_key) : option (peer_id & device_XX) =
  add_peer #dconfig_XX dv pname (Some remote_static_key) (Some psk)
let remove_peer_XX = remove_peer #dconfig_XX

(** Session *)
type session_XX = session dconfig_XX
/// In the case of XX, the initiator learns who the responder is during the handshake,
/// so we don't use any peer id at initialization time.
let create_initiator_XX (dv : device_XX) (entr: entropy) :
  sresult (session_XX & device_XX) & entropy =
  create_session dv true entr None
let create_responder_XX (dv : device_XX) (entr: entropy) :
  sresult (session_XX & device_XX) & entropy =
  create_session dv false entr None

(** Messages *)
let write_XX (payload : encap_message) (sn : session_XX) =
  write #dconfig_XX payload sn

let read_XX (cstate : cstate_XX) (dv : device_XX) (msg : bytes) (sn : session_XX) =
  read #dconfig_XX cstate dv sn msg
