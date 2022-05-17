module Spec.Noise.API.State.Definitions

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Lib.ByteSequence

open FStar.Mul
open FStar.List.Tot

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

/// Split a list at the first occurrence of an element
[@(strict_on_arguments [2])]
let rec splitAtFirstElem (#a:eqtype) (x:a) (l:list a) : Tot (list a & list a) =
  match l with
  | [] -> [], []
  | y :: l' ->
    if y = x then [y], l'
    else
      let l1, l2 = splitAtFirstElem x l' in
      y::l1, l2

val splitAtFirstElem_append_lem (#a:eqtype) (x:a) (l:list a) :
  Lemma
  (requires True)
  (ensures (
    let l1, l2 = splitAtFirstElem x l in
    l = append l1 l2))
  (decreases l)  

val splitAtFirstElem_mem_beg (#a:eqtype) (x:a) (l:list a) :
  Lemma (requires (mem x l))
  (ensures (mem x (fst (splitAtFirstElem x l))))

(* State status: handshake step or transport phase *)
type status =
| Handshake_send : i:nat -> status (* waiting to send message i *)
| Handshake_receive : i:nat -> status (* waiting to receive message i *)
| Transport

val internal_state : config -> Type0

noextract
type validation_function (nc : config) (vstate pinfo : Type0) =
  vstate -> public_key nc -> option (pinfo & option preshared_key)

/// Configuration by which a state is parameterized. We use it for several purposes:
/// - it makes clear the fact that, for instance, the configuration or the
///   validation function will not change
/// - by not storing the validation state type in the state itself, we remain in Type0
noextract
noeq type sconfig : Type u#1 = {
  sc_config : config;
  sc_vstate : Type0; // validation state
  sc_pinfo : Type0; // peer information
  sc_validate : validation_function sc_config sc_vstate sc_pinfo;
}

// TODO: the sconfig definition was initially hidden, hence the presence
// of several getters.

[@ (strict_on_arguments [0])]
let sc_get_config (sc : sconfig) : config = sc.sc_config

[@ (strict_on_arguments [0])]
let sc_get_vstate (sc : sconfig) : Type0 = sc.sc_vstate

[@ (strict_on_arguments [0])]
let sc_get_pinfo (sc : sconfig) : Type0 = sc.sc_pinfo

[@ (strict_on_arguments [0])]
let sc_get_validate (sc : sconfig) = sc.sc_validate

val state : sconfig -> Type0

(* Some functions to retrieve information from the state *)
val state_get_pattern : #sc:sconfig -> state sc -> wf_handshake_pattern

[@ (strict_on_arguments [0;1])]
val state_get_status : #sc:sconfig -> state sc -> status

[@ (strict_on_arguments [0;1])]
val internal_state_get_hash : #nc:config -> internal_state nc -> hash nc

[@ (strict_on_arguments [0;1])]
val state_get_internal_state : #sc:sconfig -> state sc -> internal_state (sc_get_config sc)

[@ (strict_on_arguments [0;1])]
let state_get_hash : #sc:sconfig -> state sc -> hash (sc_get_config sc) =
  fun #sc st -> internal_state_get_hash (state_get_internal_state st)
val state_is_initiator : #sc:sconfig -> state sc -> Tot bool
val state_is_handshake : #sc:sconfig -> state sc -> Tot bool
let state_is_transport : #sc:sconfig -> state sc -> Tot bool =
  fun #sc st -> not (state_is_handshake st)
val state_received_transport_message : #sc:sconfig -> state sc -> Tot bool

val state_get_s :
  #sc:sconfig -> st:state sc{state_is_handshake st} -> option (keypair (sc_get_config sc))
val state_get_rs :
  #sc:sconfig -> st:state sc{state_is_handshake st} -> option (public_key (sc_get_config sc))
val state_get_psk :
  #sc:sconfig -> st:state sc{state_is_handshake st} -> option preshared_key

(* All the errors which can happen *)
type s_error =
| Incorrect_transition (* Id function called while state did not have proper status *) // TODO: rename to Invalid_transition
| Premessage (* Error while processing the premessages *)
| No_key (* Missing key *)
| Already_key (* Key already received *)
| Rs_not_valid (* Remote static key was not accepted by the validation function *)
| Input_size (* If the input message doesn't have the proper size *)
| DH_error (* A DH operation failed *)
| Decryption (* An authenticated decryption failed *)
| Saturated_nonce (* Nonce is saturated *)

let s_result (a : Type) = result a s_error

val create_state :
     #sc:sconfig
  -> pattern:wf_handshake_pattern
  -> prologue:hashable (sc_get_config sc)
  -> initiator:bool
  -> s:option (keypair (sc_get_config sc))
  -> e:option (keypair (sc_get_config sc))
  -> rs:option (public_key (sc_get_config sc))
  -> psk:option preshared_key ->
  Pure (s_result (state sc))
  (requires True)
  (ensures (fun r ->
    match r with
    // The premessage processing may fail if we don't provide the required
    // remote keys.
    | Res _ | Fail Premessage -> True
    | _ -> False))

let can_send (initiator : bool) (hsk : handshake_pattern) : Tot bool =
  let more_than_one = normalize_term(List.Tot.length hsk.messages > 1) in
  if more_than_one then true else initiator

let can_receive (initiator : bool) (hsk : handshake_pattern) : Tot bool =
  let more_than_one = normalize_term(List.Tot.length hsk.messages > 1) in
  if more_than_one then true else not initiator

(* Process the handshake messages *)
val handshake_write :
     #sc:sconfig
  -> payload:bytes
  -> st:state sc ->
  Pure (s_result (bytes & state sc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res (msg, st) -> True
    | Fail Incorrect_transition
    | Fail No_key
    | Fail Input_size
    | Fail DH_error
    | Fail Saturated_nonce -> True
    | _ -> False))

val handshake_read :
     #sc:sconfig
  -> msg:bytes
  -> st:state sc
  -> vst:sc_get_vstate sc ->
  Pure (s_result (option (sc_get_pinfo sc) & hashable (sc_get_config sc) & state sc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res (pi, payload, st) -> True
    | _ -> True))

(* Split - we make a disjoint function so that it is possible to perform checks
 * (with the remote static and the payload, for example) before splitting *)
val split : #sc:sconfig -> st:state sc -> s_result (state sc)

(* Transport phase: read and write functions *)
val transport_write :
     #sc:sconfig
  -> state sc
  -> msg:bytes ->
  Pure (s_result (bytes & state sc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res _
    | Fail Incorrect_transition | Fail Input_size
    | Fail Saturated_nonce | Fail Decryption -> True
    | _ -> False))

val transport_read :
     #sc:sconfig
  -> st:state sc
  -> cipher:bytes ->
  Pure (s_result (bytes & state sc))
  (requires True)
  (ensures (fun r ->
    match r with
    | Res _
    | Fail Incorrect_transition | Fail Input_size
    | Fail Decryption | Fail Saturated_nonce -> True
    | _ -> False))
