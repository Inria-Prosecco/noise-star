module Spec.Noise.Base.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base.Definitions

friend Spec.Noise.Base.Definitions

#set-options "--z3rlimit 25 --fuel 1 --ifuel 1"

(*** Initialization *)

let initialize_unfold_lem #nc protocol_name prologue s e psk = ()

(*** Recursive definitions unfoldings *)
(**** Premessages *)
let send_premessage_tokens_nil_lem #nc st = ()

let send_premessage_tokens_unfold_lem #nc tk tokens st = ()

let receive_premessage_tokens_nil_lem #nc st = ()

let receive_premessage_tokens_unfold_lem #nc tk tokens msg st = ()

(**** Messages *)

let send_message_tokens_nil_lem #nc initiator is_psk st = ()

let send_message_tokens_unfold_lem #nc initiator is_psk tk tokens st = ()

#push-options "--fuel 2 --ifuel 2"
let send_message_tokens_one_token_lem #nc initiator is_psk tk st =
  match send_message_token initiator is_psk tk st with
  | Fail e -> ()
  | Res (msg, st') ->
    assert(Seq.append msg lbytes_empty `Seq.equal` msg)
#pop-options

let receive_message_tokens_nil_lem #nc initiator is_psk msg st = ()

let receive_message_tokens_unfold_lem #nc initiator is_psk tk tokens msg st = ()

#push-options "--fuel 2 --ifuel 2"
let receive_message_tokens_one_token_lem #nc initiator is_psk tk msg st = ()
#pop-options


(*** Messages with payload *)

let send_message_tokens_with_payload_unfold_lem initiator is_psk pattern payload st = ()

(*** Error classes *)

(**** Ciphers *)
let encrypt_with_ad_error_lem nc aad plain cs = ()

let decrypt_with_ad_error_lem nc aad cipher cs = ()

(**** Premessages *)

let rec send_premessage_tokens_error_lem #nc tokens st =
  match tokens with
  | [] -> ()
  | tk::tokens' ->
    match send_premessage_token tk st with
    | Fail e -> ()
    | Res (msg1, st1) ->
      send_premessage_tokens_error_lem tokens' st1

let rec receive_premessage_tokens_error_lem #nc tokens msg st =
  if length msg <> List.Tot.length tokens * public_key_size nc then () else
  match tokens with
  | [] -> ()
  | tk::tokens' ->
    let msg1, msg2 = split_bytes msg (public_key_size nc) in
    match receive_premessage_token tk msg1 st with
    | Fail e -> ()
    | Res st' -> receive_premessage_tokens_error_lem tokens' msg2 st'

(**** Messages *)
let rec send_message_tokens_error_lem =
  fun #nc initiator is_psk tokens st ->
  match tokens with
  | [] -> ()
  | tk :: tokens' ->
    match send_message_token initiator is_psk tk st with
    | Fail e -> ()
    | Res (msg, st') ->
      send_message_tokens_error_lem #nc initiator is_psk tokens' st'

let send_message_tokens_with_payload_error_lem =
  fun #nc initiator is_psk pattern payload st ->
  send_message_tokens_error_lem initiator is_psk pattern st

(*** Framing lemmas *)

#push-options "--ifuel 1 --fuel 1"
let rec send_message_tokens_preserves_some #nc initiator is_psk pattern st =
  match pattern with
  | [] -> ()
  | tk::pattern' ->    
    match send_message_token initiator is_psk tk st with
    | Fail e -> ()
    | Res (msg, st') ->
      send_message_tokens_preserves_some initiator is_psk pattern' st'
#pop-options

let send_message_tokens_with_payload_preserves_some #nc initiator is_psk pattern payload st =
  send_message_tokens_preserves_some #nc initiator is_psk pattern st

#push-options "--ifuel 1 --fuel 1"
let rec receive_message_tokens_preserves_some #nc initiator is_psk pattern msg st =
  match pattern with
  | [] -> ()
  | tk::pattern' ->    
    match receive_message_token initiator is_psk tk msg st with
    | Fail e -> ()
    | Res (msg', st') ->
      receive_message_tokens_preserves_some initiator is_psk pattern' msg' st'
#pop-options

let receive_message_tokens_with_payload_preserves_some #nc initiator is_psk pattern msg st =
  receive_message_tokens_preserves_some #nc initiator is_psk pattern msg st

#push-options "--ifuel 1 --fuel 1"
let rec receive_message_tokens_no_S_preserves_remote_static #nc initiator is_psk pattern msg st =
  match pattern with
  | [] -> ()
  | tk::pattern' ->    
    match receive_message_token initiator is_psk tk msg st with
    | Fail e -> ()
    | Res (msg', st') ->
      receive_message_tokens_no_S_preserves_remote_static initiator is_psk pattern' msg' st'
#pop-options

let receive_message_tokens_with_payload_no_S_preserves_remote_static
  #nc initiator is_psk pattern msg st =
  receive_message_tokens_no_S_preserves_remote_static #nc initiator is_psk pattern msg st


(*** Misc *)

let receive_message_token_S_has_rs_lem #nc initiator is_psk message state = ()
