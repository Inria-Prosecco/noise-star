module Spec.Noise.NonceCounter
open FStar.Mul

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.HandshakeFlags

friend Spec.Noise.Base.Definitions

#set-options "--z3rlimit 25 --fuel 1 --ifuel 1"

(*** Lemmas *)

let rec tokens_update_sk_nonce_same_as_update_sym_key_flag is_psk pattern sk_nonce =
  match pattern with
  | [] -> ()
  | tk :: pattern1 ->
    let sk_nonce1 = token_update_sk_nonce is_psk tk sk_nonce in
    tokens_update_sk_nonce_same_as_update_sym_key_flag is_psk pattern1 sk_nonce1

val message_update_nonce_as_update_sym_key_flag_expr :
     has_sk : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> nonce : nat ->
  Lemma (
    let has_sk1 = tokens_update_sym_key_flag has_sk is_psk pattern in
    let nonce1 = tokens_update_nonce has_sk is_psk pattern nonce in
    message_update_nonce has_sk is_psk pattern nonce ==
      (if has_sk1 then nonce1 + 1 else nonce1))

let message_update_nonce_as_update_sym_key_flag_expr has_sk is_psk pattern nonce =
  tokens_update_sk_nonce_same_as_update_sym_key_flag is_psk pattern (has_sk, nonce)

(**** send *)

let send_token_update_nonce_lem #nc initiator is_psk tk state = ()

let rec send_tokens_update_sk_nonce_lem #nc initiator is_psk pattern state =
  match pattern with
  | [] -> ()
  | tk :: pattern1 ->
    send_token_update_nonce_lem initiator is_psk tk state;
    match send_message_token initiator is_psk tk state with
    | Fail _ -> ()
    | Res (msg, state1) ->
      send_tokens_update_sk_nonce_lem initiator is_psk pattern1 state1

let send_message_update_nonce_lem #nc initiator is_psk pattern payload state =
  send_tokens_update_sk_nonce_lem initiator is_psk pattern state

(**** receive *)

let receive_token_update_nonce_lem #nc initiator is_psk tk message state = ()

let rec receive_tokens_update_sk_nonce_lem #nc initiator is_psk pattern message state =
  match pattern with
  | [] -> ()
  | tk :: pattern1 ->
    receive_token_update_nonce_lem initiator is_psk tk message state;
    match receive_message_token initiator is_psk tk message state with
    | Fail _ -> ()
    | Res (msg1, state1) ->
      receive_tokens_update_sk_nonce_lem initiator is_psk pattern1 msg1 state1

let receive_message_update_nonce_lem #nc initiator is_psk pattern message state =
  receive_tokens_update_sk_nonce_lem initiator is_psk pattern message state


(**** Decomposition lemmas *)

#push-options "--fuel 1"
let rec tokens_update_sk_nonce_decompose_lem is_psk tokens1 tokens2 skn =
  match tokens1 with
  | [] -> ()
  | tk :: tokens1' ->
    let skn' = token_update_sk_nonce is_psk tk skn in
    tokens_update_sk_nonce_decompose_lem is_psk tokens1' tokens2 skn'
#pop-options

let tokens_update_nonce_decompose_lem has_sk is_psk tokens1 tokens2 nonce =
  tokens_update_sk_nonce_decompose_lem is_psk tokens1 tokens2 (has_sk, nonce);
  tokens_update_sk_nonce_same_as_update_sym_key_flag is_psk tokens1 (has_sk, nonce)
