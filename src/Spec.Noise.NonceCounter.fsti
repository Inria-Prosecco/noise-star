module Spec.Noise.NonceCounter
open FStar.Mul

open Lib.ByteSequence
open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.HandshakeFlags

/// The following file implements functions and predicates to compute and reason
/// about the value of the nonce counter at every step of the handshake.

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

inline_for_extraction noextract
type sk_nonce_info = bool & nat

let get_has_sk_nonce (#nc : config) (state : handshake_state nc) : sk_nonce_info =
  has_symmetric_key state, get_nonce state

(*** Definitions *)
inline_for_extraction noextract
let token_update_nonce (has_sk is_psk : bool) (tk : message_token)
                       (nonce : nat) : nat =
  match tk with
  | S -> if has_sk then nonce + 1 else nonce
  | E -> if is_psk then 0 else nonce
  | _ -> 0

inline_for_extraction noextract
let token_update_sk_nonce (is_psk : bool) (tk : message_token)
                          (sk_nonce : sk_nonce_info) : sk_nonce_info  =
  let has_sk, nonce = sk_nonce in
  let has_sk1 = token_update_sym_key_flag has_sk is_psk tk in
  let nonce1 = token_update_nonce has_sk is_psk tk nonce in
  has_sk1, nonce1

(** Updates the symmetric key boolean and nonce over a list of tokens *)
[@(strict_on_arguments [1])]
inline_for_extraction noextract
let rec tokens_update_sk_nonce (is_psk : bool) (pattern : list message_token)
                               (sk_nonce : sk_nonce_info) :
  Tot sk_nonce_info (decreases pattern) =
  match pattern with
  | [] -> sk_nonce
  | tk :: pattern1 ->
    let sk_nonce1 = token_update_sk_nonce is_psk tk sk_nonce in
    tokens_update_sk_nonce is_psk pattern1 sk_nonce1

inline_for_extraction noextract
let tokens_update_nonce (has_sk is_psk : bool) (pattern : list message_token)
                        (nonce : nat) :
  Tot nat =
  snd (tokens_update_sk_nonce is_psk pattern (has_sk, nonce))

(** Updates the nonce over a message with payload *)
inline_for_extraction noextract
let message_update_nonce (has_sk is_psk : bool) (pattern : list message_token)
                         (nonce : nat) : nat =
  let has_sk1, nonce1 = tokens_update_sk_nonce is_psk pattern (has_sk, nonce) in
  if has_sk1 then nonce1 + 1 else nonce1


(*** Lemmas *)

(**** Consistency lemmas *)
/// Most of the following lemmas are not used in the proofs, but are a guarantee that the
/// above functions are the ones we need: it is less painful to correct them early
/// than notice they are wrong in the middle of the implementation proofs.

(***** update sym key flag *)
val tokens_update_sk_nonce_same_as_update_sym_key_flag :
     is_psk : bool
  -> pattern : list message_token
  -> sk_nonce : sk_nonce_info ->
  Lemma
  (ensures (
    let sk1, nonce = tokens_update_sk_nonce is_psk pattern sk_nonce in
    let sk2 = tokens_update_sym_key_flag (fst sk_nonce) is_psk pattern in
    sk1 == sk2))
  (decreases pattern)

(***** send *)

val send_token_update_nonce_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> state : handshake_state nc ->
  Lemma(
    match send_message_token initiator is_psk tk state with
    | Fail _ -> True
    | Res (_, state1) ->
      let has_sk, nonce = get_has_sk_nonce state in
      get_nonce state1 == token_update_nonce has_sk is_psk tk nonce)

val send_tokens_update_sk_nonce_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> state : handshake_state nc ->
  Lemma
  (ensures (
    match send_message_tokens initiator is_psk pattern state with
    | Fail _ -> True
    | Res (_, state1) ->
      let sk_nonce = get_has_sk_nonce state in
      let sk_nonce1 = get_has_sk_nonce state1 in
      sk_nonce1 == tokens_update_sk_nonce is_psk pattern sk_nonce))
  (decreases pattern)

val send_message_update_nonce_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> payload : plain_message nc
  -> state : handshake_state nc ->
  Lemma
  (ensures (
    match send_message_tokens_with_payload initiator is_psk pattern payload state with
    | Fail _ -> True
    | Res (_, state1) ->
      let has_sk, nonce = get_has_sk_nonce state in
      let nonce1 = get_nonce state1 in
      nonce1 == message_update_nonce has_sk is_psk pattern nonce))

(***** receive *)

val receive_token_update_nonce_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> message : bytes
  -> state : handshake_state nc ->
  Lemma(
    match receive_message_token initiator is_psk tk message state with
    | Fail _ -> True
    | Res (_, state1) ->
      let has_sk, nonce = get_has_sk_nonce state in
      get_nonce state1 == token_update_nonce has_sk is_psk tk nonce)

val receive_tokens_update_sk_nonce_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> message : bytes
  -> state : handshake_state nc ->
  Lemma
  (ensures (
    match receive_message_tokens initiator is_psk pattern message state with
    | Fail _ -> True
    | Res (_, state1) ->
      let sk_nonce = get_has_sk_nonce state in
      let sk_nonce1 = get_has_sk_nonce state1 in
      sk_nonce1 == tokens_update_sk_nonce is_psk pattern sk_nonce))
  (decreases pattern)

val receive_message_update_nonce_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> message : bytes
  -> state : handshake_state nc ->
  Lemma
  (ensures (
    match receive_message_tokens_with_payload initiator is_psk pattern message state with
    | Fail _ -> True
    | Res (_, state1) ->
      let has_sk, nonce = get_has_sk_nonce state in
      let nonce1 = get_nonce state1 in
      nonce1 == message_update_nonce has_sk is_psk pattern nonce))

(**** Decomposition lemmas *)

val tokens_update_sk_nonce_decompose_lem (is_psk : bool)
                                         (tokens1 tokens2 : list message_token)
                                         (skn : sk_nonce_info) :
  Lemma
  (requires True)
  (ensures (
    let skn1 = tokens_update_sk_nonce is_psk tokens1 skn in
    let skn2 = tokens_update_sk_nonce is_psk tokens2 skn1 in
    let skn2' = tokens_update_sk_nonce is_psk (List.Tot.append tokens1 tokens2) skn in
    skn2' = skn2))
  (decreases tokens1)

val tokens_update_nonce_decompose_lem (has_sk is_psk : bool)
                                      (tokens1 tokens2 : list message_token)
                                      (nonce : nat) :
  Lemma
  (requires True)
  (ensures (
    let has_sk' = tokens_update_sym_key_flag has_sk is_psk tokens1 in
    let n1 = tokens_update_nonce has_sk is_psk tokens1 nonce in
    let n2 = tokens_update_nonce has_sk' is_psk tokens2 n1 in
    let n2' = tokens_update_nonce has_sk is_psk (List.Tot.append tokens1 tokens2) nonce in
    n2' = n2))
