module Spec.Noise.HandshakeFlags
open FStar.Mul

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base

friend Spec.Noise.Base.Definitions

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Handshake pattern flags *)
(**** Consistency lemmas *)
#push-options "--fuel 1 --ifuel 1"
let rec compute_hsk_msg_flags_psk_exists_lem
  (ir : bool) (f : handshake_pattern_flags)
  (msg : list message_token) =
  match msg with
  | [] -> ()
  | tk :: msg1 ->
    let f' = compute_hsk_token_flags ir f tk in
    (* TODO: doesn't work without this assert_norm and whatever the amount of
     * fuel. This is very weird... *)
    assert_norm(f'.hsk_psk <==> (f.hsk_psk \/ tk == PSK));
    compute_hsk_msg_flags_psk_exists_lem ir f' msg1
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec compute_hsk_msg_flags_aux_psk_exists_lem
  (ir : bool) (f : handshake_pattern_flags)
  (msgs : list(list message_token)) =
  match msgs with
  | [] -> ()
  | msg :: msgs1 ->
    let f' = compute_hsk_msg_flags ir f msg in
    compute_hsk_msg_flags_psk_exists_lem ir f msg;
    compute_hsk_msg_flags_aux_psk_exists_lem (not ir) f' msgs1
#pop-options

let compute_hsk_flags_consistent_with_check_hsk_is_psk_lem
  (hsk : handshake_pattern) =
  let hskf = compute_hsk_pre_msgs_flags hsk in
  assert(hskf.hsk_psk == false);
  compute_hsk_msg_flags_aux_psk_exists_lem true hskf hsk.messages

(**** Monotonicity lemmas *)
let compute_hsk_token_flags_is_increasing ir hskf0 tk = ()

#push-options "--fuel 1"
let rec compute_hsk_msg_flags_is_increasing ir hskf0 msg =
  match msg with
  | [] -> ()
  | tk :: msg' ->
    let hskf1 = compute_hsk_token_flags ir hskf0 tk in
    // I don't know why we need to call this lemma
    compute_hsk_token_flags_is_increasing ir hskf0 tk;
    assert(hskf0 `hskf_less_than` hskf1);
    compute_hsk_msg_flags_is_increasing ir hskf1 msg'
#pop-options

#push-options "--fuel 1"
let rec compute_hsk_msgs_flags_aux_is_increasing ir hskf0 msgs =
  match msgs with
  | [] -> ()
  | msg :: msgs' ->
    let hskf1 = compute_hsk_msg_flags ir hskf0 msg in
    compute_hsk_msg_flags_is_increasing ir hskf0 msg;
    compute_hsk_msgs_flags_aux_is_increasing (not ir) hskf1 msgs'
#pop-options

(*** Symmetric key flag *)
(**** Update lemmas *)
let send_message_token_has_sym_key_lem (#nc : config)
                                       (initiator is_psk : bool)
                                       (tk : message_token)
                                       (st : handshake_state nc) :
  Lemma(
    match send_message_token initiator is_psk tk st with
    | Fail _ -> True
    | Res (_, st') ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = Some? st'.sym_state.c_state.k in
      has_sym_key' == token_update_sym_key_flag has_sym_key is_psk tk) = ()

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let rec send_message_tokens_has_sym_key_lem
  (#nc : config) (initiator is_psk : bool) (pattern : list message_token)
  (st : handshake_state nc) :
  Lemma(
    match send_message_tokens initiator is_psk pattern st with
    | Fail _ -> True
    | Res (_, st') ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = Some? st'.sym_state.c_state.k in
      has_sym_key' == tokens_update_sym_key_flag has_sym_key is_psk pattern) =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    send_message_token_has_sym_key_lem initiator is_psk tk st;
    match send_message_token initiator is_psk tk st with
    | Fail _ -> ()
    | Res (_, st1) ->
      send_message_tokens_has_sym_key_lem initiator is_psk pattern' st1
#pop-options

#push-options "--fuel 1"
let rec tokens_update_sym_key_flag_decompose_lem has_sym_key is_psk tokens1 tokens2 =
  match tokens1 with
  | [] -> ()
  | tk :: tokens1' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    tokens_update_sym_key_flag_decompose_lem has_sym_key' is_psk tokens1' tokens2
#pop-options

(*** Handshake state flags *)

(**** Compute over message *)
#push-options "--fuel 1"
let rec updt_sk_consistent_with_receive_tokens_update_hsf_lem
  (is_psk : bool) (pattern : list message_token) (hsf : handshake_state_flags) =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    let hsf' = receive_token_update_hsf is_psk tk hsf in
    updt_sk_consistent_with_receive_tokens_update_hsf_lem is_psk pattern' hsf'
#pop-options

(**** Decomposition lemmas *)
#push-options "--fuel 1"
let rec receive_tokens_update_hsf_decompose_lem is_psk tokens1 tokens2 hsf =
  match tokens1 with
  | [] -> ()
  | tk :: tokens1' ->
    let hsf' = receive_token_update_hsf is_psk tk hsf in
    receive_tokens_update_hsf_decompose_lem is_psk tokens1' tokens2 hsf'
#pop-options

(**** Frame lemmas *)
(** We can set the psk later than initialization with no influence on
  * handshake_state_flags (besides the psk field) *)
let receive_pretoken_update_hsf_frame_lem (tk : premessage_token)
                                          (hsf : handshake_state_flags) :
  Lemma(forall sk s e psk.
          receive_pretoken_update_hsf tk ({ hsf with sk = sk; s = s; e = e; psk = psk }) ==
            { receive_pretoken_update_hsf tk hsf with sk = sk; s = s; e = e; psk = psk }) = ()

#push-options "--fuel 1 --ifuel 1"
let rec receive_premessage_update_hsf_frame_lem (pattern : list premessage_token)
                                                (hsf : handshake_state_flags) :
  Lemma(forall sk s e psk.
          receive_premessage_update_hsf pattern
                              ({ hsf with sk = sk; s = s; e = e; psk = psk }) ==
            { receive_premessage_update_hsf pattern hsf
              with sk = sk; s = s; e = e; psk = psk }) =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    let hsf' = receive_pretoken_update_hsf tk hsf in
    receive_pretoken_update_hsf_frame_lem tk hsf;
    receive_premessage_update_hsf_frame_lem pattern' hsf'
#pop-options

let receive_token_update_hsf_frame_lem (is_psk : bool) (tk : message_token)
                                       (hsf : handshake_state_flags) :
  Lemma(
    forall s e psk.
    receive_token_update_hsf is_psk tk ({ hsf with s = s; e = e; psk = psk; }) ==
      { receive_token_update_hsf is_psk tk hsf with s = s; e = e; psk = psk; }) = ()

#push-options "--fuel 1 --ifuel 1"
let rec receive_tokens_update_hsf_frame_lem (is_psk : bool)
                                            (pattern : list message_token)
                                            (hsf : handshake_state_flags) :
  Lemma(
    forall s e psk.
    receive_tokens_update_hsf is_psk pattern ({ hsf with s = s; e = e; psk = psk; }) ==
      { receive_tokens_update_hsf is_psk pattern hsf with s = s; e = e; psk = psk; }) =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    let hsf' = receive_token_update_hsf is_psk tk hsf in
    receive_token_update_hsf_frame_lem is_psk tk hsf;
    receive_tokens_update_hsf_frame_lem is_psk pattern' hsf'
#pop-options

(**** PSK flag equality lemmas *)
#push-options "--fuel 1 --ifuel 1"
let rec send_receive_tokens_update_hsf_same_sk_lem
  (is_psk : bool)
  (shsf rhsf : handshake_state_flags)
  (msg : list message_token) :
  Lemma
  (requires (shsf.sk == rhsf.sk))
  (ensures(
   let shsf1 = send_tokens_update_hsf is_psk msg shsf in
   let rhsf1 = receive_tokens_update_hsf is_psk msg rhsf in
   shsf1.sk == rhsf1.sk))
  (decreases msg) =
  match msg with
  | [] -> ()
  | tk :: msg1 ->
    let shsf1 = { shsf with sk = token_update_sym_key_flag shsf.sk is_psk tk } in
    let rhsf1 = receive_token_update_hsf is_psk tk rhsf in
    assert(shsf1.sk == rhsf1.sk);
    send_receive_tokens_update_hsf_same_sk_lem is_psk shsf1 rhsf1 msg1
#pop-options
