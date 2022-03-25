module Spec.Noise.WellFormedness
open FStar.Mul

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.HandshakeFlags
open Spec.Noise.Lengths
open Spec.Noise.NonceCounter
open Spec.Noise.MetaInfo

friend Spec.Noise.Base.Definitions

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

(*** Properties *)

#push-options "--fuel 1"
let rec check_send_message_smi_psk_no_diff_lem smi initiator is_psk message =
  match message with
  | [] -> ()
  | tk :: message' ->
    let smi' = send_token_update_smi is_psk tk smi in
    check_send_message_smi_psk_no_diff_lem smi' initiator is_psk message'
#pop-options

#push-options "--fuel 1"
let rec check_receive_message_smi_psk_no_diff_lem smi initiator is_psk message =
  match message with
  | [] -> ()
  | tk :: message' ->
    let smi' = receive_token_update_smi is_psk tk smi in
    check_receive_message_smi_psk_no_diff_lem smi' initiator is_psk message'
#pop-options

#push-options "--fuel 1"
let check_handshake_pattern_well_formed_forall_psk_true_lem hsk i =
  let has_psk = true in
  forallb_handshake_pattern_messages_lem hsk has_psk
                                         check_message_executable
#pop-options

let check_hsk_wf_csend_creceive_message_smi_precond_psk_no_diff_lem hsk has_psk i =
  check_handshake_pattern_well_formed_forall_psk_true_lem hsk i;
  let msg = List.Tot.index hsk.messages i in
  let is_psk = chskf_check_is_psk hsk in
  let ir = is_even i in
  (* send *)
  let ssmi0 = csend_message_pre_smi hsk true i in
  let ssmi1 = csend_message_pre_smi hsk false i in
  assert(csend_message_smi_precond hsk true i);
  (* receive *)
  let rsmi0 = creceive_message_pre_smi hsk true i in
  let rsmi1 = creceive_message_pre_smi hsk false i in
  assert(creceive_message_smi_precond hsk true i);
  (* frame lemma *)
  csend_creceive_message_pre_smi_psk_frame_lem hsk i;
  assert(ssmi0 == smi_set_psk true ssmi1);
  assert(rsmi0 == smi_set_psk true rsmi1);
  (* Prove that csend/creceive_message_pre_smi are true for has_psk = false  *)
  if not (has_psk) then
    begin
    check_send_message_smi_psk_no_diff_lem ssmi0 ir is_psk msg;
    check_receive_message_smi_psk_no_diff_lem rsmi0 (not ir) is_psk msg
    end
  else ()

#push-options "--fuel 1"
let rec tokens_update_nonce_not_saturated ir is_psk pattern smi =
  match pattern with
  | [] -> ()
  | tk :: pattern1 ->
    let smi1 =
      if check_send_message_smi smi ir is_psk pattern
      then send_token_update_smi is_psk tk smi
      else receive_token_update_smi is_psk tk smi
    in
    tokens_update_nonce_not_saturated ir is_psk pattern1 smi1
#pop-options
