module Impl.Noise.RecursiveMessages

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence
module SB = FStar.Seq.Base
module L = FStar.List
module Seq = FStar.Seq

module B = LowStar.Buffer
module BS = Lib.ByteSequence
module LB = Lib.Buffer
open Lib.Buffer
module BB = Lib.ByteBuffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Meta.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.SendReceive

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(*** Send messages tokens *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
[@(strict_on_arguments [5])]
inline_for_extraction noextract
let rec send_message_tokens_m
    (#nc : iconfig)
    (send_message_token_impl : send_message_token_st nc) :
    send_message_tokens_st nc =
  fun smi initiator is_psk pattern st outlen out ->
  (**) let h0 = HST.get () in
  (**) let st0_v : Ghost.erased _ = eval_handshake_state_m h0 st smi in
  match pattern with
  | Nil ->
    (**) send_message_tokens_nil_lem initiator is_psk st0_v;
    success _
  | [tk] ->
    (**) send_message_tokens_one_token_lem initiator is_psk tk st0_v;
    let r = send_message_token_impl smi initiator is_psk tk st out in
    token_message_rtype_to_tokens #smi #is_psk #true #tk [] r
  | tk :: pattern' ->
    [@inline_let] let tk_outlen = token_message_vs nc smi tk in
    let tk_out = sub out 0ul tk_outlen in
    (**) assert(send_message_token_pre smi initiator is_psk tk st tk_out h0);
    let r1 = send_message_token_impl smi initiator is_psk tk st tk_out in
    (**) send_message_tokens_unfold_lem initiator is_psk tk pattern' st0_v;
    if is_success r1
    then
      begin
      let outlen' = outlen -! tk_outlen in
      (**) assert(size_v outlen' == size_v outlen - size_v tk_outlen);
      let out' = sub out tk_outlen outlen' in
      [@inline_let] let smi' = send_token_update_smi is_psk tk smi in
      (**) let h1 = HST.get () in
      (**) assert(send_message_token_post smi initiator is_psk tk st tk_out h0 (success _) h1);
      (**) assert(send_message_tokens_pre smi' initiator is_psk pattern' st outlen' out' h1);
      let r2 = send_message_tokens_m send_message_token_impl smi' initiator
                                     is_psk pattern' st outlen' out' in
      (**) let h2 = HST.get () in
      (**) assert(send_message_tokens_post smi' initiator is_psk pattern' st
                                           outlen' out' h1 r2 h2);
      (**) assert(tk_outlen == token_message_vs nc smi tk);
      (**) assert(size_v outlen == size_v tk_outlen + size_v outlen');
      (**) assert(tk_out == Ghost.reveal (gsub out 0ul tk_outlen));
      (**) assert(out' == Ghost.reveal (gsub out tk_outlen outlen'));
      (**) send_message_tokens_pre_post_lem smi initiator is_psk tk pattern' st
                                            tk_outlen tk_out outlen' out' outlen out
                                            h0 h1 h2 r2;
      tokens_message_rtype_add_token #smi #is_psk #true #pattern' tk r2
      end
    else token_message_rtype_to_tokens #smi #is_psk #true #tk pattern' r1

(*** Receive message tokens *)
#push-options "--z3rlimit 25 --fuel 1 --ifuel 1"
inline_for_extraction noextract
let receive_message_tokens_nout_m_Nil_
    (#nc : iconfig)
    (smi : meta_info)
    (initiator : bool)
    (is_psk : bool)
    (st : valid_hsm nc smi)
    (inlen : size_t)
    (input : lbuffer uint8 inlen) :
    Stack (rtype (receive_tokens_return_type smi is_psk []))
    (requires (receive_message_tokens_nout_pre smi initiator is_psk []
                                               st inlen input))
    (ensures (fun h0 r h1 -> receive_message_tokens_nout_post smi initiator is_psk []
                                               st inlen input h0 r h1)) =
  (**) let h0 = HST.get () in
  (**) let st0_v : Ghost.erased _ = eval_handshake_state_m h0 st smi in
  (**) assert(size_v inlen = 0);
  (**) assert(h0.[|input|] `Seq.equal` Seq.empty);
  (**) receive_message_tokens_nout_nil_lem initiator is_psk st0_v;
  success _
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
inline_for_extraction noextract
let receive_message_tokens_nout_m_Cons_Nil_
    (#nc : iconfig)
    (receive_message_token_impl : receive_message_token_st nc)
    (smi : meta_info)
    (initiator : bool)
    (is_psk : bool)
    (tk : message_token)
    (st : valid_receive_token_hsm nc is_psk tk smi)
    (inlen : size_t)
    (input : lbuffer uint8 inlen) :
    Stack (rtype (receive_tokens_return_type smi is_psk [tk]))
    (requires (receive_message_tokens_nout_pre smi initiator is_psk [tk]
                                               st inlen input))
    (ensures (fun h0 r h1 -> receive_message_tokens_nout_post smi initiator is_psk [tk]
                                               st inlen input h0 r h1)) =
  (**) let h0 = HST.get () in
  (**) let st0_v : Ghost.erased _ = eval_handshake_state_m h0 st smi in
  (**) assert(size_v inlen == tokens_message_vsv nc smi is_psk [tk]);
  (**) assert(check_receive_message_smi smi initiator is_psk [tk]);
  (**) receive_message_tokens_nout_one_token_lem initiator is_psk tk #(size_v inlen) h0.[|input|] st0_v;
  receive_message_token_m_ receive_message_token_impl [] smi initiator is_psk
                           tk st input
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
[@(strict_on_arguments [5])]
inline_for_extraction noextract
let rec receive_message_tokens_nout_m
    (#nc : iconfig)
    (receive_message_token_impl : receive_message_token_st nc) :
    receive_message_tokens_nout_st nc =
  fun smi initiator is_psk pattern st inlen input ->
  match pattern with
  | Nil -> receive_message_tokens_nout_m_Nil_ smi initiator is_psk st inlen input
  | [tk] -> receive_message_tokens_nout_m_Cons_Nil_ receive_message_token_impl
                                                    smi initiator is_psk tk st inlen input
  | tk :: pattern' ->
    [@inline_let] let tk_inlen = token_message_vs nc smi tk in
    let tk_input = sub input 0ul tk_inlen in
    (**) let h0 = HST.get () in
    (**) let st0_v : Ghost.erased _ = eval_handshake_state_m h0 st smi in
    (**) assert(receive_message_token_pre_ pattern' smi initiator is_psk tk st tk_input h0);
    let r1 = receive_message_token_m_ receive_message_token_impl pattern' smi
                                      initiator is_psk tk st tk_input in
    (**) receive_message_tokens_nout_unfold_lem initiator is_psk tk pattern' h0.[|input|] st0_v;
    if is_success r1
    then
      begin
      let inlen' = inlen -! tk_inlen in
      (**) assert(size_v inlen' == size_v inlen - size_v tk_inlen);
      let input' = sub input tk_inlen inlen' in
      [@inline_let] let smi' = receive_token_update_smi is_psk tk smi in
      (**) let h1 = HST.get () in
      (**) assert(receive_message_token_post_ pattern' smi initiator is_psk tk
                                              st tk_input h0 (success _) h1);
      (**) assert(receive_message_tokens_nout_pre smi' initiator is_psk
                                                  pattern' st inlen' input' h1);
      let r2 = receive_message_tokens_nout_m receive_message_token_impl smi'
                                             initiator is_psk pattern'
                                             st inlen' input' in
      (**) let h2 = HST.get () in
      (**) assert(receive_message_tokens_nout_post smi' initiator is_psk pattern'
                                           st inlen' input' h1 r2 h2);
      (**) assert(tk_inlen == token_message_vs nc smi tk);
      (**) assert(size_v inlen == size_v tk_inlen + size_v inlen');
      (**) assert(tk_input == Ghost.reveal (gsub input 0ul tk_inlen));
      (**) assert(input' == Ghost.reveal (gsub input tk_inlen inlen'));
      (**) receive_message_tokens_nout_pre_post_lem smi initiator is_psk tk pattern'
                                            st tk_inlen tk_input inlen' input' inlen input
                                            h0 h1 h2 r2;
      tokens_message_rtype_add_token #smi #is_psk #false #pattern' tk r2
      end
    else token_message_rtype_to_tokens #smi #is_psk #false #tk pattern' r1
#pop-options

(*** Send messages with payload *)
#push-options "--z3rlimit 200"
inline_for_extraction noextract
let send_message_tokens_with_payload_m
    (#nc : iconfig) (ssi : ss_impls nc)
    (send_message_tokens_impl : send_message_tokens_st nc) :
    send_message_tokens_with_payload_st nc =
  fun smi initiator is_psk pattern payload_len payload st outlen out ->
  (**) let h0 = HST.get () in
  (**) let st0_v : Ghost.erased _ = eval_handshake_state_m h0 st smi in
  [@inline_let] let pat_outlen_v = tokens_message_vsv nc smi is_psk pattern in
  let pat_outlen = size pat_outlen_v in
  let pat_out = sub out 0ul pat_outlen in
  [@inline_let] let payload_outlen = size (size_v outlen - size_v pat_outlen) in
  let payload_out : lbuffer uint8 payload_outlen = sub out pat_outlen payload_outlen in
  (**) assert(pat_outlen_v + v payload_outlen == v outlen);
  (**) assert(h0.[|out|] `S.equal` (S.concat h0.[|pat_out|] h0.[|payload_out|]));
  [@inline_let] let st_sym = hsm_get_sym_state st in
  [@inline_let] let smi1_nn = send_tokens_update_smi is_psk pattern smi in
  [@inline_let] let smi1 = with_norm(smi1_nn) in
  [@inline_let] let sk1 = smi1.hsf.sk in
  [@inline_let] let nonce1 = smi1.nonce in
  (**) assert(smi1.hsf.sk == tokens_update_sym_key_flag smi.hsf.sk is_psk pattern);
  (**) let smi2 : Ghost.erased meta_info = send_message_update_smi is_psk pattern smi in
  (**) assert(
  (**)   smi2.hsf == smi1.hsf /\
  (**)   smi2.nonce == (if smi1.hsf.sk then smi1.nonce + 1 else smi1.nonce));
  (**) tokens_update_nonce_not_saturated initiator is_psk pattern smi;
  (**) assert(nonce1 < saturated_nonce_value);
  (**) assert(v payload_outlen == opt_encrypt_size sk1 (v payload_len));
  let r1 = send_message_tokens_impl smi initiator is_psk pattern st pat_outlen pat_out in
  (**) send_message_tokens_with_payload_unfold_lem initiator is_psk pattern h0.[|payload|] st0_v;
  (**) let h1 = HST.get () in
  if not (is_success r1)
  then r1
  else
  begin
    (**) assert(
    (**)   let st1_v = eval_handshake_state_m h1 st (**) smi1 (**) in
    (**)   match to_prim_error_code r1,
    (**)         Spec.send_message_tokens initiator is_psk pattern st0_v with
    (**)   | CSuccess, Res (out_v, st1'_v) ->
    (**)     st1_v == st1'_v /\ length pat_out == S.length out_v /\
    (**)     h1.[|pat_out|] `S.equal` out_v
    (**)   | _ -> False);
    (**) let h1 = HST.get () in
    let r2 = ssi_get_encrypt_and_hash ssi sk1 payload_len payload payload_out st_sym
                                      (uint nonce1) in
    (**) let h2 = HST.get () in
    (**) assert(h2.[|out|] `S.equal` (S.concat h2.[|pat_out|] h2.[|payload_out|]));
    (**) assert(
    (**)   let st0_v = eval_handshake_state_m h1 st smi1 in
    (**)   match to_prim_error_code r2,
    (**)         Spec.encrypt_and_hash h1.[|payload|] st0_v.sym_state with
    (**)   | CSuccess, Res (payload_out_v, sym_st1_v) ->
    (**)     h2.[|payload_out|] `S.equal` payload_out_v /\
    (**)     sym_st1_v == (eval_handshake_state_m h2 st smi2).sym_state
    (**)   | _ -> False);
    encrypt_hash_rtype_to_message_payload #smi #is_psk #pattern r2
  end
#pop-options

(*** Receive messages with payload *)

#push-options "--z3rlimit 300"
inline_for_extraction noextract
let receive_message_tokens_nout_with_payload_m
    (#nc : iconfig) (ssi : ss_impls nc)
    (receive_message_tokens_nout_impl : receive_message_tokens_nout_st nc) :
    receive_message_tokens_nout_with_payload_st nc =
  fun smi initiator is_psk pattern payload_outlen payload_out st
    msg_inlen msg_input payload_inlen payload_input ->
  (**) let h0 = HST.get () in
  [@inline_let] let st_sym = hsm_get_sym_state st in
  [@inline_let] let smi1_nn = receive_tokens_update_smi is_psk pattern smi in
  [@inline_let] let smi1 = with_norm(smi1_nn) in
  (**) updt_sk_consistent_with_receive_tokens_update_smi is_psk pattern smi;
  (**) assert(tokens_update_sym_key_flag smi.hsf.sk is_psk pattern == smi1.hsf.sk);
  (**) tokens_update_nonce_not_saturated initiator is_psk pattern smi;
  (**) assert(smi1.nonce < saturated_nonce_value);
  (**) let smi2 : Ghost.erased meta_info =
  (**)            receive_message_update_smi is_psk pattern smi in
  (**) assert(
  (**)   smi2.hsf == smi1.hsf /\
  (**)   smi2.nonce = (if smi1.hsf.sk then smi1.nonce + 1 else smi1.nonce));
  let r1 = receive_message_tokens_nout_impl smi initiator is_psk pattern st
                                            msg_inlen msg_input in
  (**) let h1 = HST.get () in
  (**) let st0_v : Ghost.erased _ = eval_handshake_state_m h0 st smi in
  (**) let r1_v : Ghost.erased (eresult (handshake_state (get_config nc))) =
  (**)    Spec.receive_message_tokens_nout initiator is_psk pattern
                                           h0.[|msg_input|] st0_v in
  (**) assert(
  (**)   let st1_v = eval_handshake_state_m h1 st smi1 in
  (**)   let input_v = h0.[|msg_input|] in
  (**)   begin match to_prim_error_code r1, Ghost.reveal r1_v with
  (**)   | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
  (**)   | CSuccess, Res st1'_v -> st1_v == st1'_v
  (**)   | _ -> False
  (**)   end);
  (**) receive_message_tokens_nout_with_payload_unfold_lem initiator is_psk pattern
  (**)                                                     h0.[|msg_input|] h0.[|payload_input|] st0_v;
  if not (is_success r1) then convert_subtype r1 else
  begin
    let r2 = ssi_get_decrypt_and_hash ssi smi1.hsf.sk payload_outlen payload_out
                                      payload_input st_sym (uint smi1.nonce) in
    (**) let st1_v : Ghost.erased (handshake_state (get_config nc)) =
    (**)               eval_handshake_state_m h1 st smi1 in
    (**) let h2 = HST.get () in
    (**) assert(Res? r1_v /\ is_success r1 /\ Ghost.reveal st1_v == Res?.v r1_v);
    (**) assert(
    (**)   let has_key = smi1.hsf.sk in
    (**)   let nonce1 = smi1.nonce in
    (**)   let nonce2 = if has_key then nonce1 + 1 else nonce1 in
    (**)   let st0_v = eval_symmetric_state_m h1 st_sym has_key nonce1 in
    (**)   let res_v = Spec.decrypt_and_hash h1.[|payload_input|] st0_v in
    (**)   match to_prim_error_code r2, res_v with
    (**)   | CDecrypt_error, Fail Decryption ->
    (**)     eval_symmetric_state_m h2 st_sym has_key nonce1 == st0_v
    (**)   | CSuccess, Res (msg_v, st1_v) ->
    (**)     S.length h1.[|payload_out|] == S.length msg_v /\
    (**)     h2.[|payload_out|] `S.equal` msg_v /\
    (**)     st1_v == eval_symmetric_state_m h2 st_sym has_key nonce2
    (**)   | _ -> False);
    (**) assert(hsm_modifies1 st payload_out h0 h2);
    let r2' =
      decrypt_hash_rtype_convert_sk smi1.hsf.sk
                                    (receive_tokens_update_smi is_psk pattern smi).hsf.sk r2 in
    convert_subtype (decrypt_hash_rtype_to_message_payload #smi #is_psk #pattern r2')
  end
#pop-options

#push-options "--z3rlimit 25"
inline_for_extraction noextract
let receive_message_tokens_with_payload_m
    (#nc : iconfig)
    (receive_message_tokens_with_payload_nout_impl :
       receive_message_tokens_nout_with_payload_st nc) :
    receive_message_tokens_with_payload_st nc =
  fun smi initiator is_psk pattern payload_outlen payload_out st inlen input ->
  (**) let h0 = HST.get () in
  (* Split the input *)
  [@inline_let] let msg_inlen_v = tokens_message_vsv nc smi is_psk pattern in
  let msg_input = sub input 0ul (size msg_inlen_v) in
  [@inline_let] let sk1_nn = tokens_update_sym_key_flag smi.hsf.sk is_psk pattern in
  [@inline_let] let sk1 = with_norm(sk1_nn) in
  [@inline_let] let payload_inlen = opt_encrypt_size sk1 (size_v payload_outlen) in
  (**) assert(msg_inlen_v + payload_inlen == size_v inlen);
  let payload_input = sub input (size msg_inlen_v) (size payload_inlen) in
  (**) assert(h0.[|input|] `S.equal` (S.concat h0.[|msg_input|] h0.[|payload_input|]));
  (* Delegate *)
  let r = receive_message_tokens_with_payload_nout_impl smi initiator
                    is_psk pattern payload_outlen payload_out st
                    (size msg_inlen_v) msg_input (size payload_inlen) payload_input
                    in
  (* Prove the postcondition with an equivalence lemma *)
  (**) let st0_v : Ghost.erased (handshake_state (get_config nc)) =
  (**)               eval_handshake_state_m h0 st smi in
  (**) receive_message_tokens_with_payload_eq initiator is_psk pattern
                                              #msg_inlen_v h0.[|msg_input|]
                                              #payload_inlen
                                              h0.[|payload_input|] st0_v;
  convert_subtype r
#pop-options
