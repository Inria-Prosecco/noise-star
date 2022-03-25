module Impl.Noise.SendReceive

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
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState

friend Spec.Noise.Base.Definitions
friend Spec.Noise.Lengths

(* In order to prevent issues with the interleaving of the .fsti:
 * for the parameters we set the maximum values of the options used in the
 * .fsti *)
#set-options "--z3rlimit 25 --fuel 1 --ifuel 1"

let smi_opt_init_sk (b : bool) (smi : meta_info) : Tot meta_info =
  if b then { smi with hsf = { smi.hsf with sk = true }; nonce = 0} else smi

let smi_init_sk (smi : meta_info) : Tot meta_info =
  smi_opt_init_sk true smi

(*** Send message token(s) *)
(**** send_message_token *)
noextract
let send_message_token_no_fail_post
    (#nc : iconfig)
    (smi0 : meta_info)
    (smi1 : meta_info{less_than smi0 smi1})
    (initiator : bool)
    (is_psk : bool)
    (tk : message_token)
    (st : valid_hsm nc smi1)
    (out : token_message_t nc smi0 tk)
    (h0 : mem) (r : rtype (send_token_return_type smi0 is_psk tk))
    (h1 : mem) : Type0 =
  ssm_modifies1 (hsm_get_sym_state st) out h0 h1 /\
  begin
  let st0_v = eval_handshake_state_m h0 st smi0 in
  let st1_v = eval_handshake_state_m h1 st smi1 in
  let r_v = Spec.send_message_token initiator is_psk tk st0_v in
  match to_prim_error_code r, r_v with
  | CSuccess, Res (cipher_v, st1'_v) ->
    st1_v == st1'_v /\ S.length cipher_v == length out /\
    cipher_v `S.equal` h1.[|out|]
  | _ -> False
  end

noextract
let send_message_token_DH_post
    (#nc : iconfig)
    (smi : meta_info)
    (initiator : bool)
    (is_psk : bool)
    (tk : message_token)
    (st : valid_hsm nc (smi_set_sk true smi))
    (h0 : mem) (r : rtype (send_token_return_type smi is_psk tk))
    (h1 : mem) : Type0 =
  ssm_modifies0 (hsm_get_sym_state st) h0 h1 /\
  begin
  let st0_v = eval_handshake_state_m h0 st smi in
  let st1_v = eval_handshake_state_m h1 st (smi_init_sk smi) in
  let r_v = Spec.send_message_token initiator is_psk tk st0_v in
  match to_prim_error_code r, r_v with
  | CSuccess, Res (cipher_v, st1'_v) ->
    st1_v == st1'_v /\ S.length cipher_v == 0 /\ cipher_v `S.equal` BS.lbytes_empty
  | CDH_error, Fail DH -> True
  | _ -> False
  end


inline_for_extraction noextract
val send_message_S_m :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_send_token_hsm nc is_psk S smi ->
  out : lbuffer uint8 (size (opt_encrypt_size smi.hsf.sk (public_key_vsv nc))) ->
  Stack (rtype (send_token_return_type smi is_psk S))
  (requires (fun h -> hsm_inv h st smi /\ live h out /\ hsm_disjoint st out /\
                    (**) smi.hsf.s == true (**) /\
                    smi.nonce < saturated_nonce_value /\
                    (smi.hsf.sk ==> get_aead_pre nc) /\
                    get_hash_pre nc))
  (ensures (
    send_message_token_no_fail_post smi (send_token_update_smi is_psk S smi)
                                    initiator is_psk S st out))

#push-options "--z3rlimit 50"
let send_message_S_m #nc ssi smi initiator is_psk st out =
  [@inline_let] let s_pub = kpm_get_pub (hsm_get_static st) in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  (**) hash_max_input_norm_lem (get_config nc);
  ssi_get_encrypt_and_hash ssi smi.hsf.sk (public_key_vs nc) s_pub out sym_st
                           (uint smi.nonce)
#pop-options


inline_for_extraction noextract
val send_message_E_m :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_send_token_hsm nc is_psk E smi ->
  out : public_key_t nc ->
  Stack (rtype (send_token_return_type smi is_psk E))
  (requires (fun h -> hsm_inv h st smi /\ live h out /\ hsm_disjoint st out /\
                    (**) smi.hsf.e == true (**) /\ get_hash_pre nc))
  (ensures (
    send_message_token_no_fail_post smi (send_token_update_smi is_psk E smi)
                                    initiator is_psk E st out))

#push-options "--z3rlimit 50"
let send_message_E_m #nc ssi smi initiator is_psk st out =
  (**) let h0 = HST.get () in
  [@inline_let] let e_pub = kpm_get_pub (hsm_get_ephemeral st) in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  (**) hash_max_input_norm_lem (get_config nc);
  ssi_get_mix_hash ssi smi.hsf.sk (public_key_vs nc) e_pub sym_st smi.nonce;
  if is_psk then
    ssi_get_mix_key ssi smi.hsf.sk e_pub sym_st smi.nonce;
    begin
    update_sub out 0ul (public_key_vs nc) e_pub;
    (**) let h1 = HST.get () in
    (**) assert(ssm_modifies1 sym_st out h0 h1);
    let r3 = success (send_token_return_type smi is_psk E) in
    (**) assert(
    (**)   let smi0 = smi in
    (**)   let smi1 = send_token_update_smi is_psk E smi in
    (**)   let st0_v = eval_handshake_state_m h0 st smi0 in
    (**)   let st1_v = eval_handshake_state_m h1 st smi1 in
    (**)   let r_v = Spec.send_message_token initiator is_psk E st0_v in
    (**)   match to_prim_error_code r3, r_v with
    (**)   | CSuccess, Res (cipher_v, st1'_v) ->
    (**)     st1_v == st1'_v /\ S.length cipher_v == length out /\
    (**)     cipher_v `S.equal` h1.[|out|]
    (**)   | _ -> False);
    r3
    end
#pop-options

inline_for_extraction noextract
val send_message_SS_m :
  #nc : iconfig ->
  ssdhi : ssdh_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_send_token_hsm nc is_psk SS smi ->
  Stack (rtype (send_token_return_type smi is_psk SS))
  (requires (fun h -> hsm_inv h st smi /\ (**) smi.hsf.s == true /\ smi.hsf.rs == true (**) /\
                    get_dh_pre nc /\ get_hash_pre nc))
  (ensures (send_message_token_DH_post smi initiator is_psk SS st))

let send_message_SS_m #nc ssdhi smi initiator is_psk st =
  [@inline_let] let priv = hsm_get_static st in
  [@inline_let] let pub = hsm_get_remote_static st in
  ssdhi_get_dh_update ssdhi BS.lbytes_empty smi priv pub st


inline_for_extraction noextract
val send_message_EE_m :
  #nc : iconfig ->
  ssdhi : ssdh_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_send_token_hsm nc is_psk EE smi ->
  Stack (rtype (send_token_return_type smi is_psk EE))
  (requires (fun h -> hsm_inv h st smi /\ (**) smi.hsf.e == true /\ smi.hsf.re == true (**) /\
                    get_dh_pre nc /\ get_hash_pre nc))
  (ensures (send_message_token_DH_post smi initiator is_psk EE st))

let send_message_EE_m #nc ssdhi smi initiator is_psk st =
  [@inline_let] let priv = hsm_get_ephemeral st in
  [@inline_let] let pub = hsm_get_remote_ephemeral st in
  ssdhi_get_dh_update ssdhi BS.lbytes_empty smi priv pub st


inline_for_extraction noextract
val send_message_SE_m :
  #nc : iconfig ->
  ssdhi : ssdh_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_send_token_hsm nc is_psk SE smi ->
  Stack (rtype (send_token_return_type smi is_psk SE))
  (requires (fun h -> hsm_inv h st smi /\
                    (**)
                    (if initiator then smi.hsf.s == true /\ smi.hsf.re == true
                                  else smi.hsf.e == true /\ smi.hsf.rs == true)
                    (**) /\
                    get_dh_pre nc /\ get_hash_pre nc))
  (ensures (send_message_token_DH_post smi initiator is_psk SE st))

let send_message_SE_m #nc ssdhi smi initiator is_psk st =
  [@inline_let] let priv = if initiator then hsm_get_static st
                                        else hsm_get_ephemeral st in
  [@inline_let] let pub = if initiator then hsm_get_remote_ephemeral st
                                       else hsm_get_remote_static st in
  ssdhi_get_dh_update ssdhi BS.lbytes_empty smi priv pub st


inline_for_extraction noextract
val send_message_ES_m :
  #nc : iconfig ->
  ssdhi : ssdh_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_send_token_hsm nc is_psk ES smi ->
  Stack (rtype (send_token_return_type smi is_psk ES))
  (requires (fun h -> hsm_inv h st smi /\
                    (**)
                    (if initiator then smi.hsf.e == true /\ smi.hsf.rs == true
                                  else smi.hsf.s == true /\ smi.hsf.re == true)
                    (**) /\
                    get_dh_pre nc /\ get_hash_pre nc))
  (ensures (send_message_token_DH_post smi initiator is_psk ES st))

let send_message_ES_m #nc ssdhi smi initiator is_psk st =
  [@inline_let] let priv = if initiator then hsm_get_ephemeral st
                                        else hsm_get_static st in
  [@inline_let] let pub = if initiator then hsm_get_remote_static st
                                       else hsm_get_remote_ephemeral st in
  ssdhi_get_dh_update ssdhi BS.lbytes_empty smi priv pub st

#push-options "--ifuel 1"
inline_for_extraction noextract
val send_message_PSK_m :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  st : valid_send_token_hsm nc true PSK smi ->
  Stack (rtype (send_token_return_type smi true PSK))
  (requires (fun h -> hsm_inv h st smi /\ (**) smi.hsf.psk == true (**) /\
                    get_hash_pre nc))
  (ensures (send_message_token_no_fail_post smi (**) (send_token_update_smi true PSK smi) (**)
                                            initiator true PSK st null))
#pop-options

let send_message_PSK_m #nc ssi smi initiator st =
  [@inline_let] let psk = hsm_get_preshared st in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  (**) hash_max_input_norm_lem (get_config nc);
  ssi_get_mix_key_and_hash ssi smi.hsf.sk psk sym_st smi.nonce

/// Some intermediate step: replace the specific preconditions/postconditions of the individual
/// [send_message] functions with the general ones. If we don't do this intermediate step,
/// the proofs explode.

/// Rk.: this intermediate post is maybe not necessary any more...

type send_message_token_m_impl (tk : message_token) =
     #nc : iconfig
  -> ssdhi : ssdh_impls nc
  -> smi : meta_info
  -> initiator : bool
  -> is_psk : bool
  -> st : valid_send_token_hsm nc is_psk tk smi
  -> out : token_message_t nc smi tk ->
  Stack (rtype (send_token_return_type smi is_psk tk))
  (requires (send_message_token_pre smi initiator is_psk tk st out))
  (ensures (send_message_token_post smi initiator is_psk tk st out))

inline_for_extraction noextract
let send_message_S_m_ : send_message_token_m_impl S =
  fun #nc ssdhi smi initiator is_psk st out ->
    send_message_S_m #nc (ssdhi_get_ssi ssdhi) smi initiator is_psk st out

inline_for_extraction noextract
let send_message_E_m_ : send_message_token_m_impl E =
  fun #nc ssdhi smi initiator is_psk st out ->
    send_message_E_m #nc (ssdhi_get_ssi ssdhi) smi initiator is_psk st out

inline_for_extraction noextract
let send_message_SS_m_ : send_message_token_m_impl SS =
  fun #nc ssdhi smi initiator is_psk st out ->
    send_message_SS_m ssdhi smi initiator is_psk st

inline_for_extraction noextract
let send_message_EE_m_ : send_message_token_m_impl EE =
  fun #nc ssdhi smi initiator is_psk st out ->
    send_message_EE_m ssdhi smi initiator is_psk st

inline_for_extraction noextract
let send_message_SE_m_ : send_message_token_m_impl SE =
  fun #nc ssdhi smi initiator is_psk st out ->
    send_message_SE_m #nc ssdhi smi initiator is_psk st

inline_for_extraction noextract
let send_message_ES_m_ : send_message_token_m_impl ES =
  fun #nc ssdhi smi initiator is_psk st out ->
    send_message_ES_m #nc ssdhi smi initiator is_psk st

inline_for_extraction noextract
let send_message_PSK_m_ : send_message_token_m_impl PSK =
  fun #nc ssdhi smi initiator is_psk st out ->
    send_message_PSK_m #nc (ssdhi_get_ssi ssdhi) smi initiator st

#push-options "--ifuel 1"
let send_message_token_m ssdhi smi initiator is_psk tk st out =
  match tk with
  | S -> send_message_S_m_ ssdhi smi initiator is_psk st out
  | E -> send_message_E_m_ ssdhi smi initiator is_psk st out
  | SS -> send_message_SS_m_ ssdhi smi initiator is_psk st out
  | EE -> send_message_EE_m_ ssdhi smi initiator is_psk st out
  | SE -> send_message_SE_m_ ssdhi smi initiator is_psk st out
  | ES -> send_message_ES_m_ ssdhi smi initiator is_psk st out
  | PSK -> send_message_PSK_m_ ssdhi smi initiator is_psk st out
#pop-options

(**** send_message_tokens *)

#push-options "--z3rlimit 100 --fuel 1"
let send_message_tokens_pre_post_lem #nc smi initiator is_psk tk pattern st
                                     tk_outlen tk_out outlen' out' outlen out
                                     h0 h1 h2 r2 =
  let st0_v = eval_handshake_state_m h0 st smi in
  let smi1 = send_token_update_smi is_psk tk smi in
  let st1_v = eval_handshake_state_m h1 st smi1 in
  let smi2 = send_tokens_update_smi is_psk pattern smi1 in
  let st2_v = eval_handshake_state_m h2 st smi2 in
  assert(smi2 == send_tokens_update_smi is_psk (tk :: pattern) smi);
  let sk1 = smi1.hsf.sk in
  assert(outlen' == tokens_message_vs nc smi1 is_psk pattern);
  assert(outlen == tokens_message_vs nc smi is_psk (tk::pattern));
  send_message_token_has_sym_key_lem initiator is_psk tk st0_v;
  token_message_size_lem initiator is_psk tk st0_v;
  (* send_message_token *)
  let r1_v = Spec.send_message_token initiator is_psk tk st0_v in
  assert(
    ssm_modifies1 (hsm_get_sym_state st) tk_out h0 h1 /\
    begin match r1_v with
    | Fail DH -> False
    | Res (tk_out_v, st1'_v) ->
      st1'_v == st1_v /\ length tk_out == S.length tk_out_v /\ h1.[|tk_out|] `S.equal` tk_out_v
    | _ -> False
    end);
  let tk_out_v, st1'_v = Res?.v r1_v in
  assert(st1'_v == st1_v /\ length tk_out == S.length tk_out_v /\ h1.[|tk_out|] `S.equal` tk_out_v);
  (* send_message_tokens *)
  let r2'_v = Spec.send_message_tokens initiator is_psk pattern st1_v in
  assert(
    hsm_modifies1 st out' h1 h2 /\ hsm_disjoint st out' /\
    begin match to_prim_error_code r2, Spec.send_message_tokens initiator is_psk pattern st1_v with
    | CDH_error, Fail DH -> True
    | CSuccess, Res (out'_v, st2'_v) ->
      st2_v == st2'_v /\ length out' == S.length out'_v /\ h2.[|out'|] `S.equal` out'_v
    | _ -> False
    end
  );
  (* postcondition *)
  let r2_v = Spec.send_message_tokens initiator is_psk (tk :: pattern) st0_v in
  match to_prim_error_code r2, r2'_v with
  | CDH_error, Fail DH -> ()
  | CSuccess, Res (out'_v, st2'_v) ->
    match r2_v with
    | Fail _ -> ()
    | Res (out_v, st2_v) ->
      assert(st2'_v == st2_v);
      assert(S.length out'_v == tokens_message_vsv nc smi1 is_psk pattern);
      assert(h2.[|out'|]  `S.equal` out'_v);
      assert(out_v `S.equal` (S.concat #uint8 #(S.length tk_out_v) #(S.length out'_v)
                                       tk_out_v out'_v))
#pop-options

(*** Receive message token(s) *)
(**** receive_message_token *)
let receive_message_no_fail_functional_post
    (#nc : iconfig)
    (smi0 : meta_info)
    (smi1 : meta_info{less_than smi0 smi1})
    (initiator is_psk : bool) (tk : message_token)
    (st : valid_hsm nc smi1)
    (input : token_message_t nc smi0 tk)
    (h0 : mem) (r : rtype (receive_token_return_type smi0 is_psk tk))
    (h1 : mem) : Type0 =
  let st0_v = eval_handshake_state_m h0 st smi0 in
  let st1_v = eval_handshake_state_m h1 st smi1 in
  let input_v = h0.[|input|] in
  let r_v = receive_message_token_nout initiator is_psk tk input_v st0_v in
  match to_prim_error_code r, r_v with
  | CSuccess, Res st1'_v -> st1_v == st1'_v
  | _ -> False

let receive_message_DH_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (tk : message_token{tk == SS \/ tk == EE \/ tk == SE \/ tk == ES})
    (st : valid_hsm nc (smi_init_sk smi))
    (h0 : mem) (r : rtype (receive_token_return_type smi is_psk tk))
    (h1 : mem) : Type0 =
  ssm_modifies0 (hsm_get_sym_state st) h0 h1 /\
  begin
  let st0_v = eval_handshake_state_m h0 st smi in
  let st1_v = eval_handshake_state_m h1 st (**) (smi_init_sk smi) (**) in
  let r_v = receive_message_token_nout initiator is_psk tk
                                            BS.lbytes_empty st0_v in
  match to_prim_error_code r, r_v with
  | CSuccess, Res st1'_v -> st1_v == st1'_v
  | CDH_error, Fail DH -> True
  | _ -> False
  end

inline_for_extraction noextract
val receive_message_S_m :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_receive_token_hsm nc is_psk S smi ->
  input : lbuffer uint8 (size (opt_encrypt_size smi.hsf.sk (public_key_vsv nc))) ->
  Stack (rtype (receive_token_return_type smi is_psk S))
  (requires (fun h -> hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
                    (**) smi.hsf.rs = false (**) /\
                    smi.nonce < saturated_nonce_value /\
                    (smi.hsf.sk ==> get_aead_pre nc) /\
                    get_hash_pre nc))
  (ensures (fun h0 r h1 ->
     ssm_modifies1 (hsm_get_sym_state st) (hsm_get_remote_static st) h0 h1 /\
     begin
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st
                       (**) (receive_token_update_smi is_psk S smi) (**) in
     let input_v = h0.[|input|] in
     let r_v = receive_message_token_nout initiator is_psk S input_v st0_v in
     begin
     match to_prim_error_code r, r_v with
     | CSuccess, Res st1'_v -> st1_v == st1'_v
     | CDecrypt_error, Fail Decryption -> smi.hsf.sk == true
     | _ -> False
     end
     end))

#push-options "--z3rlimit 50 --ifuel 1"
let receive_message_S_m #nc ssi smi initiator is_psk st input =
  [@inline_let] let remote_static = hsm_get_remote_static st in
  [@inline_let] let sym_state = hsm_get_sym_state st in
  (**) hash_max_input_norm_lem (get_config nc);
  let r = ssi_get_decrypt_and_hash ssi smi.hsf.sk (public_key_vs nc)
                                   remote_static input sym_state (uint smi.nonce) in
  if is_always_success r then success _ else r
#pop-options


inline_for_extraction noextract
val receive_message_E_m :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_receive_token_hsm nc is_psk E smi ->
  input : public_key_t nc ->
  Stack (rtype (receive_token_return_type smi is_psk E))
  (requires (fun h -> hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
                    (**) smi.hsf.re = false (**) /\ get_hash_pre nc))
  (ensures (fun h0 r h1 ->
    ssm_modifies1 (hsm_get_sym_state st) (hsm_get_remote_ephemeral st) h0 h1 /\
    receive_message_no_fail_functional_post smi (receive_token_update_smi is_psk E smi)
                                            initiator is_psk E st input h0 r h1))

let receive_message_E_m #nc ssi smi initiator is_psk st input =
  [@inline_let] let sym_st = hsm_get_sym_state st in
  [@inline_let] let st_re = hsm_get_remote_ephemeral st in
  (**) hash_max_input_norm_lem (get_config nc);
  ssi_get_mix_hash ssi smi.hsf.sk (public_key_vs nc) input sym_st smi.nonce;
  if is_psk then
    ssi_get_mix_key ssi smi.hsf.sk input sym_st smi.nonce;
  update_nn st_re input;
  success _


inline_for_extraction noextract
val receive_message_SS_m :
  #nc : iconfig ->
  ssdhi : ssdh_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_receive_token_hsm nc is_psk SS smi ->
  Stack (rtype (receive_token_return_type smi is_psk SS))
  (requires (fun h -> hsm_inv h st smi /\ (**) smi.hsf.s == true /\ smi.hsf.rs == true (**) /\
                    get_dh_pre nc /\ get_hash_pre nc))
  (ensures (receive_message_DH_post smi initiator is_psk SS st))

let receive_message_SS_m #nc ssdhi smi initiator is_psk st =
  [@inline_let] let priv = hsm_get_static st in
  [@inline_let] let pub = hsm_get_remote_static st in
  ssdhi_get_dh_update ssdhi BS.lbytes_empty smi priv pub st


inline_for_extraction noextract
val receive_message_EE_m :
  #nc : iconfig ->
  ssdhi : ssdh_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_receive_token_hsm nc is_psk EE smi ->
  Stack (rtype (receive_token_return_type smi is_psk EE))
  (requires (fun h -> hsm_inv h st smi /\ (**) smi.hsf.e == true /\ smi.hsf.re == true (**) /\
                    get_dh_pre nc /\ get_hash_pre nc))
  (ensures (receive_message_DH_post smi initiator is_psk EE st))

let receive_message_EE_m #nc ssdhi smi initiator is_psk st =
  [@inline_let] let priv = hsm_get_ephemeral st in
  [@inline_let] let pub = hsm_get_remote_ephemeral st in
  ssdhi_get_dh_update ssdhi BS.lbytes_empty smi priv pub st


inline_for_extraction noextract
val receive_message_SE_m :
  #nc : iconfig ->
  ssdhi : ssdh_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_receive_token_hsm nc is_psk SE smi ->
  Stack (rtype (receive_token_return_type smi is_psk SE))
  (requires (fun h -> hsm_inv h st smi /\
                    (**)
                    (if initiator then smi.hsf.s == true /\ smi.hsf.re == true
                                  else smi.hsf.e == true /\ smi.hsf.rs == true) /\
                    (**)
                    get_dh_pre nc /\ get_hash_pre nc))
  (ensures (receive_message_DH_post smi initiator is_psk SE st))

let receive_message_SE_m #nc ssdhi smi initiator is_psk st =
  [@inline_let] let priv = if initiator then hsm_get_static st
                                        else hsm_get_ephemeral st in
  [@inline_let] let pub = if initiator then hsm_get_remote_ephemeral st
                                       else hsm_get_remote_static st in
  ssdhi_get_dh_update ssdhi BS.lbytes_empty smi priv pub st



inline_for_extraction noextract
val receive_message_ES_m :
  #nc : iconfig ->
  ssdhi : ssdh_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  st : valid_receive_token_hsm nc is_psk ES smi ->
  Stack (rtype (receive_token_return_type smi is_psk ES))
  (requires (fun h -> hsm_inv h st smi /\
                    (**)
                    (if initiator then smi.hsf.e == true /\ smi.hsf.rs == true
                                  else smi.hsf.s == true /\ smi.hsf.re == true) (**) /\
                    get_dh_pre nc /\ get_hash_pre nc))
  (ensures (receive_message_DH_post smi initiator is_psk ES st))

let receive_message_ES_m #nc ssdhi smi initiator is_psk st =
  [@inline_let] let priv = if initiator then hsm_get_ephemeral st
                                        else hsm_get_static st in
  [@inline_let] let pub = if initiator then hsm_get_remote_static st
                                       else hsm_get_remote_ephemeral st in
  ssdhi_get_dh_update ssdhi BS.lbytes_empty smi priv pub st


inline_for_extraction noextract
val receive_message_PSK_m :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : meta_info ->
  initiator : bool ->
  st : valid_receive_token_hsm nc true PSK smi ->
  Stack (rtype (receive_token_return_type smi true PSK))
  (requires (fun h -> hsm_inv h st smi /\ (**) smi.hsf.psk == true (**) /\
                    get_hash_pre nc))
  (ensures (fun h0 r h1 ->
    ssm_modifies0 (hsm_get_sym_state st) h0 h1 /\
    receive_message_no_fail_functional_post smi 
      (**) (receive_token_update_smi true PSK smi) (**)
      initiator true PSK st null h0 r h1))

let receive_message_PSK_m #nc ssi smi initiator st =
  [@inline_let] let psk = hsm_get_preshared st in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  (**) hash_max_input_norm_lem (get_config nc);
  ssi_get_mix_key_and_hash ssi smi.hsf.sk psk sym_st smi.nonce

(* Some intermediate step: replace the specific preconditions/postconditions of the individual
 * [receive_message] functions with the general ones. If we don't do this intermediate step,
 * the proofs explode. *)

type receive_message_token_m_impl (tk : message_token) =
     #nc : iconfig
  -> ssdhi : ssdh_impls nc
  -> smi : meta_info
  -> initiator : bool
  -> is_psk : bool
  -> st : valid_receive_token_hsm nc is_psk tk smi
  -> input : token_message_t nc smi tk ->
  Stack (rtype (receive_token_return_type smi is_psk tk))
  (requires (receive_message_token_pre smi initiator is_psk tk st input))
  (ensures (receive_message_token_post smi initiator is_psk tk st input))

inline_for_extraction noextract
let receive_message_S_m_ : receive_message_token_m_impl S =
  fun #nc ssdhi smi initiator is_psk st input ->
    receive_message_S_m #nc (ssdhi_get_ssi ssdhi) smi initiator is_psk st input

inline_for_extraction noextract
let receive_message_E_m_ : receive_message_token_m_impl E =
  fun #nc ssdhi smi initiator is_psk st input ->
    receive_message_E_m #nc (ssdhi_get_ssi ssdhi) smi initiator is_psk st input

inline_for_extraction noextract
let receive_message_SS_m_ : receive_message_token_m_impl SS =
  fun #nc ssdhi smi initiator is_psk st input ->
    receive_message_SS_m #nc ssdhi smi initiator is_psk st

inline_for_extraction noextract
let receive_message_EE_m_ : receive_message_token_m_impl EE =
  fun #nc ssdhi smi initiator is_psk st input ->
    receive_message_EE_m #nc ssdhi smi initiator is_psk st

inline_for_extraction noextract
let receive_message_SE_m_ : receive_message_token_m_impl SE =
  fun #nc ssdhi smi initiator is_psk st input ->
    receive_message_SE_m #nc ssdhi smi initiator is_psk st

inline_for_extraction noextract
let receive_message_ES_m_ : receive_message_token_m_impl ES =
  fun #nc ssdhi smi initiator is_psk st input ->
    receive_message_ES_m #nc ssdhi smi initiator is_psk st

inline_for_extraction noextract
let receive_message_PSK_m_ : receive_message_token_m_impl PSK =
  fun #nc ssdhi smi initiator is_psk st input ->
    receive_message_PSK_m #nc (ssdhi_get_ssi ssdhi) smi initiator st

let receive_message_token_m ssdhi smi initiator is_psk tk st input =
  match tk with
  | S -> receive_message_S_m_ ssdhi smi initiator is_psk st input
  | E -> receive_message_E_m_ ssdhi smi initiator is_psk st input
  | SS -> receive_message_SS_m_ ssdhi smi initiator is_psk st input
  | EE -> receive_message_EE_m_ ssdhi smi initiator is_psk st input
  | SE -> receive_message_SE_m_ ssdhi smi initiator is_psk st input
  | ES -> receive_message_ES_m_ ssdhi smi initiator is_psk st input
  | PSK -> receive_message_PSK_m_ ssdhi smi initiator is_psk st input

(**** receive_message_tokens_nout *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let receive_message_token_m_ #nc impl pattern smi initiator is_psk tk st input =
  assert(
    let smi' = receive_token_update_smi is_psk tk smi in
    check_receive_message_smi smi' initiator is_psk pattern);
  impl smi initiator is_psk tk st input
#pop-options

(* TODO: all the asserts are proven fairly quickly if we put an admit at the end,
 * the proof is also fast if we assume all the asserts or if we just put '()',
 * but the "real", assembled proof is super long, hence the crazy rlimit *)
#push-options "--z3rlimit 1000 --fuel 1"
let receive_message_tokens_nout_pre_post_lem
    #nc smi initiator is_psk tk pattern st tk_inlen tk_input inlen' input'
    inlen input h0 h1 h2 r2 = ()
#pop-options

/// ATTENTION: keep and maintain the following commented proof: necessary for
/// debugging if the above lemma fails.
(*
  let st0_v = eval_handshake_state_m h0 st smi in
  let smi1 = receive_token_update_smi is_psk tk smi in
  let st1_v = eval_handshake_state_m h1 st smi1 in
  let smi2 = receive_tokens_update_smi is_psk pattern smi1 in
  let smi2' = receive_tokens_update_smi is_psk (tk :: pattern) smi in
  let st2_v = eval_handshake_state_m h2 st smi2 in
  assert(smi2 == smi2');
  assert(inlen' == tokens_message_vs nc smi1 is_psk pattern);
  assert(inlen == tokens_message_vs nc smi is_psk (tk :: pattern));
  let tk_input_v = h0.[|tk_input|] in
  let input'_v = h0.[|input'|] in
  let input_v = h0.[|input|] in
  (* receive_message_token *)
  let r1_v = receive_message_token_nout initiator is_psk tk tk_input_v st0_v in
  assert(Res? r1_v);
  let st1'_v = Res?.v r1_v in
  assert(hsm_modifies0 st h0 h1);
  assert(
    match r1_v with
    | Fail e -> False
    | Res st1'_v -> st1'_v == st1_v
    | _ -> False);
  assert(st1'_v == st1_v);
  (* receive_message_tokens *)
  let r2'_v = receive_message_tokens_nout initiator is_psk pattern input'_v st1_v in
  assert(h0.[|input|] `S.equal` h1.[|input|]);
  // We can prove the following assert, but then the equivalence in the last
  // assert is super long to prove. TODO: make a minimal example.
  // assert(
  //   match to_prim_error_code r2, r2'_v with
  //   | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
  //   | CHardware_check_failed, _ -> nc_has_dynamic_checks nc (* sanity check *)
  //   | CSuccess, Res st2'_v -> st2_v == st2'_v
  //   | _ -> False);
  (* postcondition *)
  let r2_v = receive_message_tokens_nout initiator is_psk (tk :: pattern) input_v st0_v in
  assert(input_v `S.equal` (S.concat tk_input_v input'_v));
  assert(r2_v == r2'_v);
  assert(hsm_modifies0 st h0 h2 /\ hsm_disjoint st input);
  let r3 = tokens_message_rtype_add_token #nc #smi #is_psk #false #pattern tk r2 in
  assert(to_prim_error_code r3 == to_prim_error_code r2);
  assert(
    receive_message_tokens_nout_post smi initiator is_psk (tk :: pattern) st inlen input h0 r3 h2
    <==>
    begin
    begin match to_prim_error_code r3, r2_v with
    | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
    | CHardware_check_failed, _ -> nc_has_dynamic_checks nc (* sanity check *)
    | CSuccess, Res st2'_v -> st2_v == st2'_v
    | _ -> False
    end
    end)
#pop-options
*)
