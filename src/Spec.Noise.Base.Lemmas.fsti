module Spec.Noise.Base.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base.Definitions

#set-options "--z3rlimit 25 --fuel 1 --ifuel 1"

(*** Initialization *)

val initialize_unfold_lem :
     #nc : config
  -> protocol_name : hashable nc
  -> prologue : hashable nc
  -> static_key : option (keypair nc)
  -> ephemeral_key : option (keypair nc)
  -> preshared_key : option preshared_key ->
  Lemma(
    initialize #nc protocol_name prologue static_key ephemeral_key preshared_key ==
    initialize_handshake_state protocol_name prologue static_key ephemeral_key None None preshared_key)

(*** Recursive definitions unfoldings *)

(**** Premessages *)

val send_premessage_tokens_nil_lem :
     #nc : config
  -> st : handshake_state nc ->
  Lemma (send_premessage_tokens #nc [] st == Res (lbytes_empty, st))

val send_premessage_tokens_unfold_lem :
     #nc : config
  -> tk : premessage_token
  -> tokens : list premessage_token
  -> st : handshake_state nc ->
  Lemma (
    send_premessage_tokens #nc (tk :: tokens) st ==
    begin match send_premessage_token tk st with
    | Fail e -> Fail e
    | Res (msg1, st1) ->
      match send_premessage_tokens tokens st1 with
      | Fail e -> Fail e
      | Res (msg2, st2) ->
        Res (Seq.append msg1 msg2, st2)
    end)

val receive_premessage_tokens_nil_lem :
     #nc : config
  -> st : handshake_state nc ->
  Lemma (receive_premessage_tokens #nc [] Seq.empty st == Res st)

val receive_premessage_tokens_unfold_lem :
     #nc : config
  -> tk : premessage_token
  -> tokens : list premessage_token
  -> msg : bytes
  -> st : handshake_state nc ->
  Lemma (
    receive_premessage_tokens #nc (tk :: tokens) msg st ==
    begin
    if length msg <> List.Tot.length (tk :: tokens) * public_key_size nc
    then Fail PE_input_size else
    let msg1, msg2 = split_bytes msg (public_key_size nc) in
    match receive_premessage_token tk msg1 st with
    | Fail e -> Fail e
    | Res st' -> receive_premessage_tokens tokens msg2 st'
    end)

(**** Messages *)

val send_message_tokens_nil_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> st : handshake_state nc ->
  Lemma (send_message_tokens #nc initiator is_psk [] st == Res (lbytes_empty, st))

val send_message_tokens_unfold_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> tokens : list message_token
  -> st : handshake_state nc ->
  Lemma (
    send_message_tokens #nc initiator is_psk (tk :: tokens) st ==
    begin match send_message_token initiator is_psk tk st with
    | Fail e -> Fail e
    | Res (msg, st') ->
      match send_message_tokens initiator is_psk tokens st' with
      | Fail e -> Fail e
      | Res (msg', st'') ->
        Res (Seq.append msg msg', st'')
    end)

// We can't directly use an equality and have to write a match because the
// return types aren't exactly the same
val send_message_tokens_one_token_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> st : handshake_state nc ->
  Lemma (
    send_message_tokens #nc initiator is_psk [tk] st ==
    begin match send_message_token initiator is_psk tk st with
    | Fail e -> Fail e
    | Res (msg', st') -> Res (msg', st')
    end)

val receive_message_tokens_nil_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> msg : bytes
  -> st : handshake_state nc ->
  Lemma (receive_message_tokens #nc initiator is_psk [] msg st == Res (msg, st))

val receive_message_tokens_unfold_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> tokens : list message_token
  -> msg : bytes
  -> st : handshake_state nc ->
  Lemma (
    receive_message_tokens #nc initiator is_psk (tk :: tokens) msg st ==
    begin match receive_message_token initiator is_psk tk msg st with
    | Fail e -> Fail e
    | Res (msg', st') ->
      match receive_message_tokens initiator is_psk tokens msg' st' with
      | Fail e -> Fail e
      | Res (msg'', st'') ->
        Res (msg'', st'')
    end)

val receive_message_tokens_one_token_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> msg : bytes
  -> st : handshake_state nc ->
  Lemma (
    receive_message_tokens #nc initiator is_psk [tk] msg st ==
    begin match receive_message_token initiator is_psk tk msg st with
    | Fail e -> Fail e
    | Res (msg', st') -> Res (msg', st')
    end)


(*** Messages with payload *)

val send_message_tokens_with_payload_unfold_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> payload : plain_message nc
  -> st : handshake_state nc ->
  Lemma(
    send_message_tokens_with_payload initiator is_psk pattern payload st ==
    begin match send_message_tokens initiator is_psk pattern st with
    | Fail e -> Fail e
    | Res (msg1, st1) ->
      match encrypt_and_hash payload st1.sym_state with
      | Fail x -> Fail x
      | Res (msg2, sym_st1) ->
        Res (Seq.append msg1 msg2, {st1 with sym_state = sym_st1})
    end)

(*** Error classes *)

(**** Cipher *)
val encrypt_with_ad_error_lem :
     nc:config   
  -> aad:aead_aad nc
  -> plain:bytes
  -> cs:cipher_state ->
  Lemma(
    match encrypt_with_ad nc aad plain cs with
    | Res _
    | Fail Saturated_nonce
    | Fail Input_size -> True
    | _ -> False) 

val decrypt_with_ad_error_lem :
     nc:config
  -> aad:aead_aad nc
  -> cipher:bytes
  -> cs:cipher_state ->
  Lemma(
    match decrypt_with_ad nc aad cipher cs with
    | Res _
    | Fail Saturated_nonce
    | Fail Input_size
    | Fail Decryption -> True
    | _ -> False) 

(**** Premessages *)

val send_premessage_tokens_error_lem :
     #nc : config
  -> tokens : list premessage_token
  -> st : handshake_state nc ->
  Lemma
  (ensures (
    match send_premessage_tokens #nc tokens st with
    | Res _
    | Fail PE_no_key -> True
    | _ -> False))
  (decreases tokens)

val receive_premessage_tokens_error_lem :
     #nc : config
  -> tokens:list premessage_token
  -> msg:bytes
  -> st:handshake_state nc ->
  Lemma
  (ensures (
    match receive_premessage_tokens #nc tokens msg st with
    | Res _
    | Fail PE_already_key | Fail PE_input_size -> True
    | _ -> False))
  (decreases tokens)


(**** Messages *)
val send_message_tokens_error_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tokens : list message_token
  -> st : handshake_state nc ->
  Lemma
  (ensures (
    match send_message_tokens #nc initiator is_psk tokens st with
    | Res _
    | Fail No_key | Fail Input_size | Fail DH | Fail Saturated_nonce -> True
    | _ -> False))
  (decreases tokens)

val send_message_tokens_with_payload_error_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> payload : plain_message nc
  -> st : handshake_state nc ->
  Lemma(
    match send_message_tokens_with_payload initiator is_psk pattern payload st with
    | Res _ -> True
    | Fail No_key | Fail Input_size | Fail DH | Fail Saturated_nonce -> True
    | _ -> False)

(*** Framing lemmas *)

let some_implies_same (#a : Type0) (x y : option a) : Type0 =
  match x, y with
  | Some x, Some y -> x == y
  | None, None -> True
  | None, Some _ -> True
  | Some _, None -> False

let handshake_state_same_keys (#nc : config) (st0 st1 : handshake_state nc) : Type0 =
  st0.static == st1.static /\
  st0.ephemeral == st1.ephemeral /\
  st0.remote_static == st1.remote_static /\
  st0.remote_ephemeral == st1.remote_ephemeral /\
  st0.preshared == st1.preshared

let handshake_state_some_key_implies_same (#nc : config) (st0 st1 : handshake_state nc) : Type0 =
  some_implies_same st0.static st1.static /\
  some_implies_same st0.ephemeral st1.ephemeral /\
  some_implies_same st0.remote_static st1.remote_static /\
  some_implies_same st0.remote_ephemeral st1.remote_ephemeral /\
  some_implies_same st0.preshared st1.preshared

val send_message_tokens_preserves_some :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> st : handshake_state nc ->
  Lemma (
    match send_message_tokens initiator is_psk pattern st with
    | Fail _ -> True
    | Res (_, st') -> handshake_state_same_keys st st')

val send_message_tokens_with_payload_preserves_some :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> payload : plain_message nc
  -> st : handshake_state nc ->
  Lemma (
    match send_message_tokens_with_payload initiator is_psk pattern payload st with
    | Fail _ -> True
    | Res (_, st') -> handshake_state_same_keys st st')

val receive_message_tokens_preserves_some :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> msg : bytes
  -> st : handshake_state nc ->
  Lemma (
    match receive_message_tokens initiator is_psk pattern msg st with
    | Fail _ -> True
    | Res (_, st') -> handshake_state_some_key_implies_same st st')

val receive_message_tokens_with_payload_preserves_some :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> msg : bytes
  -> st : handshake_state nc ->
  Lemma (
    match receive_message_tokens_with_payload initiator is_psk pattern msg st with
    | Fail _ -> True
    | Res (_, st') -> handshake_state_some_key_implies_same st st')

val receive_message_tokens_no_S_preserves_remote_static :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token{not (List.Tot.mem S pattern)}
  -> msg : bytes
  -> st : handshake_state nc ->
  Lemma (
    match receive_message_tokens initiator is_psk pattern msg st with
    | Fail _ -> True
    | Res (_, st') -> st'.remote_static == st.remote_static)

val receive_message_tokens_with_payload_no_S_preserves_remote_static :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token{not (List.Tot.mem S pattern)}
  -> msg : bytes
  -> st : handshake_state nc ->
  Lemma (
    match receive_message_tokens_with_payload initiator is_psk pattern msg st with
    | Fail _ -> True
    | Res (_, st') -> st'.remote_static == st.remote_static)

(*** Misc *)

val receive_message_token_S_has_rs_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> message : bytes
  -> state : handshake_state nc ->
  Lemma(
    match receive_message_token #nc initiator is_psk S message state with
    | Res (_, state') ->
      Some? state'.remote_static
    | _ -> True)
