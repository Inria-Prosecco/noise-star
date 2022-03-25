module Spec.Noise.Lengths

open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence
module L = LowStar.Literal

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.HandshakeFlags

friend Spec.Noise.Base.Definitions

#set-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(*** Protocol name *)

let concat_length (s1 s2: string): Lemma
  (ensures FStar.String.(length (s1 ^ s2) = length s1 + length s2))
  [ SMTPat (s1 ^ s2) ]
=
  FStar.String.concat_length s1 s2

let protocol_name_length_eq pattern_name nc =
  normalize_term_spec (String.length "25519");
  normalize_term_spec (String.length "AESGCM");
  normalize_term_spec (String.length "ChaChaPoly");
  normalize_term_spec (String.length "SHA256");
  normalize_term_spec (String.length "SHA512");
  normalize_term_spec (String.length "BLAKE2s");
  normalize_term_spec (String.length "BLAKE2b");
  normalize_term_spec (String.length "Noise_");
  normalize_term_spec (String.length "_");
  let _ = allow_inversion Spec.Agile.DH.algorithm in
  let _ = allow_inversion Spec.Agile.Hash.hash_alg in
  let _ = allow_inversion Spec.Agile.AEAD.alg in
  let dh_name = string_of_dh nc in
  let aead_name = string_of_aead nc in
  let hash_name = string_of_hash nc in
  ()

let protocol_name_length_lem pat string = ()

let list_of_concat (s1 s2: string): Lemma
  (ensures (String.list_of_string (s1 ^ s2) == String.list_of_string s1 @ String.list_of_string s2))
  [ SMTPat (String.list_of_string (s1 ^ s2)) ]
=
  FStar.String.list_of_concat s1 s2

#push-options "--fuel 1"
let rec for_all_concat #a (f: a -> bool) (s1 s2: list a): Lemma
  (ensures (List.Tot.for_all f (s1 @ s2) <==> List.Tot.for_all f s1 && List.Tot.for_all f s2))
  [ SMTPat (List.Tot.for_all f (s1 @ s2)) ]
=
  let _ = allow_inversion (list a) in
  match s1 with
  | [] -> ()
  | hd1 :: tl1 -> for_all_concat f tl1 s2
#pop-options

let protocol_name_ascii_lem pat c =
  assert_norm (L.is_ascii_string "25519");
  assert_norm (L.is_ascii_string "AESGCM");
  assert_norm (L.is_ascii_string "ChaChaPoly");
  assert_norm (L.is_ascii_string "SHA256");
  assert_norm (L.is_ascii_string "SHA512");
  assert_norm (L.is_ascii_string "BLAKE2s");
  assert_norm (L.is_ascii_string "BLAKE2b");
  assert_norm (L.is_ascii_string "Noise_");
  assert_norm (L.is_ascii_string "_");
  let _ = allow_inversion Spec.Agile.DH.algorithm in
  let _ = allow_inversion Spec.Agile.Hash.hash_alg in
  let _ = allow_inversion Spec.Agile.AEAD.alg in
  ()

(*** Lemmas *)

(**** Lemmas: send_message_token *)
let encrypt_with_ad_outlen_lem (#nc : config) (aad : aead_aad nc)
                               (plain : plain_message nc) (st : cipher_state) :
  Lemma(
    match encrypt_with_ad nc aad plain st with
    | Fail _ -> True
    | Res (cipher, _) ->
      length cipher == opt_encrypt_size (Some? st.k) (length plain))
  = ()

let encrypt_and_hash_outlen_lem (#nc : config)
                                (plain : plain_message nc)
                                (st : symmetric_state nc) :
  Lemma(
    match encrypt_and_hash plain st with
    | Fail _ -> True
    | Res (cipher, _) -> 
      length cipher == opt_encrypt_size (Some? st.c_state.k) (length plain)) =
  encrypt_with_ad_outlen_lem st.h plain st.c_state

let send_message_S_outlen_lem (#nc : config)
                              (initiator is_psk : bool)
                              (st : handshake_state nc) :
  Lemma(
    match send_message_token initiator is_psk S st with
    | Fail _ -> True
    | Res (out, _) ->
      length out == opt_encrypt_size (Some? st.sym_state.c_state.k) (public_key_size nc)) =
  match st.static with
  | None -> ()
  | Some k ->
    (**) hash_max_input_norm_lem nc;
    encrypt_and_hash_outlen_lem k.pub st.sym_state

#push-options "--fuel 100"
let token_message_size_lem (#nc : config)
                                  (initiator is_psk : bool)
                                  (tk : message_token)
                                  (st : handshake_state nc) :
  Lemma(
    match send_message_token initiator is_psk tk st with
    | Fail _ -> True
    | Res (out, _) ->
      length out == token_message_size nc (Some? st.sym_state.c_state.k) tk) =
  match tk with
  | S -> send_message_S_outlen_lem initiator is_psk st
  | _ -> ()
#pop-options

let rec max_tokens_message_size_lem nc has_sym_key is_psk pattern =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    max_tokens_message_size_lem nc has_sym_key' is_psk pattern'

let rec min_tokens_message_size_lem nc has_sym_key is_psk pattern =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    min_tokens_message_size_lem nc has_sym_key' is_psk pattern'

(**** Lemmas: send_message_tokens *)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 2"
let rec tokens_message_size_lem
  (#nc : config) (initiator is_psk : bool) (pattern : list message_token)
  (st : handshake_state nc) :
  Lemma
  (requires True)
  (ensures 
    begin match send_message_tokens initiator is_psk pattern st with
    | Fail _ -> True
    | Res (out, _) ->
      length out == tokens_message_size nc (Some? st.sym_state.c_state.k)
                                                    is_psk pattern end)
  (decreases pattern) = 
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    send_message_token_has_sym_key_lem initiator is_psk tk st;
    token_message_size_lem initiator is_psk tk st;
    match send_message_token initiator is_psk tk st with
    | Fail _ -> ()
    | Res (_, st1) ->
      tokens_message_size_lem initiator is_psk pattern' st1
#pop-options

val decrypt_with_ad_output_len_lemma :
     #nc : config
  -> aad : aead_aad nc
  -> cipher : bytes
  -> st : cipher_state{Some? st.k}
  -> Lemma(match decrypt_with_ad nc aad cipher st with
           | Res (p, _) -> length cipher >= aead_tag_size /\
                           length p == length cipher - aead_tag_size
           | Fail _ -> True)

let decrypt_with_ad_output_len_lemma #nc aad cipher st = ()

let decrypt_and_hash_output_len_lemma #nc cipher st =
  decrypt_with_ad_output_len_lemma #nc st.h cipher st.c_state

#push-options "--z3rlimit 25 --ifuel 2"
let message_size_lem
  (#nc : config) (initiator is_psk : bool) (pattern : list message_token)
  (payload : plain_message nc) (st : handshake_state nc) :
  Lemma
  (requires True)
  (ensures 
    begin match send_message_tokens_with_payload initiator is_psk pattern payload st with
    | Fail _ -> True
    | Res (out, _) ->
      length out == message_size nc (Some? st.sym_state.c_state.k)
                                    is_psk pattern (length payload) end)
  (decreases pattern) =
  match send_message_tokens_with_payload initiator is_psk pattern payload st with
  | Fail _ -> ()
  | Res (out, st1) ->
    tokens_message_size_lem initiator is_psk pattern st;
    send_message_tokens_has_sym_key_lem initiator is_psk pattern st;
    encrypt_and_hash_outlen_lem payload st1.sym_state
#pop-options

(*** receive_message_tokens_outlen *)

let dh_update_nout #nc opt_priv opt_pub st =
  match opt_priv, opt_pub with
  | Some priv, Some pub ->
    (match dh priv.priv pub with
     | Some k -> Res ({ st with sym_state = mix_key k st.sym_state })
     | None -> Fail DH)
  | _ -> Fail No_key

let receive_message_token_nout #nc initiator is_psk tk #msg_len msg st =
  match tk with
  | S ->
    (**) hash_max_input_norm_lem nc;
    if Some? st.remote_static then Fail Already_key else
    begin match decrypt_and_hash msg st.sym_state with
    | Res (rs, sym_st') ->
      Res ({ st with remote_static = Some rs; sym_state = sym_st' })
    | Fail e -> Fail e
    end
  | E ->
    (**) hash_max_input_norm_lem nc;
    if Some? st.remote_ephemeral then Fail Already_key else
    let sym_st1 = mix_hash msg st.sym_state in
    let sym_st2 =
      if is_psk
      then mix_key msg sym_st1
      else sym_st1
    in
    Res ({ st with sym_state = sym_st2; remote_ephemeral = Some msg})
  | SS -> dh_update_nout st.static st.remote_static st
  | EE -> dh_update_nout st.ephemeral st.remote_ephemeral st
  | SE ->
    let opt_priv = if initiator then st.static else st.ephemeral in
    let opt_pub = if initiator then st.remote_ephemeral
                                  else st.remote_static in
    dh_update_nout opt_priv opt_pub st
  | ES ->
    let opt_priv = if initiator then st.ephemeral else st.static in
    let opt_pub = if initiator then st.remote_static
                                  else st.remote_ephemeral in
    dh_update_nout opt_priv opt_pub st
  | PSK ->
    begin
    match st.preshared with
    | None -> Fail No_key
    | Some k ->
      Res ({ st with sym_state = mix_key_and_hash k st.sym_state; })
    end

let receive_message_token_nout_has_sym_key_lem #nc initiator is_psk tk #msg_len msg st = ()

let receive_message_token_has_sym_key_lem (#nc : config) (initiator is_psk : bool)
                                          (tk : message_token) (msg : bytes)
                                          (st : handshake_state nc) :
  Lemma(
    match receive_message_token initiator is_psk tk msg st with
    | Fail _ -> True
    | Res (_, st') ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = Some? st'.sym_state.c_state.k in
      has_sym_key' == token_update_sym_key_flag has_sym_key is_psk tk) = ()

#push-options "--z3rlimit 50 --fuel 1"
let rec receive_message_tokens_has_sym_key_lem (#nc : config)
                                               (initiator is_psk : bool)
                                               (pattern : list message_token)
                                               (msg : bytes) (st : handshake_state nc) :
  Lemma(
  match receive_message_tokens initiator is_psk pattern msg st with
    | Fail _ -> True
    | Res (_, st') ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = Some? st'.sym_state.c_state.k in
      has_sym_key' == tokens_update_sym_key_flag has_sym_key is_psk pattern) =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    receive_message_token_has_sym_key_lem initiator is_psk tk msg st;
    match receive_message_token initiator is_psk tk msg st with
    | Fail _ -> ()
    | Res (msg1, st1) ->
      receive_message_tokens_has_sym_key_lem initiator is_psk pattern' msg1 st1
#pop-options

let rec receive_message_tokens_nout #nc initiator is_psk pattern #msg_len msg st =
  match pattern with
  | [] -> Res st
  | tk :: pattern' ->
    let tk_msg_len = token_message_size nc (Some? st.sym_state.c_state.k) tk in
    (**) assert(length msg >= tk_msg_len);
    let tk_msg, msg' = split_bytes msg tk_msg_len in
    match receive_message_token_nout initiator is_psk tk #tk_msg_len tk_msg st with
    | Fail e -> Fail e
    | Res st' ->
       (**) receive_message_token_nout_has_sym_key_lem initiator is_psk tk #tk_msg_len tk_msg st;
       (**) assert(tokens_message_size nc (Some? st.sym_state.c_state.k) is_psk pattern ==
                     token_message_size nc (Some? st.sym_state.c_state.k) tk +
                     tokens_message_size nc (Some? st'.sym_state.c_state.k) is_psk pattern');
       receive_message_tokens_nout initiator is_psk pattern' #(length msg') msg' st'

let receive_message_tokens_nout_nil_lem #nc initiator is_psk st = ()

let receive_message_tokens_nout_unfold_lem #nc initiator is_psk tk tokens #msg_len msg st = ()

#push-options "--fuel 2 --ifuel 2"
let receive_message_tokens_nout_one_token_lem #nc initiator is_psk tk #msg_len msg st = ()
#pop-options

#push-options "--z3rlimit 100"
let receive_message_token_eq #nc initiator is_psk tk #tk_msg_len tk_msg #msg_len msg st =
  match tk with
  | SS | EE | ES | SE | PSK -> ()
  | S | E ->
    let cmsg = concat tk_msg msg in
    assert(length cmsg == tk_msg_len + msg_len);
    assert(tk_msg_len <= length cmsg);
    let r = receive_message_token initiator is_psk tk cmsg st in
    let r' = receive_message_token_nout initiator is_psk tk #tk_msg_len tk_msg st in
    let tk_msg', msg'' = split_bytes cmsg tk_msg_len in
    assert(cmsg `Lib.Sequence.equal` (concat tk_msg' msg''));
    assert(msg'' `Lib.Sequence.equal` msg);
    assert(tk_msg' `Lib.Sequence.equal` tk_msg)
#pop-options

#push-options "--z3rlimit 200 --fuel 1"
let rec receive_message_tokens_eq #nc initiator is_psk pattern #msg_len msg
                                  #payload_length payload st =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    (* *)
    let cmsg = concat #uint8 #(length msg) #(length payload) msg payload in
    let r = receive_message_tokens initiator is_psk pattern cmsg st in
    let r' = receive_message_tokens_nout initiator is_psk pattern #msg_len msg st in
    (* Recursive call *)
    let r1 = receive_message_token initiator is_psk tk cmsg st in
    let tk_msg_len = token_message_size nc (Some? st.sym_state.c_state.k) tk in
    let tk_msg, msg1 = split_bytes msg tk_msg_len in
    let r1' = receive_message_token_nout initiator is_psk tk #tk_msg_len tk_msg st in
    let tk_msg', cmsg_end = split_bytes cmsg tk_msg_len in
    assert(cmsg `Seq.equal` (Seq.append tk_msg' cmsg_end));
    assert(tk_msg' `Seq.equal` tk_msg);
    assert(cmsg_end `Seq.equal` (Seq.append msg1 payload));
    receive_message_token_eq initiator is_psk tk #tk_msg_len tk_msg
                             #(length cmsg_end) cmsg_end st;
    match r1, r1' with
    | Fail e1, Fail e1' ->
      assert(e1 == e1');
      assert(r == Fail e1);
      assert(r' == Fail e1')
    | Fail _, _ | _, Fail _ -> ()
    | Res (msg1', st1), Res st1' ->
      assert(st1 == st1');
      assert(msg1' `Seq.equal` cmsg_end);
      receive_message_tokens_eq initiator is_psk pattern' #(length msg1) msg1 #payload_length
                                payload st1
#pop-options

let receive_message_tokens_nout_has_sym_key_lem #nc initiator is_psk pattern #msg_len msg st =
  assert(msg `equal` (concat msg lbytes_empty));
  receive_message_tokens_eq initiator is_psk pattern #msg_len msg #0 lbytes_empty st;
  receive_message_tokens_has_sym_key_lem initiator is_psk pattern msg st

#push-options "--fuel 1 --ifuel 2"
let receive_message_tokens_nout_with_payload =
  fun #nc initiator is_psk pattern #msg_len msg #payload_length payload st ->
  match receive_message_tokens_nout initiator is_psk pattern #msg_len msg st with
  | Fail e -> Fail e
  | Res st1 ->
    (**) receive_message_tokens_nout_has_sym_key_lem initiator is_psk pattern #msg_len msg st;
    (**) let has_sym_key = Some? st.sym_state.c_state.k in
    (**) let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pattern in
    (**) assert(Some? st1.sym_state.c_state.k == has_sym_key');
    match decrypt_and_hash payload st1.sym_state with
    | Fail e -> Fail e
    | Res (plain, sym_state1) ->
      Res (plain, {st1 with sym_state = sym_state1})
#pop-options

let receive_message_tokens_nout_with_payload_unfold_lem =
  fun #nc initiator is_psk pattern #msg_len msg #payload_length payload st ->
  ()

#push-options "--ifuel 2"
let receive_message_tokens_with_payload_eq #nc initiator is_psk pattern #msg_len msg
                                           #payload_length payload st =
  receive_message_tokens_eq initiator is_psk pattern #msg_len msg
                            #payload_length payload st
#pop-options

(*** Decomposition lemmas *)

let rec tokens_message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end =
  match tokens_beg with
  | [] -> ()
  | tk :: tokens_beg' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    tokens_message_size_decompose_lem nc has_sym_key' is_psk tokens_beg' tokens_end

let rec message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end payload_length =
  match tokens_beg with
  | [] -> ()
  | tk :: tokens_beg' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    message_size_decompose_lem nc has_sym_key' is_psk tokens_beg' tokens_end payload_length

/// Small helper to stabilize the below proof
let split_helper_lem (l tk_length tokens_length : size_nat) (msg : lbytes l) :
  Lemma
  (requires (tk_length <= tokens_length /\ tokens_length <= l))
  (ensures (
    let tk_msg, msg' = Seq.split msg tk_length in
    let msg1, msg2 = Seq.split msg tokens_length in
    let msg1', msg2' = Seq.split msg' (tokens_length - tk_length) in
    Seq.equal msg1 (Seq.append tk_msg msg1') /\
    Seq.equal msg2 msg2')) = ()

let rec receive_message_tokens_nout_decompose_lem #nc initiator is_psk tokens_beg tokens_end
                                                  #msg_length msg st =
  match tokens_beg with
  | [] -> ()
  | tk :: tokens_beg' ->
    let has_sym_key = Some? st.sym_state.c_state.k in
    let tk_msg_length = token_message_size nc has_sym_key tk in
    let tk_msg, msg' = split_bytes msg tk_msg_length in
    match receive_message_token_nout initiator is_psk tk #tk_msg_length tk_msg st with
    | Fail e -> ()
    | Res st' ->
       receive_message_token_nout_has_sym_key_lem initiator is_psk tk #tk_msg_length tk_msg st;
       receive_message_tokens_nout_decompose_lem initiator is_psk tokens_beg' tokens_end
                                                 #(length msg') msg' st';
       tokens_message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end;
       let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
       let msg1, msg2 = Seq.split msg (tokens_message_size nc has_sym_key is_psk tokens_beg) in
       let msg1', msg2' = Seq.split msg' (tokens_message_size nc has_sym_key' is_psk tokens_beg') in
       (* Without this helper, the below assertions take a huge time to be proven.
        * Note that we use '==' on purpose: we want to check that the helper gives
        * use the equalities we need, while preventing Z3 from applying SMT patterns
        * to prove them without the helper. *)
       split_helper_lem msg_length tk_msg_length (tokens_message_size nc has_sym_key is_psk tokens_beg) msg;
       assert(msg1 == (Seq.append tk_msg msg1'));
       assert(msg2 == msg2')

let receive_message_tokens_nout_with_payload_decompose_lem #nc initiator is_psk tokens_beg tokens_end
                                                           #msg_length msg #payload_length payload st =
  let tokens = List.Tot.append tokens_beg tokens_end in
  receive_message_tokens_nout_decompose_lem #nc initiator is_psk tokens_beg tokens_end
                                            #msg_length msg st;
  match receive_message_tokens_nout initiator is_psk tokens #msg_length msg st with
  | Fail e -> ()
  | Res st1 ->
    (**) receive_message_tokens_nout_has_sym_key_lem initiator is_psk tokens #msg_length msg st;
    (**) let has_sym_key = Some? st.sym_state.c_state.k in
    (**) let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    (**) assert(Some? st1.sym_state.c_state.k == has_sym_key');
    match decrypt_and_hash payload st1.sym_state with
    | Fail e -> ()
    | Res (plain, sym_state1) -> ()
