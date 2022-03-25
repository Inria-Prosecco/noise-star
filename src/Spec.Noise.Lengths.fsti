module Spec.Noise.Lengths

open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence
module L = LowStar.Literal

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.HandshakeFlags

#set-options "--z3rlimit 15 --fuel 1 --ifuel 1"

(*** Protocol name *)

let string_of_dh_length (nc : config) : n:nat{n = String.length (string_of_dh nc)} =
  (**) normalize_term_spec (String.length "25519");
  match get_dh_alg nc with
  | Spec.Agile.DH.DH_Curve25519 -> 5

let string_of_aead_length (nc: config) : n:nat{n = String.length (string_of_aead nc)} =
  (**) normalize_term_spec (String.length "AESGCM");
  (**) normalize_term_spec (String.length "ChaChaPoly");
  match get_aead_alg nc with
  | Spec.Agile.AEAD.AES256_GCM -> 6
  | Spec.Agile.AEAD.CHACHA20_POLY1305 -> 10

let string_of_hash_length (nc: config) : n:nat{n = String.length (string_of_hash nc)} =
  (**) normalize_term_spec (String.length "SHA256");
  (**) normalize_term_spec (String.length "SHA512");
  (**) normalize_term_spec (String.length "BLAKE2s");
  (**) normalize_term_spec (String.length "BLAKE2b");
  match get_hash_alg nc with
  | Spec.Agile.Hash.SHA2_256 -> 6
  | Spec.Agile.Hash.SHA2_512 -> 6
  | Spec.Agile.Hash.Blake2S -> 7
  | Spec.Agile.Hash.Blake2B -> 7

let protocol_name_length (patlength : nat) (nc: config) : nat =
  patlength + 9 + string_of_dh_length nc + string_of_aead_length nc + string_of_hash_length nc

val protocol_name_length_eq (pat: string) (nc: config) :
  Lemma (String.length (compute_protocol_name pat nc) = protocol_name_length (String.length pat) nc)

val protocol_name_length_lem (patlength : nat) (nc: config) :
  Lemma (protocol_name_length patlength nc <= patlength + 31)

val protocol_name_ascii_lem (pat: string) (c: config): Lemma
  (requires (L.is_ascii_string pat))
  (ensures (L.is_ascii_string (compute_protocol_name pat c)))
  [ SMTPat (L.is_ascii_string (compute_protocol_name pat c)) ]

(*** Length functions *)
inline_for_extraction noextract
let encrypt_size (n : nat) : Tot nat =
  n + aead_tag_size

inline_for_extraction noextract
let opt_encrypt_size (encrypt : bool) (n : nat) :
  Tot nat =
  if encrypt then encrypt_size n else n

inline_for_extraction noextract
let decrypt_size (n : size_nat{n >= encrypt_size 0}) : Tot size_nat =
  n - aead_tag_size

inline_for_extraction noextract
let opt_decrypt_size (has_sym_key : bool)
  (l : size_nat{l >= opt_encrypt_size has_sym_key 0}) =
  if has_sym_key then decrypt_size l else l

inline_for_extraction noextract
let token_message_size (nc : config) (has_sym_key : bool) (tk : message_token) :
  size_nat =
  match tk with
  | S -> opt_encrypt_size has_sym_key (public_key_size nc)
  | E -> public_key_size nc
  | _ -> 0

inline_for_extraction noextract
let rec tokens_message_size (nc : config)
                            (has_sym_key is_psk : bool)
                            (pattern : list message_token) :
  Tot nat (decreases pattern) =
  match pattern with
  | [] -> 0
  | tk :: pattern' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    let tk_msg_len = token_message_size nc has_sym_key tk in
    let end_msg_len = tokens_message_size nc has_sym_key' is_psk pattern' in
    tk_msg_len + end_msg_len

inline_for_extraction noextract
let max_public_key_size : size_nat = apublic_key_size Spec.Agile.DH.DH_Curve25519

// There is only one option for now...
inline_for_extraction noextract
let min_public_key_size : size_nat = apublic_key_size Spec.Agile.DH.DH_Curve25519

inline_for_extraction noextract
let max_token_message_size (has_sym_key : bool) (tk : message_token) :
  size_nat =
  match tk with
  | S -> opt_encrypt_size has_sym_key max_public_key_size
  | E -> max_public_key_size
  | _ -> 0

inline_for_extraction noextract
let min_token_message_size (has_sym_key : bool) (tk : message_token) :
  size_nat =
  match tk with
  | S -> opt_encrypt_size has_sym_key max_public_key_size
  | E -> min_public_key_size
  | _ -> 0

inline_for_extraction noextract
let rec max_tokens_message_size (has_sym_key is_psk : bool)
                                (pattern : list message_token) :
  Tot nat (decreases pattern) =
  match pattern with
  | [] -> 0
  | tk :: pattern' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    let tk_msg_len = max_token_message_size has_sym_key tk in
    let end_msg_len = max_tokens_message_size has_sym_key' is_psk pattern' in
    tk_msg_len + end_msg_len

inline_for_extraction noextract
let rec min_tokens_message_size (has_sym_key is_psk : bool)
                                (pattern : list message_token) :
  Tot nat (decreases pattern) =
  match pattern with
  | [] -> 0
  | tk :: pattern' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    let tk_msg_len = max_token_message_size has_sym_key tk in
    let end_msg_len = min_tokens_message_size has_sym_key' is_psk pattern' in
    tk_msg_len + end_msg_len

inline_for_extraction noextract
let message_size
  (nc : config)
  (has_sym_key is_psk : bool)
  (pattern : list message_token)
  (payload_length : size_nat) =
  let l1 = tokens_message_size nc has_sym_key is_psk pattern in
  let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pattern in
  let l2 = opt_encrypt_size has_sym_key' payload_length in
  l1 + l2

inline_for_extraction noextract
let max_message_size
  (has_sym_key is_psk : bool)
  (pattern : list message_token)
  (payload_length : size_nat) =
  let l1 = max_tokens_message_size has_sym_key is_psk pattern in
  let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pattern in
  let l2 = opt_encrypt_size has_sym_key' payload_length in
  l1 + l2

inline_for_extraction noextract
let min_message_size
  (has_sym_key is_psk : bool)
  (pattern : list message_token)
  (payload_length : size_nat) =
  let l1 = min_tokens_message_size has_sym_key is_psk pattern in
  let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pattern in
  let l2 = opt_encrypt_size has_sym_key' payload_length in
  l1 + l2

(*** Lemmas *)
(**** Lemmas: send_message_token *)

val token_message_size_lem :
     #nc : config  
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> st : handshake_state nc ->
  Lemma(
    match send_message_token initiator is_psk tk st with
    | Fail _ -> True
    | Res (out, _) ->
      length out == token_message_size nc (Some? st.sym_state.c_state.k) tk)

val max_tokens_message_size_lem (nc : config)
                                (has_sym_key is_psk : bool)
                                (pattern : list message_token) :
  Lemma
  (requires True)
  (ensures (
    tokens_message_size nc has_sym_key is_psk pattern
    <= max_tokens_message_size has_sym_key is_psk pattern))
  (decreases pattern)

val min_tokens_message_size_lem (nc : config)
                                (has_sym_key is_psk : bool)
                                (pattern : list message_token) :
  Lemma
  (requires True)
  (ensures (
    min_tokens_message_size has_sym_key is_psk pattern
    <= tokens_message_size nc has_sym_key is_psk pattern))
  (decreases pattern)
  
(**** Lemmas: send_message_tokens *)

val tokens_message_size_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> st : handshake_state nc ->
  Lemma
  (requires True)
  (ensures 
    begin match send_message_tokens initiator is_psk pattern st with
    | Fail _ -> True
    | Res (out, _) ->
      length out == tokens_message_size nc (Some? st.sym_state.c_state.k)
                                                    is_psk pattern end)
  (decreases pattern)

val decrypt_and_hash_output_len_lemma :
      #nc : config
   -> cipher : hashable nc
   -> st : symmetric_state nc{Some? st.c_state.k}
   -> Lemma(match decrypt_and_hash cipher st with
           | Res (p, _) -> length cipher >= aead_tag_size /\
                           length p == length cipher - aead_tag_size
           | Fail _ -> True)

val message_size_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> payload : plain_message nc
  -> st : handshake_state nc ->
  Lemma
  (requires True)
  (ensures 
    begin match send_message_tokens_with_payload initiator is_psk pattern payload st with
    | Fail _ -> True
    | Res (out, _) ->
      length out == message_size nc (Some? st.sym_state.c_state.k)
                                    is_psk pattern (length payload) end)
  (decreases pattern)

(*** receive_message_tokens_outlen *)
(* We prove that receive_message_tokens is equivalent to another function, more convenient
 * to use to prove that the implementation is correct *)
inline_for_extraction noextract
let receive_msg_tk_outlen (nc : config) (tk : message_token) : size_nat =
  match tk with
  | S | E -> public_key_size nc
  | _ -> 0

val dh_update_nout :
     #nc : config
  -> option (keypair nc)
  -> option (public_key nc)
  -> handshake_state nc
  -> Tot (eresult (handshake_state nc))

val receive_message_token_nout :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> #message_len : size_nat
  -> message : lbytes message_len
  -> st : handshake_state nc
  -> Pure (eresult (handshake_state nc))
  (requires (message_len == token_message_size nc (Some? st.sym_state.c_state.k) tk))
  (ensures (fun _ -> True))

private
val receive_message_token_nout_has_sym_key_lem :
      #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> st : handshake_state nc ->
  Lemma
  (requires (msg_len == token_message_size nc (Some? st.sym_state.c_state.k) tk))
  (ensures
    (match receive_message_token_nout initiator is_psk tk #msg_len msg st with
    | Fail _ -> True
    | Res st' ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = Some? st'.sym_state.c_state.k in
      has_sym_key' == token_update_sym_key_flag has_sym_key is_psk tk))

val receive_message_tokens_nout :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> st : handshake_state nc
  ->  Pure (eresult (handshake_state nc))
  (requires
    (msg_len == tokens_message_size nc (Some? st.sym_state.c_state.k) is_psk pattern))
  (ensures (fun _ -> True))

val receive_message_tokens_nout_nil_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> st : handshake_state nc ->
  Lemma
  (requires True)
  (ensures (
    receive_message_tokens_nout #nc initiator is_psk [] #0 Seq.empty st == Res st))

val receive_message_tokens_nout_unfold_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> tokens : list message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> st : handshake_state nc ->
  Lemma
  (requires
    (msg_len == tokens_message_size nc (Some? st.sym_state.c_state.k) is_psk (tk :: tokens)))
  (ensures (
    receive_message_tokens_nout #nc initiator is_psk (tk :: tokens) #msg_len msg st ==
    begin
    let tk_msg_len = token_message_size nc (Some? st.sym_state.c_state.k) tk in
    let tk_msg, msg' = split_bytes msg tk_msg_len in
    match receive_message_token_nout initiator is_psk tk #tk_msg_len tk_msg st with
    | Fail e -> Fail e
    | Res st' ->
       (**) receive_message_token_nout_has_sym_key_lem initiator is_psk tk #tk_msg_len tk_msg st;
       receive_message_tokens_nout initiator is_psk tokens #(length msg') msg' st'
    end))

val receive_message_tokens_nout_one_token_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> st : handshake_state nc ->
  Lemma
  (requires
    (msg_len == tokens_message_size nc (Some? st.sym_state.c_state.k) is_psk [tk]))
  (ensures (
    receive_message_tokens_nout #nc initiator is_psk [tk] #msg_len msg st ==
    begin
    let tk_msg_len = token_message_size nc (Some? st.sym_state.c_state.k) tk in
    let tk_msg, msg' = split_bytes msg tk_msg_len in
    receive_message_token_nout initiator is_psk tk #tk_msg_len tk_msg st
    end))

#push-options "--fuel 1"
val receive_message_token_eq :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> #tk_msg_len : size_nat
  -> tk_msg : lbytes tk_msg_len
  -> #msg_len : size_nat{tk_msg_len + msg_len <= max_size_t}
  -> msg : lbytes msg_len
  -> st : handshake_state nc
  -> Lemma
  (requires
    (tk_msg_len == token_message_size nc (Some? st.sym_state.c_state.k) tk))
  (ensures
    begin
    let cmsg = concat tk_msg msg in
    let r = receive_message_token initiator is_psk tk cmsg st in
    let r' = receive_message_token_nout initiator is_psk tk #tk_msg_len tk_msg st in
    match r, r' with
    | Fail e1, Fail e2 -> e1 == e2
    | Res (msg', st1), Res st2 ->
      length msg' == length msg /\
      msg' `Lib.Sequence.equal` msg /\
      st1 == st2
    | _ -> False
    end)
#pop-options

#push-options "--fuel 1"
val receive_message_tokens_eq :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> #payload_length : size_nat{msg_len + payload_length <= max_size_t}
  -> payload : lbytes payload_length
  -> st : handshake_state nc
  -> Lemma
  (requires
    (msg_len == tokens_message_size nc (Some? st.sym_state.c_state.k) is_psk pattern))
  (ensures
    begin
    let cmsg = concat #uint8 #(length msg) #(length payload) msg payload in
    let r = receive_message_tokens initiator is_psk pattern cmsg st in
    let r' = receive_message_tokens_nout initiator is_psk pattern #msg_len msg st in
    match r, r' with
    | Fail e1, Fail e2 -> e1 == e2
    | Res (payload', st1), Res st2 ->
      length payload' == length payload /\
      payload' `Lib.Sequence.equal` payload /\
      st1 == st2
    | _ -> False
    end)
#pop-options

val receive_message_tokens_nout_has_sym_key_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> st : handshake_state nc
  -> Lemma
  (requires
    (msg_len == tokens_message_size nc (Some? st.sym_state.c_state.k) is_psk pattern))
  (ensures
    begin match receive_message_tokens_nout initiator is_psk pattern #msg_len msg st with
    | Fail _ -> True
    | Res st' ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = Some? st'.sym_state.c_state.k in
      has_sym_key' == tokens_update_sym_key_flag has_sym_key is_psk pattern
    end)

val receive_message_tokens_nout_with_payload :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> #payload_length : size_nat{msg_len + payload_length <= max_size_t}
  -> payload : lbytes payload_length {is_hashable nc payload}
  -> st : handshake_state nc
  ->  Pure (eresult (bytes & (handshake_state nc)))
  (requires
    (let has_sym_key = Some? st.sym_state.c_state.k in
     let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pattern in
     msg_len == tokens_message_size nc has_sym_key is_psk pattern /\
     payload_length >= opt_encrypt_size has_sym_key' 0))
  (ensures (fun r ->
    match r with
    | Fail _ -> True
    | Res (plain, st') ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pattern in
      length plain == opt_decrypt_size has_sym_key' payload_length))

val receive_message_tokens_nout_with_payload_unfold_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> #payload_length : size_nat{msg_len + payload_length <= max_size_t}
  -> payload : lbytes payload_length {is_hashable nc payload}
  -> st : handshake_state nc ->
  Lemma
  (requires
    (let has_sym_key = Some? st.sym_state.c_state.k in
     let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pattern in
     msg_len == tokens_message_size nc has_sym_key is_psk pattern /\
     payload_length >= opt_encrypt_size has_sym_key' 0))
  (ensures (
    receive_message_tokens_nout_with_payload initiator is_psk pattern msg payload st ==
    begin match receive_message_tokens_nout initiator is_psk pattern #msg_len msg st with
    | Fail e -> Fail e
    | Res st1 ->
      match decrypt_and_hash payload st1.sym_state with
      | Fail e -> Fail e
      | Res (plain, sym_state1) ->
        Res (plain, {st1 with sym_state = sym_state1})
    end))

val receive_message_tokens_with_payload_eq :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> #msg_len : size_nat
  -> msg : lbytes msg_len
  -> #payload_length : size_nat{msg_len + payload_length <= max_size_t}
  -> payload : lbytes payload_length {is_hashable nc payload}
  -> st : handshake_state nc
  ->  Lemma
  (requires
    (let has_sym_key = Some? st.sym_state.c_state.k in
     let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pattern in
     msg_len == tokens_message_size nc has_sym_key is_psk pattern /\
     payload_length >= opt_encrypt_size has_sym_key' 0))
  (ensures
    begin
    let cmsg = concat #uint8 #(length msg) #(length payload) msg payload in
    let r = receive_message_tokens_with_payload initiator is_psk pattern cmsg st in
    let r' = receive_message_tokens_nout_with_payload initiator is_psk pattern #msg_len msg
                                                      #payload_length payload st in
    match r, r' with
    | Fail e, Fail e' -> e == e'
    | Res (plain, st1), Res (plain', st1') ->
      (* We use == rather then 'Lib.Sequence.equal' on purpose *)
      plain == plain' /\
      st1 == st1'
    | _ -> False
    end)

(*** Decomposition lemmas *)

val tokens_message_size_decompose_lem :
     nc : config
  -> has_sym_key : bool
  -> is_psk : bool
  -> tokens_beg : list message_token
  -> tokens_end : list message_token ->
  Lemma
  (ensures (
    let tokens = List.Tot.append tokens_beg tokens_end in
    let l1 = tokens_message_size nc has_sym_key is_psk tokens in
    let l2 = tokens_message_size nc has_sym_key is_psk tokens_beg in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens_beg in
    let l3 = tokens_message_size nc has_sym_key' is_psk tokens_end in
    l1 = l2 + l3))
  (decreases tokens_beg)

val message_size_decompose_lem :
     nc : config
  -> has_sym_key : bool
  -> is_psk : bool
  -> tokens_beg : list message_token
  -> tokens_end : list message_token
  -> payload_length : size_nat -> //{payload_length + aead_tag_size + hash_size nc <= max_size_t} ->
  Lemma
  (ensures (
    let tokens = List.Tot.append tokens_beg tokens_end in
    let l1 = message_size nc has_sym_key is_psk tokens payload_length in
    let l2 = tokens_message_size nc has_sym_key is_psk tokens_beg in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens_beg in
    let l3 = message_size nc has_sym_key' is_psk tokens_end payload_length in
    l1 = l2 + l3))
  (decreases tokens_beg)

val receive_message_tokens_nout_decompose_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tokens_beg : list message_token
  -> tokens_end : list message_token
  -> #msg_length : size_nat
  -> msg : lbytes msg_length
  -> st : handshake_state nc
  ->  Lemma
  (requires
    (let tokens = List.Tot.append tokens_beg tokens_end in
     let has_sym_key = Some? st.sym_state.c_state.k in
     let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
     msg_length == tokens_message_size nc has_sym_key is_psk tokens))
  (ensures (
     let has_sym_key = Some? st.sym_state.c_state.k in
    (**) tokens_message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end;
    let msg1, msg2 = Seq.split msg (tokens_message_size nc has_sym_key is_psk tokens_beg) in
    let tokens = List.Tot.append tokens_beg tokens_end in
    let r1 = receive_message_tokens_nout initiator is_psk tokens #msg_length msg  st in
    let r2 = receive_message_tokens_nout initiator is_psk tokens_beg #(Seq.length msg1) msg1 st in
    match r1, r2 with
    | Fail e, _ -> True
    | Res st1, Res st2 ->
      (**) receive_message_tokens_nout_has_sym_key_lem #nc initiator is_psk tokens_beg #(Seq.length msg1) msg1 st;
      let r3 = receive_message_tokens_nout initiator is_psk tokens_end #(Seq.length msg2) msg2 st2 in
      begin match r3 with
      | Res st3 -> st1 == st3
      | _ -> False
      end
    | _ -> False
    ))
  (decreases tokens_beg)

val receive_message_tokens_nout_with_payload_decompose_lem :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tokens_beg : list message_token
  -> tokens_end : list message_token
  -> #msg_length : size_nat
  -> msg : lbytes msg_length
  -> #payload_length : size_nat{msg_length + payload_length <= max_size_t}
  -> payload : lbytes payload_length {is_hashable nc payload}
  -> st : handshake_state nc
  ->  Lemma
  (requires
    (let tokens = List.Tot.append tokens_beg tokens_end in
     let has_sym_key = Some? st.sym_state.c_state.k in
     let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
     msg_length == tokens_message_size nc has_sym_key is_psk tokens /\
     payload_length >= opt_encrypt_size has_sym_key' 0))
  (ensures (
     let has_sym_key = Some? st.sym_state.c_state.k in
    (**) tokens_message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end;
    let msg1, msg2 = Seq.split msg (tokens_message_size nc has_sym_key is_psk tokens_beg) in
    let tokens = List.Tot.append tokens_beg tokens_end in
    let r1 = receive_message_tokens_nout_with_payload initiator is_psk tokens #msg_length msg #payload_length payload st in
    let r2 = receive_message_tokens_nout initiator is_psk tokens_beg #(Seq.length msg1) msg1 st in
    match r1, r2 with
    | Fail e, _ -> True
    | Res (plain1, st1), Res st2 ->
      (**) message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end payload_length;
      (**) receive_message_tokens_nout_has_sym_key_lem #nc initiator is_psk tokens_beg #(Seq.length msg1) msg1 st;
      let r3 = receive_message_tokens_nout_with_payload initiator is_psk tokens_end #(Seq.length msg2) msg2 #payload_length payload st2 in
      begin match r3 with
      | Res (plain3, st3) ->
        (* We use == rather then 'Lib.Sequence.equal' on purpose *)
        plain1 == plain3 /\
        st1 == st3
      | _ -> False
      end
    | _ -> False
    ))
  (decreases tokens_beg)
