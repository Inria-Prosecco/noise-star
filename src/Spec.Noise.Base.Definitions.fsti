module Spec.Noise.Base.Definitions

open FStar.Mul

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.Noise.CryptoPrimitives

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Exceptions *)
type result (a b : Type) = | Res : v:a -> result a b | Fail : v:b -> result a b

type pre_error =
| PE_no_key
| PE_already_key
| PE_input_size

type error =
| No_key          (* Missing key *)
| Already_key     (* Key already received: we can't send/receive twice the same key *)
| Input_size      (* Not valid input size (too short, or longer than max_size_t) *)
| DH              (* Result of DH is trivial *)
| Decryption      (* Decryption failed *)
| Saturated_nonce (* Value of the nonce (counter) is 2^64 - 1: we can't increment it *)

let peresult (a : Type) = result a pre_error
let eresult (a : Type) = result a error

(*** Cipher state *)

noeq type cipher_state = {
  k : option aead_key;
  n : nat;
}

inline_for_extraction noextract
let saturated_nonce_value : nat = pow2 64 - 1

val initialize_key : option aead_key -> Tot cipher_state
val has_key : cipher_state -> Tot bool
val set_nonce : nat -> cipher_state -> Tot cipher_state

val encrypt_with_ad : nc:config -> aad:bytes -> plain:bytes -> cipher_state ->
                      Tot (eresult (bytes & cipher_state))
val decrypt_with_ad : nc:config -> aad:bytes -> cipher:bytes -> cipher_state ->
                      Tot (eresult (bytes & cipher_state))

(*** Symmetric state *)

noeq type symmetric_state (nc : config) = {
  c_state : cipher_state;
  ck : chaining_key nc;
  h : hash nc;
}

val initialize_symmetric :
     #nc : config
  -> protocol_name : hashable nc
  -> Tot (symmetric_state nc)

val mix_key : #nc:config -> hashable_key nc -> symmetric_state nc -> Tot (symmetric_state nc)
val mix_hash : #nc:config -> hashable nc -> symmetric_state nc -> Tot (symmetric_state nc)
val mix_key_and_hash : #nc:config -> hashable_key nc -> (symmetric_state nc) ->
                       Tot (symmetric_state nc)

(* No need for a get_handshake_hash function *)

val encrypt_and_hash : #nc:config -> plain_message nc -> symmetric_state nc ->
                       Tot (eresult (bytes & (symmetric_state nc)))
val decrypt_and_hash : #nc:config -> hashable nc -> symmetric_state nc ->
                       Tot (eresult (bytes & (symmetric_state nc)))

let cipher_states_pair = cipher_state & cipher_state

val split : #nc:config -> symmetric_state nc -> Tot cipher_states_pair

(*** Handshake state *)
/// TODO: we shouldn't store keypairs in the spec, but rather "valid" private
/// keys (from which we know we can derive a public key)
noeq type handshake_state (nc : config) = {
  sym_state : symmetric_state nc;
  static : option (keypair nc);
  ephemeral : option (keypair nc);
  remote_static : option (public_key nc);
  remote_ephemeral : option (public_key nc);
  preshared : option preshared_key;
}

val initialize_handshake_state :
     #nc : config
  -> protocol_name : hashable nc
  -> prologue : hashable nc
  -> s : option (keypair nc)
  -> e : option (keypair nc)
  -> rs : option (public_key nc)
  -> re : option (public_key nc)
  -> psk : option preshared_key
  -> Tot (handshake_state nc)

let set_psk : #nc:config -> preshared_key -> handshake_state nc -> Tot (handshake_state nc) =
  fun #nc psk st -> { st with preshared = Some psk; }

(** Some facility functions (not in Wireguard spec) *)
let has_symmetric_key : #nc:config -> handshake_state nc -> Tot bool =
  fun #nc state -> Some? state.sym_state.c_state.k
let get_nonce : #nc:config -> handshake_state nc -> Tot nat =
  fun #nc state -> state.sym_state.c_state.n

type message_token = | S | E | SS | EE | SE | ES | PSK
type premessage_token = | PS | PE

val send_premessage_token :
     #nc : config
  -> tk : premessage_token
  -> st : handshake_state nc
  -> Tot (peresult (bytes & (handshake_state nc)))

val receive_premessage_token :
     #nc : config
  -> tk : premessage_token
  -> msg : public_key nc
  -> st : handshake_state nc
  -> Tot (peresult (handshake_state nc))

val send_premessage_tokens :
     #nc : config
  -> list premessage_token
  -> handshake_state nc
  -> Tot (peresult (bytes & (handshake_state nc)))

let split_bytes (msg : bytes) (n : size_nat{n <= length msg}) : 
  Tot (bytes & bytes) =
  let msg1 = Seq.slice msg 0 n in
  let msg2 = Seq.slice msg n (length msg) in
  msg1, msg2

val receive_premessage_tokens :
     #nc : config
  -> list premessage_token
  -> bytes
  -> handshake_state nc
  -> Tot (peresult (handshake_state nc))

val dh_update :
     #nc : config
  -> bytes
  -> option (keypair nc)
  -> option (public_key nc)
  -> handshake_state nc
  -> Tot (eresult (bytes & (handshake_state nc)))

val send_message_token :
     #nc : config
  -> initiator : bool
  -> is_psk : bool 
  -> tk : message_token
  -> state : handshake_state nc
  -> Tot (eresult (bytes & (handshake_state nc)))

val receive_message_token :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> tk : message_token
  -> message : bytes
  -> state : handshake_state nc
  -> Tot (eresult (bytes & (handshake_state nc)))

val send_message_tokens :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> st : handshake_state nc
  -> Tot (eresult (bytes & (handshake_state nc)))

val send_message_tokens_with_payload :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> payload : plain_message nc
  -> st : handshake_state nc
  -> Tot (eresult (bytes & (handshake_state nc)))

val receive_message_tokens :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> msg : bytes
  -> st : handshake_state nc
  ->  Tot (eresult (bytes & (handshake_state nc)))

val receive_message_tokens_with_payload :
     #nc : config
  -> initiator : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> msg : bytes
  -> st : handshake_state nc
  ->  Tot (eresult ((hashable nc) & (handshake_state nc)))

// TODO: we shouldn't need keypairs
val initialize :
     #nc : config
  -> protocol_name : hashable nc
  -> prologue : hashable nc
  -> static_key : option (keypair nc)
  -> ephemeral_key : option (keypair nc)
  -> preshared_key : option preshared_key
  -> Tot (handshake_state nc)

(*** Patterns *)
type handshake_pattern = {
  name : string;
  premessage_ir : option (list premessage_token);
  premessage_ri : option (list premessage_token);
  messages : list (list message_token);
}

(*
 * [pre_ri [s];
 * ---------------
 * ir [e; es; s; ss];
 * ri [e; ee; se; psk]]
 *)
type message =
  | Pre_ir of list premessage_token
  | Pre_ri of list premessage_token
  | Ir of list message_token
  | Ri of list message_token

let hs_pre_msg (name : string) (ls : list message) :
  Tot (option (handshake_pattern & list message)) =
  match ls with
  | Pre_ir pir :: Pre_ri pri :: ls' ->
    Some ({ name = name; premessage_ir = Some pir; premessage_ri = Some pri; messages = []; }, ls')
  | Pre_ir pir :: ls' ->
    Some ({ name = name; premessage_ir = Some pir; premessage_ri = None; messages = []; }, ls')
  | Pre_ri pri :: ls' ->
    Some ({ name = name; premessage_ir = None; premessage_ri = Some pri; messages = []; }, ls')
  | _ ->
    Some ({ name = name; premessage_ir = None; premessage_ri = None; messages = []; }, ls)

let rec hs_msg (ir : bool) (ls : list message) :
  Tot (option (list (list message_token))) (decreases ls) =
  match ir, ls with
  | true, Ir tks::ls' ->
    (match hs_msg false ls' with
    | None -> None
    | Some msgs -> Some (tks::msgs))
  | false, Ri tks::ls' ->
    (match hs_msg true ls' with
    | None -> None
    | Some msgs -> Some (tks::msgs))
  | _, [] -> Some []
  | _ -> None

let hs_safe (name : string) (ls : list message) : option handshake_pattern =
  (* Process the pre-messages *)
  match hs_pre_msg name ls with
  | None -> None
  | Some (hsk, ls') ->
    (* Process the messages *)
    match hs_msg true ls' with
    | None -> None
    | Some msgs ->
      Some ({ hsk with messages = msgs })

let hs (name : string) (ls : list message) :
  Pure handshake_pattern
  (requires (normalize_term (Some? (hs_safe name ls) == true)))
  (ensures (fun _ -> True))
  =
  normalize_term (Some?.v (hs_safe name ls))

let ( ~>>~ ) (pat : list premessage_token) = Pre_ir pat
let ( ~<<~ ) (pat : list premessage_token) = Pre_ri pat
let ( ~>~ ) (pat : list message_token) = Ir pat
let ( ~<~ ) (pat : list message_token) = Ri pat

(*
let pattern_IKpsk2 =
  hs "IKpsk2" [
    ~<<~ [PS];
    ~>~ [E; ES; S; SS];
    ~<~ [E; EE; SE; PSK]
  ]
*)

(*** "Compilation" *)
/// Derive top-level specification functions from a pattern

inline_for_extraction noextract
let is_even (n : nat) : bool = ((n % 2) = 0)

(** Structure containing the functions used for a handshake, without payload *)
type send_premessage_function (nc : config) =
  handshake_state nc -> Tot (peresult (bytes & (handshake_state nc)))
type receive_premessage_function (nc : config) =
  bytes -> handshake_state nc -> Tot (peresult (handshake_state nc))
type send_message_function (nc : config) =
  plain_message nc -> handshake_state nc -> Tot (eresult (bytes & (handshake_state nc)))
type receive_message_function (nc : config) =
  bytes -> handshake_state nc -> Tot (eresult ((hashable nc) & (handshake_state nc)))

// Do not use strict_on_arguments here: causes loops at type inference
// in [Impl.Noise.API.DState.mk_dstate_t_create]
let check_hsk_is_psk (hsk : handshake_pattern) : Tot bool =
  List.Tot.existsb (List.Tot.mem PSK) hsk.messages

(** Individual functions *)
let has_premessage (hsk : handshake_pattern) (ir : bool) : bool =
  if ir then Some? hsk.premessage_ir else Some? hsk.premessage_ri

noextract
let csend_premessage (nc : config)
                     (hsk : handshake_pattern)
                     (ir : bool{has_premessage hsk ir}) :
  send_premessage_function nc =
  let is_psk = check_hsk_is_psk hsk in
  let pre = if ir then Some?.v hsk.premessage_ir else Some?.v hsk.premessage_ri in
  send_premessage_tokens pre

noextract
let creceive_premessage (nc : config)
                        (hsk : handshake_pattern)
                        (ir : bool{has_premessage hsk ir}) :
  receive_premessage_function nc =
  let is_psk = check_hsk_is_psk hsk in
  let pre = if ir then Some?.v hsk.premessage_ir else Some?.v hsk.premessage_ri in
  receive_premessage_tokens pre

noextract
let csend_message (nc : config)
                  (hsk : handshake_pattern)
                  (i : nat{i < List.Tot.length hsk.messages}) :
  send_message_function nc =
  let is_psk = check_hsk_is_psk hsk in
  let initiator = (i%2)=0 in
  let tokens = List.Tot.index hsk.messages i in
  send_message_tokens_with_payload initiator is_psk tokens

noextract
let creceive_message (nc : config)
                     (hsk : handshake_pattern)
                     (i : nat{i < List.Tot.length hsk.messages}) :
  receive_message_function nc =
  let is_psk = check_hsk_is_psk hsk in
  let initiator = (i%2)=1 in
  let tokens = List.Tot.index hsk.messages i in
  receive_message_tokens_with_payload initiator is_psk tokens

(** Protocol name computation *)
/// For now, we only derive the procotol name from the pattern name and the
/// chosen algorithms. We don't compute the pattern name from the pattern itself.
/// We only use the patterns listed in the Noise technical paper anyway.

noextract
let string_of_dh (nc : config) =
  match get_dh_alg nc with
  | Spec.Agile.DH.DH_Curve25519 -> "25519"

let string_of_aead (nc: config) =
  match get_aead_alg nc with
  | Spec.Agile.AEAD.AES256_GCM -> "AESGCM"
  | Spec.Agile.AEAD.CHACHA20_POLY1305 -> "ChaChaPoly"

let string_of_hash (nc: config) =
  match get_hash_alg nc with
  | Spec.Agile.Hash.SHA2_256 -> "SHA256"
  | Spec.Agile.Hash.SHA2_512 -> "SHA512"
  | Spec.Agile.Hash.Blake2S -> "BLAKE2s"
  | Spec.Agile.Hash.Blake2B -> "BLAKE2b"

noextract
let compute_protocol_name (pattern_name : string) (nc : config) =
  let dh_name = string_of_dh nc in
  let aead_name = string_of_aead nc in
  let hash_name = string_of_hash nc in
  "Noise_" ^ pattern_name ^ "_" ^ dh_name ^ "_" ^ aead_name ^ "_" ^ hash_name

