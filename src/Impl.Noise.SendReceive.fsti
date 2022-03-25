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
open Meta.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(* TODO: move those functions? *)
inline_for_extraction noextract
let token_message_vsv (nc : iconfig) (smi : meta_info) (tk : message_token) :
  Tot size_nat =
  token_message_size (get_config nc) smi.hsf.sk tk

inline_for_extraction noextract
let token_message_vs (nc : iconfig) (smi : meta_info) (tk : message_token) :
  Tot size_t =
  size (token_message_vsv nc smi tk)

inline_for_extraction noextract
type token_message_t (nc : iconfig) (smi : meta_info) (tk : message_token) =
  lbuffer uint8 (token_message_vs nc smi tk)

inline_for_extraction noextract
let tokens_message_vsv (nc : iconfig) (smi : meta_info) (is_psk : bool)
                       (pattern : list message_token) :
  Tot (n:nat{n == tokens_message_size (get_config nc) smi.hsf.sk is_psk pattern}) =
  (* We need to perform the normalization in 2 steps, otherwise it doesn't
   * work properly *)
  [@inline_let] let c = with_norm(get_config nc) in
  with_norm(tokens_message_size c smi.hsf.sk is_psk pattern)

inline_for_extraction noextract
let tokens_message_vs (nc : iconfig) (smi : meta_info) (is_psk : bool)
                      (pattern : list message_token) :
  Pure size_t
  (requires (tokens_message_vsv nc smi is_psk pattern <= max_size_t))
  (ensures (fun _ -> True)) =
  size (tokens_message_vsv nc smi is_psk pattern)

inline_for_extraction noextract
let message_vsv
  (nc : iconfig) (smi : meta_info) (is_psk : bool)
  (pattern : list message_token)
  (payload_len : size_nat{payload_len + aead_tag_size + hash_size (get_config nc) <= max_size_t}) :
  Tot (n:nat{n == message_size (get_config nc) smi.hsf.sk is_psk pattern payload_len}) =
  [@inline_let] let c = with_norm(get_config nc) in
  with_norm(message_size c smi.hsf.sk is_psk pattern payload_len)

/// In the following we define the return types for the send message functions.
/// Note that we try to be as precise as possible so as to remove as many tests
/// as we can, and use unit as the return type for our functions whenever possible.

/// Most general message return types (handle hash, dh and encryption/decryption
/// errors). Those types will be used in more precise types (which adapt the error
/// code precision to the pattern) defined below.
inline_for_extraction noextract
let send_prim_error_code : Type0 =
  r:prim_error_code{
    r == CSuccess \/ r == CDH_error}

inline_for_extraction noextract
let send_return_type : return_type =
  { prim_error_code_return_type with
    rty = send_prim_error_code; }

inline_for_extraction noextract
let receive_prim_error_code : Type0 =
  r:prim_error_code{
    r == CSuccess \/ r == CDH_error \/ r == CDecrypt_error}

inline_for_extraction noextract
let receive_return_type : return_type =
  { prim_error_code_return_type with
    rty = receive_prim_error_code; }

/// The following types and functions are used to statically compute information
/// about the operations performed in the pattern, in order to determine which
/// return type is relevant. For instance: hash, DH, encryption/decryption.
inline_for_extraction //noextract
type pattern_type_ops = {
  hash_op : bool;
  dh_op : bool;
  sk_op : bool;
  
  (* The following field is not directly used to compute the return type:
   * we need it to keep track whether there is a symmetric key in the cipher
   * state so as to compute correctly the [sk_op] field *)
  has_sk : bool;
}

let init_pto (has_sk : bool) : pattern_type_ops =
  { hash_op = false; dh_op = false; sk_op = false; has_sk = has_sk; }

/// [patter_type_ops] is monotonous over a pattern execution
noextract
let pto_less_than (pto0 pto1 : pattern_type_ops) : Tot bool =
  (pto1.hash_op || (not pto0.hash_op)) &&
  (pto1.dh_op || (not pto0.dh_op)) &&
  (pto1.sk_op || (not pto0.sk_op)) &&
  (pto1.has_sk || (not pto0.has_sk))

inline_for_extraction noextract
type greater_pto (pto0 : pattern_type_ops) =
  pto1:pattern_type_ops{pto_less_than pto0 pto1}

let pto_do_hash (pto : pattern_type_ops) : greater_pto pto =
  { pto with hash_op = true }

let pto_do_dh_hash (pto : pattern_type_ops) : greater_pto pto =
  { pto with hash_op = true; dh_op = true; has_sk = true; }

let pto_do_cipher_hash (pto : pattern_type_ops) : greater_pto pto =
  { pto with hash_op = true; sk_op = pto.sk_op || pto.has_sk }

let pto_do_mix_key_hash (pto : pattern_type_ops) : greater_pto pto =
  { pto with hash_op = true; has_sk = true }

/// Functions to compute a pto over a pattern
#push-options "--ifuel 1"
inline_for_extraction noextract
let token_update_pto (is_psk : bool) (tk : message_token)
                     (pto : pattern_type_ops) : greater_pto pto =
  match tk with
  | S -> pto_do_cipher_hash pto
  | E -> if is_psk then pto_do_mix_key_hash pto else pto_do_hash pto
  | SS | EE | SE | ES -> pto_do_dh_hash pto
  | PSK -> pto_do_mix_key_hash pto
#pop-options

inline_for_extraction noextract
let compute_token_pto (smi : meta_info) (is_psk : bool)
                      (tk : message_token) :
  Tot pattern_type_ops =
  with_norm (token_update_pto is_psk tk (init_pto smi.hsf.sk))

#push-options "--ifuel 1"
[@(strict_on_arguments [1])]
inline_for_extraction noextract
let rec tokens_update_pto (is_psk : bool) (pattern : list message_token)
                          (pto : pattern_type_ops) :
  Tot (greater_pto pto)
  (decreases pattern) =
  match pattern with
  | [] -> pto
  | tk :: pattern' ->
    tokens_update_pto is_psk pattern' (token_update_pto is_psk tk pto)
#pop-options

inline_for_extraction noextract
let compute_tokens_pto (smi : meta_info) (is_psk : bool)
                       (pattern : list message_token) :
  Tot pattern_type_ops =
  with_norm (tokens_update_pto is_psk pattern (init_pto smi.hsf.sk))

[@(strict_on_arguments [1])]
inline_for_extraction noextract
let message_update_pto (is_psk : bool) (pattern : list message_token)
                       (pto : pattern_type_ops) :
  Tot (greater_pto pto) =
  let pto1 = tokens_update_pto is_psk pattern pto in
  pto_do_cipher_hash pto1

// Don't put strict_on_arguments here: makes [send_message_tokens_with_payload_m] loop
inline_for_extraction noextract
let compute_message_pto (smi : meta_info) (is_psk : bool)
                        (pattern : list message_token) :
  Tot pattern_type_ops =
  with_norm (message_update_pto is_psk pattern (init_pto smi.hsf.sk))

/// Useful lemma, especially for type conversions
#push-options "--fuel 1 --ifuel 1"
let rec tokens_update_pto_monotonous (is_psk : bool)
                                     (pattern : list message_token)
                                     (pto0 pto1 : pattern_type_ops) :
  Lemma
  (requires (pto0 `pto_less_than` pto1))
  (ensures (
    tokens_update_pto is_psk pattern pto0 `pto_less_than`
      tokens_update_pto is_psk pattern pto1))
  (decreases pattern) =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    let pto0' = token_update_pto is_psk tk pto0 in
    let pto1' = token_update_pto is_psk tk pto1 in
    tokens_update_pto_monotonous is_psk pattern' pto0' pto1'
#pop-options

/// Consistency of the computation of the has_sk field:
let token_update_pto_has_sk_consistent (is_psk : bool) (tk : message_token)
                                       (pto : pattern_type_ops) :
  Lemma((token_update_pto is_psk tk pto).has_sk ==
        token_update_sym_key_flag pto.has_sk is_psk tk) = ()

#push-options "--fuel 1 --ifuel 1"
let rec tokens_update_pto_has_sk_consistent (is_psk : bool) (pattern : list message_token)
                                            (pto : pattern_type_ops) :
  Lemma
  (requires True)
  (ensures (
    (tokens_update_pto is_psk pattern pto).has_sk ==
    tokens_update_sym_key_flag pto.has_sk is_psk pattern))
  (decreases pattern) =
  match pattern with
  | [] -> ()
  | tk :: pattern' ->
    let pto' = token_update_pto is_psk tk pto in
    tokens_update_pto_has_sk_consistent is_psk pattern' pto'
#pop-options

/// Below, we define the general return types used by the send/receive message
/// functions.

/// This return type is only used in [return_type_from_pto] (see the explanations below)
let dh_use_sk_rtype (sender : bool) : Type0 =
  r:prim_error_code{
    if sender then
      r <> CDecrypt_error
    else True
  }

let dh_use_sk_return_type (sender : bool) : return_type =
  { prim_error_code_return_type with
    rty = dh_use_sk_rtype sender; }

/// Conversion from a [pattern_type_ops]. Note that some of the branches won't
/// actually be used (they are not legit operation combinations for a token/pattern),
/// but we define them in a way which is consistent with the rest because it eases/
/// makes possible some proofs later on (in particular the proofs about return type
/// conversions).
[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
let return_type_from_pto (sender : bool) (pto : pattern_type_ops) :
  return_type =
  match pto.hash_op, pto.dh_op, pto.sk_op with
  | false, false, false -> unit_return_type
  | false, false, true -> (* won't happen *)
    if sender then encrypt_return_type else decrypt_return_type
  | false, true, false -> (* won't happen *)
    dh_return_type
  | false, true, true -> (* won't happen *)
    dh_use_sk_return_type sender
  | true, false, false -> hash_return_type
  | true, true, false -> dh_hash_return_type
  | true, false, true -> if sender then encrypt_hash_return_type
                                   else decrypt_hash_return_type true //pto.sk_op
  | true, true, true -> if sender then send_return_type else receive_return_type

/// token message error code

inline_for_extraction noextract
let token_message_return_type (smi : meta_info) (is_psk sender : bool)
                              (tk : message_token) : return_type =
  with_norm(
    let pto = compute_token_pto smi is_psk tk in
    return_type_from_pto sender pto)

inline_for_extraction noextract
let send_token_return_type smi is_psk tk =
  with_norm(token_message_return_type smi is_psk true tk)

inline_for_extraction noextract
let receive_token_return_type smi is_psk tk =
  with_norm(token_message_return_type smi is_psk false tk)

inline_for_extraction noextract
let tokens_message_return_type (smi : meta_info) (is_psk sender : bool)
                               (pattern : list message_token) : return_type =
  with_norm(
    let pto = compute_tokens_pto smi is_psk pattern in
    return_type_from_pto sender pto)

inline_for_extraction noextract
let send_tokens_return_type smi is_psk pattern =
  with_norm(tokens_message_return_type smi is_psk true pattern)

inline_for_extraction noextract
let receive_tokens_return_type smi is_psk pattern =
  with_norm(tokens_message_return_type smi is_psk false pattern)

inline_for_extraction noextract
let message_return_type (smi : meta_info) (is_psk sender : bool)
                        (pattern : list message_token) : return_type =
  with_norm(
    let pto = compute_message_pto smi is_psk pattern in
    return_type_from_pto sender pto)

// Don't put strict_on_arguments here: it causes type inference to loop
// in [Impl.Noise.RecursiveMessages.send_message_tokens_with_payload_m]
inline_for_extraction noextract
let send_message_return_type smi is_psk pattern =
  with_norm(message_return_type smi is_psk true pattern)

// Don't put strict_on_arguments here: it causes type inference to loop in
// [Impl.Noise.PatternMessages.Definitions.to_creceive_message_rtype]
inline_for_extraction noextract
let receive_message_return_type smi is_psk pattern =
  with_norm(message_return_type smi is_psk false pattern)

/// Conversion between the different return types

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
let return_type_from_pto_convert_pto
  (#sender : bool) (pto0 : pattern_type_ops) (pto1 : greater_pto pto0)
  (r : rtype (return_type_from_pto sender pto0)) :
  r':rtype (return_type_from_pto sender pto1) {to_prim_error_code r' = to_prim_error_code r} =
  with_norm(if is_always_success r then success _ else
    (convert_subtype #(rtype (return_type_from_pto sender pto0))
                     #(rtype (return_type_from_pto sender pto1)) r))
#pop-options

#push-options "--fuel 2 --ifuel 1"
inline_for_extraction noextract
let token_message_rtype_to_tokens_
  (#smi : meta_info) (#is_psk #sender : bool) (#tk : message_token)
  (pattern : list message_token)
  (r : rtype (token_message_return_type smi is_psk sender tk)) :
  r':rtype (tokens_message_return_type smi is_psk sender (tk :: pattern)) {
    to_prim_error_code r' = to_prim_error_code r} =
  let pto_tk = compute_token_pto smi is_psk tk in
  let pto_pat = compute_tokens_pto smi is_psk (tk::pattern) in
  assert(pto_tk `pto_less_than` pto_pat);
  return_type_from_pto_convert_pto #sender pto_tk pto_pat r
#pop-options

inline_for_extraction noextract
let token_message_rtype_to_tokens
  (#smi : meta_info) (#is_psk #sender : bool) (#tk : message_token)
  (pattern : list message_token)
  (r : rtype (token_message_return_type smi is_psk sender tk)) :
  r':rtype (tokens_message_return_type smi is_psk sender (tk :: pattern)) {
    to_prim_error_code r' = to_prim_error_code r} =
  with_norm(token_message_rtype_to_tokens_ pattern r)

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
let tokens_message_rtype_to_message_
  (#smi : meta_info) (#is_psk #sender : bool)
  (#pattern : list message_token)
  (r : rtype (tokens_message_return_type smi is_psk sender pattern)) :
  r':rtype (message_return_type smi is_psk sender pattern) {
    to_prim_error_code r' = to_prim_error_code r} =
  let pto_pat = compute_tokens_pto smi is_psk pattern in
  let pto_msg = compute_message_pto smi is_psk pattern in
  assert(pto_pat `pto_less_than` pto_msg);
  return_type_from_pto_convert_pto #sender pto_pat pto_msg r
#pop-options

inline_for_extraction noextract
let tokens_message_rtype_to_message
  (#smi : meta_info) (#is_psk #sender : bool)
  (#pattern : list message_token)
  (r : rtype (tokens_message_return_type smi is_psk sender pattern)) :
  r':rtype (message_return_type smi is_psk sender pattern) {
    to_prim_error_code r' = to_prim_error_code r} =
  with_norm(tokens_message_rtype_to_message_ r)

#push-options "--z3rlimit 25 --fuel 1 --ifuel 1"
inline_for_extraction noextract
let tokens_message_rtype_add_token_
  (#smi : meta_info)
  (#is_psk #sender : bool)
  (#pattern : list message_token)
  (tk : message_token)
  (r : rtype (tokens_message_return_type (token_update_smi is_psk sender tk smi)
                                         is_psk sender pattern)) :
  r':rtype (tokens_message_return_type smi is_psk sender (tk :: pattern)) {
    to_prim_error_code r' = to_prim_error_code r} =
  let smi1 = token_update_smi is_psk sender tk smi in
  (**) let smi' : Ghost.erased _ = token_update_smi is_psk sender tk smi in
  (**) assert(smi'.hsf.sk || not smi1.hsf.sk);
//  (**) with_norm_spec(compute_tokens_pto smi1 is_psk pattern);
  let pto_pat = compute_tokens_pto smi1 is_psk pattern in
  let pto_tk_pat = compute_tokens_pto smi is_psk (tk::pattern) in
  (**) let pto_pat0 : Ghost.erased _ = init_pto smi1.hsf.sk in
  (**) let pto1 : Ghost.erased _ = compute_token_pto smi is_psk tk in
  (**) let pto2 : Ghost.erased _ = tokens_update_pto is_psk pattern pto1 in
  (**) assert(pto_tk_pat = Ghost.reveal pto2);
  (**) assert(pto_pat0 `pto_less_than` pto1);
  (**) tokens_update_pto_monotonous is_psk pattern pto_pat0 pto1;
  (**) assert(pto_pat `pto_less_than` pto_tk_pat);
  return_type_from_pto_convert_pto #sender pto_pat pto_tk_pat r
#pop-options

inline_for_extraction noextract
let tokens_message_rtype_add_token
  (#smi : meta_info)
  (#is_psk #sender : bool)
  (#pattern : list message_token)
  (tk : message_token)
  (r : rtype (tokens_message_return_type (token_update_smi is_psk sender tk smi)
                                         is_psk sender pattern)) :
  r':rtype (tokens_message_return_type smi is_psk sender (tk :: pattern)) {
    to_prim_error_code r' = to_prim_error_code r} =
  with_norm(tokens_message_rtype_add_token_ tk r)

/// Some more specific conversions for the send/receive with payload functions
#push-options "--ifuel 1 --fuel 1"
inline_for_extraction noextract
let encrypt_hash_rtype_to_message_payload_
  (#smi : meta_info) (#is_psk : bool) (#pattern : list message_token)
  (r : rtype encrypt_hash_return_type) :
  r':rtype (message_return_type smi is_psk true pattern) {
    to_prim_error_code r = to_prim_error_code r' } =
  let smi1 = send_tokens_update_smi is_psk pattern smi in
  let return_type1 = encrypt_hash_return_type in
  let return_type2 = tokens_message_return_type smi is_psk true pattern in
  let enc_hash_pto : pattern_type_ops =
    { hash_op = true; dh_op = false; sk_op = smi1.hsf.sk; has_sk = smi1.hsf.sk; } in
  let send_msg_pto = compute_message_pto smi is_psk pattern in
  (**) assert(message_return_type smi is_psk true pattern ==
  (**)         return_type_from_pto true send_msg_pto);
  (**) tokens_update_pto_has_sk_consistent is_psk pattern (init_pto smi.hsf.sk);
  (**) assert(send_msg_pto.sk_op || not smi1.hsf.sk);
  (**) assert(send_msg_pto.has_sk == smi1.hsf.sk);
  (**) assert(enc_hash_pto `pto_less_than` send_msg_pto);
  return_type_from_pto_convert_pto #true enc_hash_pto send_msg_pto
                                   (r <: rtype (return_type_from_pto true enc_hash_pto))
#pop-options

inline_for_extraction noextract
let encrypt_hash_rtype_to_message_payload
  (#smi : meta_info) (#is_psk : bool) (#pattern : list message_token)
  (r : rtype encrypt_hash_return_type) :
  r':rtype (message_return_type smi is_psk true pattern) {
    to_prim_error_code r = to_prim_error_code r' } =
  with_norm(encrypt_hash_rtype_to_message_payload_ r)

#push-options "--ifuel 1 --fuel 1"
inline_for_extraction noextract
let decrypt_hash_rtype_to_message_payload_
  (#smi : meta_info) (#is_psk : bool) (#pattern : list message_token)
  (r : rtype (decrypt_hash_return_type (receive_tokens_update_smi is_psk pattern smi).hsf.sk)) :
  r':rtype (message_return_type smi is_psk false pattern) {
    to_prim_error_code r = to_prim_error_code r' } =
  let smi1 = receive_tokens_update_smi is_psk pattern smi in
  let return_type1 =
    decrypt_hash_return_type (receive_tokens_update_smi is_psk pattern smi).hsf.sk in
  let return_type2 = tokens_message_return_type smi is_psk false pattern in
  let dec_hash_pto : pattern_type_ops =
    { hash_op = true; dh_op = false; sk_op = smi1.hsf.sk; has_sk = smi1.hsf.sk; } in
  let recv_msg_pto = compute_message_pto smi is_psk pattern in
  (**) tokens_update_pto_has_sk_consistent is_psk pattern (init_pto smi.hsf.sk);
  (**) updt_sk_consistent_with_receive_tokens_update_smi is_psk pattern smi;
  (**) assert(recv_msg_pto.sk_op || not smi1.hsf.sk);
  (**) assert(recv_msg_pto.has_sk == smi1.hsf.sk);
  (**) assert(dec_hash_pto `pto_less_than` recv_msg_pto);
  (**) assert(message_return_type smi is_psk false pattern ==
  (**)          return_type_from_pto false recv_msg_pto);
  (**) assert(smi1.hsf.sk ==> decrypt_hash_return_type smi1.hsf.sk ==
  (**)          return_type_from_pto false dec_hash_pto);
  (**) assert(not (smi1.hsf.sk) ==>
  (**)          subtype_of (rtype hash_return_type) (decrypt_hash_rtype false));
  (**) assert(not (smi1.hsf.sk) ==>
  (**)          subtype_of (decrypt_hash_rtype false) (rtype hash_return_type));
  if smi1.hsf.sk then
    return_type_from_pto_convert_pto #false dec_hash_pto recv_msg_pto r
  else
    if never_fails hash_return_type then success _ else r
#pop-options

inline_for_extraction noextract
let decrypt_hash_rtype_to_message_payload
  (#smi : meta_info) (#is_psk : bool) (#pattern : list message_token)
  (r : rtype (decrypt_hash_return_type (receive_tokens_update_smi is_psk pattern smi).hsf.sk)) :
  r':rtype (message_return_type smi is_psk false pattern) {
    to_prim_error_code r = to_prim_error_code r' } =
  with_norm(decrypt_hash_rtype_to_message_payload_ r)

(* TODO: very weird, but we need it in Impl.Noise.MessageCode.fsti *)
inline_for_extraction noextract
let decrypt_hash_rtype_convert_sk (sk1 : bool) (sk2 : bool{sk2 == sk1})
                                  (r : rtype (decrypt_hash_return_type sk1)) :
  r':rtype (decrypt_hash_return_type sk2){to_prim_error_code r' = to_prim_error_code r} =
  r

(*** Send message token(s) *)
(**** send_message_token *)

/// At this point it doesn't cost us much to have a precise hardware precondition
/// for the cryptographic primitives. It may prove useful later.
#push-options "--ifuel 1"
let send_message_token_crypto_prims_pre (nc : iconfig) (smi : meta_info) (tk : message_token) :
  Type0 =
  match tk with
  | S -> (if smi.hsf.sk then get_aead_pre nc else True) /\ get_hash_pre nc
  | E -> get_hash_pre nc
  | SS | EE | SE | ES | PSK -> get_dh_pre nc /\ get_hash_pre nc
#pop-options

#push-options "--ifuel 1"
[@(strict_on_arguments [3])]
let rec send_message_tokens_crypto_prims_pre (nc : iconfig) (smi : meta_info)
                                             (is_psk : bool)
                                             (pattern : list message_token) :
  Tot (t:Type0{get_pres nc ==> t})
  (decreases pattern) =
  match pattern with
  | [] -> True
  | tk :: pattern' ->
    send_message_token_crypto_prims_pre nc smi tk /\
    begin
    let smi' = send_token_update_smi is_psk tk smi in
    send_message_tokens_crypto_prims_pre nc smi' is_psk pattern'
    end
#pop-options

let send_message_crypto_prims_pre (nc : iconfig) (smi : meta_info)
                                  (is_psk : bool)
                                  (pattern : list message_token) :
  Tot (t:Type0{get_pres nc ==> t}) =
  send_message_tokens_crypto_prims_pre nc smi is_psk pattern /\
  get_hash_pre nc /\
  begin
  let smi' = send_tokens_update_smi is_psk pattern smi in
  if smi'.hsf.sk then get_aead_pre nc else True
  end

let send_message_token_pre
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (tk : message_token) (st : valid_hsm nc smi)
    (out : token_message_t nc smi tk)
    (h : mem) : Type0 =
  hsm_inv h st smi /\ live h out /\ hsm_disjoint st out /\
  check_send_token_smi smi initiator tk /\
  send_message_token_crypto_prims_pre nc smi tk

let send_message_token_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (tk : message_token) (st : valid_send_token_hsm nc is_psk tk smi)
    (out : token_message_t nc smi tk)
    (h0 : mem) (r : rtype (send_token_return_type smi is_psk tk)) (h1 : mem) :
    Type0 =
  let st0_v = eval_handshake_state_m h0 st smi in
  let smi' = send_token_update_smi is_psk tk smi in
  let st1_v = eval_handshake_state_m h1 st (**) smi' (**) in
  let r_v = Spec.send_message_token initiator is_psk tk st0_v in
  ssm_modifies1 (hsm_get_sym_state st) out h0 h1 /\
  begin match to_prim_error_code r, r_v with
  | CDH_error, Fail DH -> True
  | CSuccess, Res (out_v, st1'_v) ->
    st1'_v == st1_v /\ length out == S.length out_v /\
    h1.[|out|] `S.equal` out_v
  | _ -> False
  end

type send_message_token_st (nc : iconfig) =
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  tk : message_token ->
  st : valid_send_token_hsm nc is_psk tk smi ->
  out : token_message_t nc smi tk ->
  Stack (rtype (send_token_return_type smi is_psk tk))
  (requires (send_message_token_pre smi initiator is_psk tk st out))
  (ensures (send_message_token_post smi initiator is_psk tk st out))

inline_for_extraction noextract
val send_message_token_m (#nc : iconfig) (ssdhi : ssdh_impls nc) :
  send_message_token_st nc


(**** send_message_tokens *)

let send_message_tokens_pre
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (st : valid_hsm nc smi) (outlen : size_t) (out : lbuffer uint8 outlen)
    (h : mem) : Type0 =
  hsm_inv h st smi /\ live h out /\ hsm_disjoint st out /\
  size_v outlen == tokens_message_vsv nc smi is_psk pattern /\
  check_send_message_smi smi initiator is_psk pattern /\
  send_message_tokens_crypto_prims_pre nc smi is_psk pattern

let send_message_tokens_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (st : valid_send_message_hsm nc is_psk pattern smi)
    (outlen : size_t) (out : lbuffer uint8 outlen)
    (h0 : mem) (r : rtype (send_tokens_return_type smi is_psk pattern))
    (h1 : mem) : Type0 =
  ssm_modifies1 (hsm_get_sym_state st) out h0 h1 /\ hsm_disjoint st out /\
  begin
  let smi' = send_tokens_update_smi is_psk pattern smi in
  let st0_v = eval_handshake_state_m h0 st smi in
  let st1_v = eval_handshake_state_m h1 st (**) smi' (**) in
  begin match to_prim_error_code r,
              Spec.send_message_tokens initiator is_psk pattern st0_v with
  | CDH_error, Fail DH -> True
  | CSuccess, Res (out_v, st1'_v) ->
    st1_v == st1'_v /\ length out == S.length out_v /\ h1.[|out|] `S.equal` out_v
  | _ -> False
  end end

type send_message_tokens_st (nc : iconfig) =
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  pattern : list message_token ->
  st : valid_send_message_hsm nc is_psk pattern smi ->
  outlen : size_t -> (* this parameter is actually meta *)
  out : lbuffer uint8 outlen ->
  Stack (rtype (send_tokens_return_type smi is_psk pattern))
  (requires (send_message_tokens_pre smi initiator is_psk pattern st outlen out))
  (ensures (send_message_tokens_post smi initiator is_psk pattern st outlen out))

(* A helper lemma which proves the post-condition of [send_message_tokens], assuming
 * the pre and post-conditions of the functions called by [send_message_tokens] in the
 * recursive case *)
(* The fuel is necessary for the proof of [hs_nn_pred] *)
#push-options "--fuel 1 --ifuel 1"
val send_message_tokens_pre_post_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (tk : message_token)
  (pattern : list message_token)
  (st : valid_send_message_hsm nc is_psk (tk::pattern) smi)
  (tk_outlen : size_t{tk_outlen == token_message_vs nc smi tk})
  (tk_out : lbuffer uint8 tk_outlen)
  (outlen' : size_t)
  (out' : lbuffer uint8 outlen')
  (outlen : size_t{size_v outlen == size_v tk_outlen + size_v outlen'})
  (out : lbuffer uint8 outlen)
  (h0 h1 h2 : mem)
  (r2 : rtype (send_tokens_return_type (send_token_update_smi is_psk tk smi)
                                       is_psk pattern)) :
  Lemma
  (requires (
    let smi' = send_token_update_smi is_psk tk smi in
    begin
    tk_out == Ghost.reveal (gsub out 0ul tk_outlen) /\
    out' == Ghost.reveal (gsub out tk_outlen outlen') /\
    send_message_tokens_pre smi initiator is_psk (tk :: pattern) st outlen out h0 /\ (**)
    send_message_token_pre smi initiator is_psk tk st tk_out h0 /\ (**)
    send_message_token_post smi initiator is_psk tk st tk_out h0 (success _) h1 /\
    send_message_tokens_pre smi' initiator is_psk pattern st outlen' out' h1 /\
    send_message_tokens_post smi' initiator is_psk pattern st outlen' out' h1 r2 h2
    end
  ))
  (ensures (
    let r3 = tokens_message_rtype_add_token #smi #is_psk #true #pattern tk r2 in
    send_message_tokens_post smi initiator is_psk (tk :: pattern) st outlen out h0 r3 h2))
#pop-options

(**** send_message_tokens_with_payload *)

let send_message_tokens_with_payload_pre
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
    (st : valid_hsm nc smi)
    (outlen : size_t) (out : lbuffer uint8 outlen)
    (h : mem) : Type0 =
  hsm_inv h st smi /\ live h out /\ live h payload /\
  hsm_disjoint st out /\ hsm_disjoint st payload /\ disjoint payload out /\
  size_v outlen == message_vsv nc smi is_psk pattern (size_v payload_len) /\
  check_send_message_smi smi initiator is_psk pattern /\
  send_message_crypto_prims_pre nc smi is_psk pattern

let send_message_tokens_with_payload_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
    (st : valid_send_message_hsm nc is_psk pattern smi)
    (outlen : size_t) (out : lbuffer uint8 outlen) 
    (h0 : mem) (r : rtype (send_message_return_type smi is_psk pattern)) (h1 : mem) : Type0 =
  ssm_modifies1 (hsm_get_sym_state st) out h0 h1 /\
  begin
  let smi' = send_message_update_smi is_psk pattern smi in
  let st0_v = eval_handshake_state_m h0 st smi in
  let st1_v = eval_handshake_state_m h1 st (**) smi' (**) in
  let payload_v = h0.[|payload|] in
  begin match to_prim_error_code r,
              Spec.send_message_tokens_with_payload initiator is_psk pattern
                                                    payload_v st0_v with
  | CDH_error, Fail DH -> True
  | CSuccess, Res (out_v, st1'_v) ->
    st1_v == st1'_v /\ length out == S.length out_v /\ h1.[|out|] `S.equal` out_v
  | _ -> False
  end end

type send_message_tokens_with_payload_st (nc : iconfig) =
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  pattern : list message_token ->
  payload_len : plain_message_len_t nc ->
  payload : plain_message_t nc payload_len ->
  st : valid_send_message_hsm nc is_psk pattern smi ->
  outlen : size_t ->
  out : lbuffer uint8 outlen ->
  Stack (rtype (send_message_return_type smi is_psk pattern))
  (requires (send_message_tokens_with_payload_pre smi initiator is_psk pattern
                                            payload_len payload st outlen out))
  (ensures (send_message_tokens_with_payload_post smi initiator is_psk
                                      pattern payload_len payload st outlen out))

(*** Receive message token(s) *)
(**** receive_message_token *)

/// Same remarks as for [send_message_token_crypto_prims_pre]
#push-options "--ifuel 1"
let receive_message_token_crypto_prims_pre (nc : iconfig) (smi : meta_info)
                                           (tk : message_token) :
  Type0 =
  match tk with
  | S -> (if smi.hsf.sk then get_aead_pre nc else True) /\ get_hash_pre nc
  | E -> get_hash_pre nc
  | SS | EE | SE | ES | PSK -> get_dh_pre nc /\ get_hash_pre nc
#pop-options

#push-options "--ifuel 1"
[@(strict_on_arguments [3])]
let rec receive_message_tokens_crypto_prims_pre (nc : iconfig) (smi : meta_info)
                                                (is_psk : bool)
                                                (pattern : list message_token) :
  Tot (t:Type0{get_pres nc ==> t})
  (decreases pattern) =
  match pattern with
  | [] -> True
  | tk :: pattern' ->
    receive_message_token_crypto_prims_pre nc smi tk /\
    begin
    let smi' = receive_token_update_smi is_psk tk smi in
    receive_message_tokens_crypto_prims_pre nc smi' is_psk pattern'
    end
#pop-options

let receive_message_crypto_prims_pre (nc : iconfig) (smi : meta_info)
                                     (is_psk : bool)
                                     (pattern : list message_token) :
  Tot (t:Type0{get_pres nc ==> t}) =
  receive_message_tokens_crypto_prims_pre nc smi is_psk pattern /\
  get_hash_pre nc /\
  begin
  let smi' = receive_tokens_update_smi is_psk pattern smi in
  if smi'.hsf.sk then get_aead_pre nc else True
  end

let receive_message_token_pre
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (tk : message_token) (st : valid_receive_token_hsm nc is_psk tk smi)
    (input : token_message_t nc smi tk)
    (h : mem) : Type0 =
  hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
  check_receive_token_smi smi initiator tk /\
  receive_message_token_crypto_prims_pre nc smi tk

(* Actually, we shouldn't need to make a match on the token now, because it
 * should be possible to retrieve this information from the return type, which
 * is quite detailed. *)
let receive_message_token_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (tk : message_token)
    (st : valid_receive_token_hsm nc is_psk tk smi)
    (input : token_message_t nc smi tk)
    (h0 : mem) (r : rtype (receive_token_return_type smi is_psk tk)) (h1 : mem) :
    Type0 =
  let st0_v = eval_handshake_state_m h0 st smi in
  let smi' = receive_token_update_smi is_psk tk smi in
  let st1_v = eval_handshake_state_m h1 st (**) smi' (**) in
  let input_v = h0.[|input|] in
  let r_v = receive_message_token_nout initiator is_psk tk input_v st0_v in
  hsm_modifies0_only_remote st h0 h1 /\
  begin match tk with
   | S ->
     begin match to_prim_error_code r, r_v with
     | CSuccess, Res st1'_v -> st1_v == st1'_v
     | CDecrypt_error, Fail Decryption -> smi.hsf.sk == true
     | _ -> False
     end
   | E | PSK ->
     begin match to_prim_error_code r, r_v with
     | CSuccess, Res st1'_v -> st1_v == st1'_v
     | _ -> False
     end
   | SS | EE | SE | ES ->
     begin match to_prim_error_code r, r_v with
     | CSuccess, Res st1'_v -> st1_v == st1'_v
     | CDH_error, Fail DH -> True
     | _ -> False
     end
  end

type receive_message_token_st (nc : iconfig) =
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  tk : message_token ->
  st : valid_receive_token_hsm nc is_psk tk smi ->
  input : token_message_t nc smi tk ->
  Stack (rtype (receive_token_return_type smi is_psk tk))
  (requires (receive_message_token_pre smi initiator is_psk tk st input))
  (ensures (receive_message_token_post smi initiator is_psk tk st input))

inline_for_extraction noextract
val receive_message_token_m (#nc : iconfig) (ssdhi : ssdh_impls nc) :
  receive_message_token_st nc


(**** receive_message_tokens_nout *)
(* We prove a refinement of [receive_message_token], where we modify the pre
 * and post conditions, so that it is easier to implement [receive_message_tokens]
 * *)
let receive_message_token_pre_ 
    (#nc : iconfig) (pattern : Ghost.erased (list message_token))
    (smi : meta_info) (initiator is_psk : bool)
    (tk : message_token)
    (st : valid_hsm nc smi)
    (input : token_message_t nc smi tk)
    (h : mem) : Type0 =
  hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
  check_receive_message_smi smi initiator is_psk (tk :: pattern) /\
  receive_message_tokens_crypto_prims_pre nc smi is_psk (tk :: pattern)

(* TODO: not sure this is necessary anymore *)
#push-options "--fuel 1 --ifuel 1"
let receive_message_token_post_
    (#nc : iconfig) (pattern : list message_token)
    (smi : meta_info) (initiator is_psk : bool)
    (tk : message_token)
    (st : valid_receive_message_hsm nc is_psk (tk::pattern) smi)
    (input : token_message_t nc smi tk)
    (h0 : mem) (r : rtype (receive_token_return_type smi is_psk tk))
    (h1 : mem) : Type0 =
  let st0_v = eval_handshake_state_m h0 st smi in
  let smi' = receive_token_update_smi is_psk tk smi in
  let st1_v = eval_handshake_state_m h1 st (**) smi' (**) in
  let input_v = h0.[|input|] in
  let r_v = receive_message_token_nout initiator is_psk tk input_v st0_v in
  hsm_modifies0_only_remote st h0 h1 /\ check_receive_message_smi smi' initiator is_psk pattern /\
  begin match to_prim_error_code r, r_v with
  | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
  | CSuccess, Res st1'_v -> st1'_v == st1_v
  | _ -> False
  end
#pop-options

inline_for_extraction noextract
val receive_message_token_m_ (#nc : iconfig) (impl : receive_message_token_st nc) :
  pattern : list message_token ->
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  tk : message_token ->
  st : valid_receive_message_hsm nc is_psk (tk::pattern) smi ->
  input : token_message_t nc smi tk ->
  Stack (rtype (receive_token_return_type smi is_psk tk))
  (requires (receive_message_token_pre_ pattern smi initiator is_psk tk st input))
  (ensures (receive_message_token_post_ pattern smi initiator is_psk tk st input))

let receive_message_tokens_nout_pre
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (st : valid_hsm nc smi)
    (inlen : size_t) (input : lbuffer uint8 inlen)
    (h : mem) : Type0 =
  hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
  size_v inlen == tokens_message_vsv nc smi is_psk pattern /\
  check_receive_message_smi smi initiator is_psk pattern /\
  receive_message_tokens_crypto_prims_pre nc smi is_psk pattern

let receive_message_tokens_nout_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (st : valid_receive_message_hsm nc is_psk pattern smi)
    (inlen : size_t)
    (input : lbuffer uint8 inlen)
    (h0 : mem) (r : rtype (receive_tokens_return_type smi is_psk pattern))
    (h1 : mem) : Type0 =
  // This first assertion should be provided by the precondition, but we need
  // it here to typecheck the current definition
  size_v inlen == tokens_message_vsv nc smi is_psk pattern /\
  hsm_modifies0_only_remote st h0 h1 /\ hsm_disjoint st input /\
  begin
  let smi' = receive_tokens_update_smi is_psk pattern smi in
  let st0_v = eval_handshake_state_m h0 st smi in
  let st1_v = eval_handshake_state_m h1 st smi' in
  let input_v = h0.[|input|] in
  let r_v = receive_message_tokens_nout initiator is_psk pattern input_v st0_v in
  begin match to_prim_error_code r, r_v with
  | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
  | CSuccess, Res st1'_v -> st1_v == st1'_v
  | _ -> False
  end
  end

type receive_message_tokens_nout_st (nc : iconfig) =
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  pattern : list message_token ->
  st : valid_receive_message_hsm nc is_psk pattern smi ->
  inlen : size_t ->
  input : lbuffer uint8 inlen ->
  Stack (rtype (receive_tokens_return_type smi is_psk pattern))
  (requires (receive_message_tokens_nout_pre smi initiator is_psk pattern
                                             st inlen input))
  (ensures (fun h0 r h1 -> receive_message_tokens_nout_post smi initiator is_psk pattern
                                             st inlen input h0 r h1))

(* TODO: Consistency of parameters order between token_update_sym_key_flag and
   rcu_updt_hs_flags *)

(* A helper lemma which proves the post-condition of [receive_message_tokens], assuming
 * the pre and post-conditions of the functions called by [receive_message_tokens] in the
 * recursive case *)
// fuel is necessary for valid_hsm
#push-options "--fuel 1 --ifuel 1"
val receive_message_tokens_nout_pre_post_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (tk : message_token) (pattern : list message_token)
  (st : valid_receive_message_hsm nc is_psk (tk::pattern) smi)
  (tk_inlen : size_t{tk_inlen == token_message_vs nc smi tk})
  (tk_input : lbuffer uint8 tk_inlen)
  (inlen' : size_t)
  (input' : lbuffer uint8 inlen')
  (inlen : size_t{size_v inlen == size_v tk_inlen + size_v inlen'})
  (input : lbuffer uint8 inlen)
  (h0 h1 h2 : mem)
  (r2 : rtype (receive_tokens_return_type (receive_token_update_smi is_psk tk smi)
                                          is_psk pattern)) :
  Lemma
  (requires (
    let smi1 = receive_token_update_smi is_psk tk smi in
    begin
    tk_input == Ghost.reveal (gsub input 0ul tk_inlen) /\
    input' == Ghost.reveal (gsub input tk_inlen inlen') /\
    receive_message_tokens_nout_pre smi initiator is_psk (tk :: pattern) st inlen input h0 /\
    receive_message_token_pre_ pattern smi initiator is_psk tk st tk_input h0 /\
    receive_message_token_post_ pattern smi initiator is_psk tk st tk_input h0 (success _) h1 /\
    receive_message_tokens_nout_pre smi1 initiator is_psk pattern st inlen' input' h1 /\
    receive_message_tokens_nout_post smi1 initiator is_psk pattern st inlen' input' h1 r2 h2
    end))
  (ensures (
    let r3 = tokens_message_rtype_add_token #smi #is_psk #false #pattern tk r2 in
    receive_message_tokens_nout_post smi initiator is_psk (tk :: pattern) st inlen input h0 r3 h2))
#pop-options

(**** receive_message_tokens_nout_with_payload *)

let receive_message_tokens_nout_with_payload_pre
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (payload_outlen : plain_message_len_t nc)
    (payload_out : plain_message_t nc payload_outlen)
    (st : valid_receive_message_hsm nc is_psk pattern smi)
    (msg_inlen : size_t) (msg_input : lbuffer uint8 msg_inlen)
    (payload_inlen : size_t) (payload_input : lbuffer uint8 payload_inlen)
    (h : mem) : Type0 =
  hsm_inv h st smi /\ live h payload_out /\ live h msg_input /\ live h payload_input /\
  hsm_disjoint st payload_out /\ hsm_disjoint st msg_input /\ hsm_disjoint st payload_input /\
  disjoint payload_out msg_input /\ disjoint payload_out payload_input /\
  size_v msg_inlen == tokens_message_vsv nc smi is_psk pattern /\
  size_v payload_inlen ==
    opt_encrypt_size (tokens_update_sym_key_flag smi.hsf.sk is_psk pattern)
                     (size_v payload_outlen) /\
  size_v msg_inlen + size_v payload_inlen <= max_size_t /\
  check_receive_message_smi smi initiator is_psk pattern /\
  receive_message_crypto_prims_pre nc smi is_psk pattern


let receive_message_tokens_nout_with_payload_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (payload_outlen : plain_message_len_t nc)
    (payload_out : plain_message_t nc payload_outlen)
    (st : valid_receive_message_hsm nc is_psk pattern smi)
    (msg_inlen : size_t{size_v msg_inlen == tokens_message_vsv nc smi is_psk pattern})
    (msg_input : lbuffer uint8 msg_inlen)
    (payload_inlen : size_t{
      size_v payload_inlen ==
        opt_encrypt_size (tokens_update_sym_key_flag smi.hsf.sk is_psk pattern)
                         (size_v payload_outlen) /\
      size_v msg_inlen + size_v payload_inlen <= max_size_t /\
      size_v payload_inlen + aead_tag_size <= max_size_t})
    (payload_input : lbuffer uint8 payload_inlen)
    (h0 : mem) (r : rtype (receive_message_return_type smi is_psk pattern))
    (h1 : mem) : Type0 =
  hsm_modifies1_only_remote st payload_out h0 h1 /\
  begin
  let smi' = receive_message_update_smi is_psk pattern smi in
  let st0_v = eval_handshake_state_m h0 st smi in
  let st1_v = eval_handshake_state_m h1 st smi' in
  let msg_input_v = h0.[|msg_input|] in
  let payload_input_v : lseq uint8 (size_v payload_inlen) = h0.[|payload_input|] in
  let payload_out_v = h1.[|payload_out|] in
  begin match to_prim_error_code r, 
              Spec.receive_message_tokens_nout_with_payload initiator is_psk pattern
                           #(size_v msg_inlen) msg_input_v
                           #(size_v payload_inlen) payload_input_v st0_v with
  | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
  | CSuccess, Res (payload_out_v', st1'_v) ->
    st1_v == st1'_v /\ S.length payload_out_v' == S.length payload_out_v /\
    payload_out_v' `S.equal` payload_out_v
  | _ -> False
  end end

type receive_message_tokens_nout_with_payload_st (nc : iconfig) =
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  pattern : list message_token ->
  payload_outlen : plain_message_len_t nc ->
  payload_out : plain_message_t nc payload_outlen ->
  st : valid_receive_message_hsm nc is_psk pattern smi ->
  msg_inlen : size_t ->
  msg_input : lbuffer uint8 msg_inlen ->
  payload_inlen : size_t ->
  payload_input : lbuffer uint8 payload_inlen ->
  Stack (rtype (receive_message_return_type smi is_psk pattern))
  (requires (fun h ->
    receive_message_tokens_nout_with_payload_pre smi initiator is_psk pattern
                   payload_outlen payload_out st msg_inlen msg_input
                   payload_inlen payload_input h))
  (ensures (fun h0 r h1 ->
    receive_message_tokens_nout_with_payload_post smi initiator is_psk pattern
                   payload_outlen payload_out st msg_inlen msg_input
                   payload_inlen payload_input h0 r h1))

(**** receive_message_tokens_with_payload *)

let receive_message_tokens_with_payload_pre
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (payload_outlen : plain_message_len_t nc)
    (payload_out : plain_message_t nc payload_outlen)
    (st : valid_receive_message_hsm nc is_psk pattern smi)
    (inlen : size_t) (input : lbuffer uint8 inlen)
    (h : mem) : Type0 =
  hsm_inv h st smi /\ live h payload_out /\ live h input /\
  hsm_disjoint st payload_out /\ hsm_disjoint st input /\ disjoint payload_out input /\
  size_v inlen == message_vsv nc smi is_psk pattern (size_v payload_outlen) /\
  check_receive_message_smi smi initiator is_psk pattern /\
  receive_message_crypto_prims_pre nc smi is_psk pattern

let receive_message_tokens_with_payload_post
    (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
    (pattern : list message_token)
    (payload_outlen : plain_message_len_t nc)
    (payload_out : plain_message_t nc payload_outlen)
    (st : valid_receive_message_hsm nc is_psk pattern smi)
    (inlen : size_t) (input : lbuffer uint8 inlen)
    (h0 : mem) (r : rtype (receive_message_return_type smi is_psk pattern))
    (h1 : mem) : Type0 =
  hsm_modifies1_only_remote st payload_out h0 h1 /\
  begin
  let smi' = receive_message_update_smi is_psk pattern smi in
  let st0_v = eval_handshake_state_m h0 st smi in
  let st1_v = eval_handshake_state_m h1 st smi' in
  let input_v = h0.[|input|] in
  let payload_out_v = h1.[|payload_out|] in
  match to_prim_error_code r, 
        Spec.receive_message_tokens_with_payload initiator is_psk pattern
                           input_v st0_v with
  | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
  | CSuccess, Res (payload_out_v', st1'_v) ->
    st1_v == st1'_v /\ S.length payload_out_v' == S.length payload_out_v /\
    payload_out_v' `S.equal` payload_out_v
  | _ -> False
  end

type receive_message_tokens_with_payload_st (nc : iconfig) =
  smi : meta_info ->
  initiator : bool ->
  is_psk : bool ->
  pattern : list message_token ->
  payload_outlen : plain_message_len_t nc ->
  payload_out : plain_message_t nc payload_outlen ->
  st : valid_receive_message_hsm nc is_psk pattern smi ->
  inlen : size_t ->
  input : lbuffer uint8 inlen ->
  Stack (rtype (receive_message_return_type smi is_psk pattern))
  (requires (fun h ->
    receive_message_tokens_with_payload_pre smi initiator is_psk pattern
                   payload_outlen payload_out st inlen input h))
  (ensures (fun h0 r h1 ->
    receive_message_tokens_with_payload_post smi initiator is_psk pattern
                   payload_outlen payload_out st inlen input h0 r h1))
