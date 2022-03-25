module Spec.Noise.WellFormedness
/// This file defines two notions of well-formedness:
/// - one of them is the well-formedness defined by Trevor Perrin in the Noise
///   technical paper (section 7.3)
/// - the other one is an internal requirement for a pattern to be implementable:
///   it just checks that the pattern can be executed, or rather than it doesn't
///   provably always fail (because some keys are exchanged twice for example).

open FStar.Mul

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.HandshakeFlags
open Spec.Noise.Lengths
open Spec.Noise.NonceCounter
open Spec.Noise.MetaInfo

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

(*** Premessages *)
noextract
let has_pretoken (smi : meta_info) (tk : premessage_token) : Tot bool =
  match tk with
  | PS -> smi.hsf.s
  | PE -> smi.hsf.e

[@(strict_on_arguments [1])]
let has_pretokens (smi : meta_info) (pattern : list premessage_token) :
  Tot bool =
  List.Tot.for_all (has_pretoken smi) pattern

noextract
let no_remote_pretoken (smi : meta_info) (tk : premessage_token) :
  Tot bool =
  match tk with
  | PS -> smi.hsf.rs = false
  | PE -> smi.hsf.re = false

[@(strict_on_arguments [1])]
let rec no_remote_pretokens (smi : meta_info)
                            (pattern : list premessage_token) :
  Tot bool
  (decreases pattern) =
  match pattern with
  | [] -> true
  | tk :: pattern' ->
    if no_remote_pretoken smi tk then
      let smi' = receive_pretoken_update_smi tk smi in
      no_remote_pretokens smi' pattern'
    else false

(*** Send/receive conditions *)
(**** Predicates *)
(** We begin by checking that a pattern is executable (which actually gives
    us rule 1 and 2, together with non-saturation of nonces) *)
let check_token_nonce (smi : meta_info) (token : message_token) : Tot bool =
  if token = S then smi.nonce < saturated_nonce_value else true

let check_send_token_hsf (hsf : handshake_state_flags) (initiator : bool)
                         (tk : message_token) : Tot bool =
  match tk with
  | S -> hsf.s
  | E -> hsf.e
  | SS -> hsf.s && hsf.rs
  | EE -> hsf.e && hsf.re
  | SE -> if initiator then hsf.s && hsf.re
                       else hsf.e && hsf.rs
  | ES -> if initiator then hsf.e && hsf.rs
                       else hsf.s && hsf.re
  | PSK -> hsf.psk

let check_send_token_smi (smi : meta_info) (initiator : bool)
                         (tk : message_token) : Tot bool =
  check_send_token_hsf smi.hsf initiator tk &&
  check_token_nonce smi tk

[@(strict_on_arguments [3])]
let rec check_send_message_smi (smi : meta_info)
                               (initiator is_psk : bool)
                               (message : list message_token) :
  Tot bool (decreases message) =
  match message with
  | [] ->
    (* For the payload encryption *)
    smi.nonce < saturated_nonce_value
  | tk :: message' ->
    if check_send_token_smi smi initiator tk then
      let smi' = send_token_update_smi is_psk tk smi in
      check_send_message_smi smi' initiator is_psk message'
    else false

let check_receive_token_hsf (hsf : handshake_state_flags) (initiator : bool)
                            (tk : message_token) : bool =
  match tk with
  | S -> not hsf.rs
  | E -> not hsf.re
  | SS -> hsf.s && hsf.rs
  | EE -> hsf.e && hsf.re
  | SE -> if initiator then hsf.s && hsf.re
                       else hsf.e && hsf.rs
  | ES -> if initiator then hsf.e && hsf.rs
                       else hsf.s && hsf.re
  | PSK -> hsf.psk

let check_receive_token_smi (smi : meta_info) (initiator : bool)
                            (tk : message_token) : Tot bool =
  check_receive_token_hsf smi.hsf initiator tk &&
  check_token_nonce smi tk

[@(strict_on_arguments [3])]
let rec check_receive_message_smi (smi : meta_info)
                                  (initiator is_psk : bool)
                                  (message : list message_token) :
  Tot bool (decreases message) =
  match message with
  | [] ->
    (* For the payload decryption *)
    smi.nonce < saturated_nonce_value
  | tk :: message' ->
    if check_receive_token_smi smi initiator tk then
      let smi' = receive_token_update_smi is_psk tk smi in
      check_receive_message_smi smi' initiator is_psk message'
    else false

/// This is a syntactic requirement given by Perrin. Note that it implies
/// that the premessages are executable (a premessage where we send the
/// remote static twice is not executable).
[@(strict_on_arguments [0])]
let check_premessage_well_formed (pat : list premessage_token) :
  Tot bool =
  match pat with
  | [PE; PS] | [PS] | [PE] -> true
  | _ -> false

(* TODO: actually we shouldn't need to re-check the premessages. Use typing? *)
(* Checks that the premessages of a handshake are well-formed, returns a triple:
 * (initiator_flags, receiver_flags) *)
[@(strict_on_arguments [0])]
let check_premessages_well_formed (hsk : handshake_pattern) : bool =
  let irb =
    match hsk.premessage_ir with
    | Some pre -> check_premessage_well_formed pre | None -> true
    in
  let rib =
    match hsk.premessage_ri with
    | Some pre -> check_premessage_well_formed pre | None -> true
    in
  irb && rib

let check_message_executable (is_psk ir : bool) 
                             (ssmi0 rsmi0 ssmi1 rsmi1 : meta_info)
                             (msg : list message_token) : bool =
  let b1 = check_send_message_smi ssmi0 ir is_psk msg in
  let b2 = check_receive_message_smi rsmi0 (not ir) is_psk msg in
  b1 && b2

let check_pattern_name (name : string) : bool =
  // Check that the pattern name is made of ASCII characters and is not too long.
  // Note that the following condition is enough to enforce that the protocol
  // name is hashable
  String.length name + 31 (* concatenated characters *) + 64 (* max hash size *)
    <= Lib.IntTypes.max_size_t &&
  LowStar.Literal.is_ascii_string name

/// This function checks that a pattern is executable (it checks rules 1 and 2
/// listed by Perrin, together with the non-saturation of the nonce).
[@(strict_on_arguments [0])]
let check_handshake_pattern_executable (hsk : handshake_pattern) : bool =
  if not (check_premessages_well_formed hsk) then false else
  let set_psk = true in
  forallb_handshake_pattern_messages hsk set_psk check_message_executable &&
  Cons? hsk.messages &&
  List.length hsk.messages <= Lib.IntTypes.max_size_t &&
  check_pattern_name hsk.name

(** We then check rules 3 and 4 about the presence and order of DHs *)
/// First, a small helper which checks if we can encrypt (rule 4: we must not
/// encrypt unless we have mixed in our ephemeral key, to prevent catastrophic
/// key reuse).
let check_hskf_encryption (initiator : bool) (hskf : handshake_pattern_flags) : bool =
  // DHs
  let b1 =
    if initiator then
      (not hskf.hsk_se || hskf.hsk_ee) &&
      (not hskf.hsk_ss || hskf.hsk_es)
    else
      (not hskf.hsk_es || hskf.hsk_ee) &&
      (not hskf.hsk_ss || hskf.hsk_se)
  in
  // PSK case
  let b2 = not hskf.hsk_psk || hskf.hsk_re || hskf.hsk_ie in
  b1 && b2

let rec check_handshake_pattern_DHs_message
  (ir : bool) (tokens : list message_token) (hskf : handshake_pattern_flags) : bool =
  match tokens with
  | [] -> true
  | tk :: tokens' ->
    let hskf1 = compute_hsk_token_flags ir hskf tk in
    // Check the current token
    let b0 =
      match tk with
      | E -> true // no encryption
      | S ->
        // We must not encrypt unless we have mixed our local ephemeral in
        check_hskf_encryption ir hskf
      | _ -> true // Just update the hskf
    in
    b0 && check_handshake_pattern_DHs_message ir tokens' hskf1

let rec check_handshake_pattern_DHs_at_step
  (hsk : handshake_pattern) (i : nat{i <= List.Tot.length hsk.messages}) :
  bool =
  if i = 0 then true
  else if not (check_handshake_pattern_DHs_at_step hsk (i-1)) then false
  else
    let ir = ((i-1)%2=0) in
    let tokens = List.Tot.index hsk.messages (i-1) in
    let hskf0 = compute_hsk_flags_at_step hsk (i-1) in
    let hskf1 = compute_hsk_msg_flags ir hskf0 tokens in
    // Recursive call
    check_handshake_pattern_DHs_at_step hsk (i-1) &&
    // Check the current message
    check_handshake_pattern_DHs_message ir tokens hskf0 &&
    // Check the potential encryption at the end of the current message
    check_hskf_encryption ir hskf1

let check_handshake_pattern_DHs (hsk : handshake_pattern) : bool =
  let n = List.Tot.length hsk.messages in
  check_handshake_pattern_DHs_at_step hsk n

/// The final well-formedness function
let check_handshake_pattern_well_formed (hsk : handshake_pattern) : bool =
  check_handshake_pattern_executable hsk &&
  check_handshake_pattern_DHs hsk
  
(** Well-formed handshake pattern *)
type wf_handshake_pattern = hsk:handshake_pattern{check_handshake_pattern_well_formed hsk}

(** Compile a list of messages to a well-formed handshake pattern *)
(* The [normalize_term] in the precondition is necessary in order for F*
 * to be able to compute to enforce typing.
 *)
let wf_hs (name : string) (ls : list message) :
  Pure (wf_handshake_pattern)
  (requires (normalize_term (
    Some? (hs_safe name ls) == true /\
    check_handshake_pattern_well_formed (Some?.v (hs_safe name ls)))))
  (ensures (fun _ -> True))
  =
  assert_norm(check_handshake_pattern_well_formed (Some?.v (hs_safe name ls)));
  normalize_term (Some?.v (hs_safe name ls))

(**** Well-formedness tests *)
(***** Well-formed *)
private let hskp1 = hs "" [~<<~ [PS]; ~>~ [E; ES; S; SS]; ~<~ [E; EE; SE; PSK]; ~>~ []; ~<~ []]
private let hskp2 = hs "" [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE]; ~>~ []; ~<~ []]
private let hskp3 = hs "" [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE; S; ES]; ~>~ []; ~<~ []]
private let hskp4 = hs "" [~<<~ [PS]; ~>~ [E; ES]; ~<~ [E; EE]; ~>~ []]

private let wf1 = check_handshake_pattern_well_formed hskp1
private let wf2 = check_handshake_pattern_well_formed hskp2
private let wf3 = check_handshake_pattern_well_formed hskp3
private let wf4 = check_handshake_pattern_well_formed hskp4
private let test_wf = wf1 && wf2 && wf3 && wf4

(***** Not well formed *)
private let hskp1_1 = hs "" [~>~ [E; ES; S; SS]; ~<~ [E; EE; SE; PSK]; ~>~ []; ~<~ []]
private let hskp1_2 = hs "" [~<<~ [PS]; ~>~ [E; ES; SS]; ~<~ [E; EE; SE; PSK]; ~>~ []; ~<~ []]
private let hskp1_3 = hs "" [~<<~ [PS]; ~>~ [E; ES; S; SS]; ~<~ [EE; SE; PSK]; ~>~ []; ~<~ []]
private let hskp1_4 = hs "" [~<<~ [PS]; ~>~ [ES; S; SS]; ~<~ [E; EE; SE; PSK]; ~>~ []; ~<~ []]

private let nwf1_1 = check_handshake_pattern_well_formed hskp1_1
private let nwf1_2 = check_handshake_pattern_well_formed hskp1_2
private let nwf1_3 = check_handshake_pattern_well_formed hskp1_3
private let nwf1_4 = check_handshake_pattern_well_formed hskp1_4
private let test_nwf1 = not nwf1_1 && not nwf1_2 && not nwf1_3 && not nwf1_4

private let hskp2_1 = hs "" [~>~ [E]; ~<~ [E; EE; SE]; ~>~ []; ~<~ []]
private let hskp2_2 = hs "" [~>>~ [PS]; ~>~ []; ~<~ [E; EE; SE]; ~>~ []; ~<~ []]
private let hskp2_3 = hs "" [~>>~ [PS]; ~>~ [E]; ~<~ [EE; SE]; ~>~ []; ~<~ []]

private let nwf2_1 = check_handshake_pattern_well_formed hskp2_1
private let nwf2_2 = check_handshake_pattern_well_formed hskp2_2
private let nwf2_3 = check_handshake_pattern_well_formed hskp2_3
private let test_nwf2 = not nwf2_1 && not nwf2_2 && not nwf2_3

private let hskp3_2 = hs "" [~>>~ [PS]; ~>~ []; ~<~ [E; EE; SE; S; ES]; ~>~ []; ~<~ []]
private let hskp3_3 = hs "" [~>>~ [PS]; ~>~ [E]; ~<~ [EE; SE; S; ES]; ~>~ []; ~<~ []]
private let hskp3_4 = hs "" [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE; ES]; ~>~ []; ~<~ []]

private let nwf3_2 = check_handshake_pattern_well_formed hskp3_2
private let nwf3_3 = check_handshake_pattern_well_formed hskp3_3
private let nwf3_4 = check_handshake_pattern_well_formed hskp3_4
private let test_nwf3 = not nwf3_2 && not nwf3_3 && not nwf3_4

private let hskp4_1 = hs "" [~>~ [E; ES]; ~<~ [E; EE]; ~>~ []]
private let hskp4_2 = hs "" [~<<~ [PS]; ~>~ [ES]; ~<~ [E; EE]; ~>~ []]
private let hskp4_3 = hs "" [~<<~ [PS]; ~>~ [E; ES]; ~<~ [EE]; ~>~ []]

private let nwf4_1 = check_handshake_pattern_well_formed hskp4_1
private let nwf4_2 = check_handshake_pattern_well_formed hskp4_2
private let nwf4_3 = check_handshake_pattern_well_formed hskp4_3
private let test_nwf4 = not nwf4_1 && not nwf4_2 && not nwf4_3

private let test_all_wf = test_wf && test_nwf1 && test_nwf2 && test_nwf3 && test_nwf4

private let test_all_wf_lem () :
  Lemma(test_all_wf == true) =
  assert_norm(test_all_wf == true)

(*** Properties *)
val check_send_message_smi_psk_no_diff_lem :
     smi : meta_info
  -> initiator : bool
  -> is_psk : bool
  -> message : list message_token ->
  Lemma
  (requires (not (List.mem PSK message)))
  (ensures (
    check_send_message_smi (smi_set_psk true smi) initiator is_psk message =
    check_send_message_smi (smi_set_psk false smi) initiator is_psk message))
  (decreases message)

val check_receive_message_smi_psk_no_diff_lem :
     smi : meta_info
  -> initiator : bool
  -> is_psk : bool
  -> message : list message_token ->
  Lemma
  (requires (not (List.mem PSK message)))
  (ensures (
    check_receive_message_smi (smi_set_psk true smi) initiator is_psk message =
    check_receive_message_smi (smi_set_psk false smi) initiator is_psk message))
  (decreases message)

val check_handshake_pattern_well_formed_forall_psk_true_lem :
     hsk : wf_handshake_pattern
  -> i : nat{ i < List.length hsk.messages} ->
  Lemma(
    let msg = List.Tot.index hsk.messages i in
    let is_psk = chskf_check_is_psk hsk in
    let ir = is_even i in
    let has_psk = true in (**)
    let ssmi0 = csend_message_pre_smi hsk has_psk i in
    let rsmi0 = creceive_message_pre_smi hsk has_psk i in
    check_send_message_smi ssmi0 ir is_psk msg /\
    check_receive_message_smi rsmi0 (not ir) is_psk msg)

let csend_message_smi_precond (hsk : wf_handshake_pattern) (has_psk : bool)
                              (i : nat{i < List.length hsk.messages}) =
  let msg = List.Tot.index hsk.messages i in
  let is_psk = chskf_check_is_psk hsk in
  let ir = is_even i in
  let ssmi = csend_message_pre_smi hsk has_psk i in
  check_send_message_smi ssmi ir is_psk msg

let creceive_message_smi_precond (hsk : wf_handshake_pattern) (has_psk : bool)
                                 (i : nat{i < List.length hsk.messages}) =
  let msg = List.Tot.index hsk.messages i in
  let is_psk = chskf_check_is_psk hsk in
  let ir = is_even i in
  let rsmi = creceive_message_pre_smi hsk has_psk i in
  check_receive_message_smi rsmi (not ir) is_psk msg

val check_hsk_wf_csend_creceive_message_smi_precond_psk_no_diff_lem :
     hsk : wf_handshake_pattern
  -> has_psk : bool
  -> i : nat{i < List.length hsk.messages} ->
  Lemma
  (requires (List.mem PSK (List.Tot.index hsk.messages i) ==> has_psk))
  (ensures (
    csend_message_smi_precond hsk has_psk i /\
    creceive_message_smi_precond hsk has_psk i))

/// If the message pattern was checked (as part of checking a handshake pattern
/// well-formedness) then after having processed the tokens, just before payload
/// encryption, the nonce is not saturated.

val tokens_update_nonce_not_saturated :
     ir : bool
  -> is_psk : bool
  -> pattern : list message_token
  -> smi : meta_info ->
  Lemma
  (requires (
    check_send_message_smi smi ir is_psk pattern \/
    check_receive_message_smi smi ir is_psk pattern))
  (ensures (
    let smi = send_tokens_update_smi is_psk pattern smi in
    smi.nonce < saturated_nonce_value))
  (decreases pattern)
