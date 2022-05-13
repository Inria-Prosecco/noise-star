module Spec.Noise.API.MetaInfo

open Spec.Noise
open Spec.Noise.API.State

open Meta.Noise

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** State meta info *)

[@@ (strict_on_arguments [0])]
inline_for_extraction noextract
let get_send_recv_premsgs (pattern : handshake_pattern) (initiator : bool) :
  option (list premessage_token) & option (list premessage_token) =
  if initiator then pattern.premessage_ir, pattern.premessage_ri
  else pattern.premessage_ri, pattern.premessage_ir  


/// First, we need to define the smis that are valid at every point in the process.

[@@ (strict_on_arguments [0])]
inline_for_extraction noextract
let knows_rs_at_init (hsk : handshake_pattern) (initiator : bool) : bool =
  let send, recv = get_send_recv_premsgs hsk initiator in
  Some? recv

[@@ (strict_on_arguments [0])]
inline_for_extraction noextract
let knows_psk_at_init (hsk : handshake_pattern) (initiator : bool) : bool =
  let is_psk = check_hsk_is_psk hsk in
  is_psk &&
  // We know the psk at initialization if:
  // 1. we know the remote at initialization
  (knows_rs_at_init hsk initiator ||
  // 2. or if we don't receive any remote static
   (if initiator then not (compute_hsk_flags hsk).hsk_rs
    else not (compute_hsk_flags hsk).hsk_is))

[@@ (strict_on_arguments [0])]
inline_for_extraction noextract
let knows_remote_at_init hsk initiator =
  knows_rs_at_init hsk initiator || knows_psk_at_init hsk initiator

/// Compute whether, given a specific status, we should have received a remote
/// static key.
[@@ (strict_on_arguments [2])]
inline_for_extraction noextract
let rec filter_alternate (#a : Type) (filter : bool) (ls : list a) :
  Tot (list a)
  (decreases ls) =
  match ls with
  | [] -> []
  | x :: ls' ->
    let ls'' = filter_alternate (not filter) ls' in
    if filter then ls'' else x :: ls''

[@@ (strict_on_arguments [1])]
inline_for_extraction noextract
let received_rs_in_messages (initiator : bool) (msgs : list (list message_token)) =
  let msgs' = filter_alternate initiator msgs in
  (* Originally written as:
   * [> List.Tot.mem S (List.Tot.flatten msgs')
   * But the new form is better for the proofs *)
  List.Tot.existsb (List.Tot.mem S) msgs'

[@@ (strict_on_arguments [0])]
inline_for_extraction noextract
let step_to_smi (hsk : handshake_pattern) (initiator : bool)
                (step : nat{step <= List.Tot.length hsk.messages}) : meta_info =
  let is_psk = check_hsk_is_psk hsk in
  let knows_psk_at_init = knows_psk_at_init hsk initiator in
  let smi1, smi2 = handshake_pattern_smi hsk knows_psk_at_init step in
  let smi =
    if initiator then if step % 2 = 0 then smi1 else smi2
    else if step % 2 = 0 then smi2 else smi1
  in
  smi_or_set_psk (is_psk && smi.hsf.rs) smi

[@@ (strict_on_arguments [0])]
inline_for_extraction noextract
let knows_remote (hsk : handshake_pattern) (initiator : bool)
                 (step : nat{step <= List.Tot.length hsk.messages}) =
  let knows_at_init = knows_remote_at_init hsk initiator in
  let smi = step_to_smi hsk initiator step in
  knows_at_init || smi.hsf.rs

/// Returns true if we should use a remote static key to lookup the psk at some point
[@@ (strict_on_arguments [0])]
inline_for_extraction noextract
let lookups_psk (hsk : handshake_pattern) (initiator : bool) =
  not (knows_psk_at_init hsk initiator) &&
  check_hsk_is_psk hsk

/// Control whether we allocate a slot for a key/computation or not
/// Handshake state key slots
inline_for_extraction noextract
type key_slots = {
  (* Device *)
  ks_s : bool;
  (* State *)
  ks_e : bool;
  ks_re : bool;
  (* Peer *)
  ks_rs : bool;
  ks_psk : bool;

  (* Transport *)
  ks_send : bool;
  ks_receive : bool;
}

inline_for_extraction noextract
let ks_get_s ks = match ks with Mkkey_slots s e re rs psk send recv -> s
inline_for_extraction noextract
let ks_get_e ks = match ks with Mkkey_slots s e re rs psk send recv -> e
inline_for_extraction noextract
let ks_get_re ks = match ks with Mkkey_slots s e re rs psk send recv -> re
inline_for_extraction noextract
let ks_get_rs ks = match ks with Mkkey_slots s e re rs psk send recv -> rs
inline_for_extraction noextract
let ks_get_psk ks = match ks with Mkkey_slots s e re rs psk send recv -> psk
inline_for_extraction noextract
let ks_get_send ks = match ks with Mkkey_slots s e re rs psk send recv -> send
inline_for_extraction noextract
let ks_get_receive ks = match ks with Mkkey_slots s e re rs psk send recv -> recv

inline_for_extraction noextract
let ks_valid_meta_info (ks : key_slots) (smi : meta_info) : bool =
  (not smi.hsf.s || ks_get_s ks) &&
  (not smi.hsf.e || ks_get_e ks) &&
  (not smi.hsf.rs || ks_get_rs ks) &&
  (not smi.hsf.re || ks_get_re ks) &&
  (not smi.hsf.psk || ks_get_psk ks)

[@@ (strict_on_arguments [1])]
inline_for_extraction noextract
let key_slots_from_pattern (initiator : bool) (hsk : handshake_pattern) : key_slots =
  let l = List.Tot.length hsk.messages in
  let is_psk = check_hsk_is_psk hsk in
  let smi = step_to_smi hsk initiator l in
  {
    ks_s = smi.hsf.s;
    ks_e = smi.hsf.e;
    ks_re = smi.hsf.re;
    ks_rs = smi.hsf.rs;
    ks_psk = smi.hsf.psk;
    ks_send = can_send initiator hsk;
    ks_receive = can_receive initiator hsk;
  }

(*** Lengths *)

/// The following helper computes the length of a message, without the payload.
/// The total length of message i (starting from 0) is:
/// [> payload_length + compute_message_length ...
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let compute_message_length
  (nc : config)
  (hsk : handshake_pattern)
  (step : nat{step < List.Tot.length hsk.messages}) :
//  (step : nat{step < normalize_term (List.Tot.length hsk.messages)}) :
  nat =
//  (**) normalize_term_spec(List.Tot.length hsk.messages);
  let is_psk = check_hsk_is_psk hsk in
  let pat = List.Tot.index hsk.messages step in
  let initiator = true in // doesn't matter
  let smi = step_to_smi hsk initiator step in
  let has_sym_key = smi.hsf.sk in
  let l1 = tokens_message_size nc has_sym_key is_psk pat in
  let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pat in
  let aead_length = if has_sym_key' then aead_tag_size else 0 in
  l1 + aead_length

/// We use this helper to check that all patterns generate messages of length > 0
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let compute_min_message_length
  (hsk : handshake_pattern)
  (step : nat{step < List.Tot.length hsk.messages}) :
  nat =
  let is_psk = check_hsk_is_psk hsk in
  let pat = List.Tot.index hsk.messages step in
  let initiator = true in // doesn't matter
  let smi = step_to_smi hsk initiator step in
  let has_sym_key = smi.hsf.sk in
  let l1 = min_tokens_message_size has_sym_key is_psk pat in
  let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk pat in
  let aead_length = if has_sym_key' then aead_tag_size else 0 in
  l1 + aead_length

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let compute_min_message_length_lem
  (nc : config)
  (hsk : handshake_pattern)
  (step : nat{step < List.Tot.length hsk.messages}) :
  Lemma (compute_min_message_length hsk step <= compute_message_length nc hsk step) =
  let is_psk = check_hsk_is_psk hsk in
  let pat = List.Tot.index hsk.messages step in
  let initiator = true in // doesn't matter
  let smi = step_to_smi hsk initiator step in
  let has_sym_key = smi.hsf.sk in
  min_tokens_message_size_lem nc has_sym_key is_psk pat

(*** Security levels *)

/// Note that if the pattern is two-ways, we compute the security levels
/// for the handshake messages plus two transport messages. Otherwise,
/// we don't care about transport messages. The reason is that the security
/// levels may be improved once we have received the first transport message,
/// because we then know the remote was able to process the last handshake
/// message we sent, meaning he was able to perform the DHs, etc.
/// This makes the security levels computation a bit tricky for the transport messages.

open FStar.List.Tot
open Spec.Noise.PatternsSecurity

/// Return true if this party is the one who sends the last message of
/// the handshake.
[@(strict_on_arguments [0; 1])]
inline_for_extraction noextract
let sends_last_handshake (initiator : bool) (pattern : handshake_pattern) : Tot bool =
  let num_msgs = length pattern.messages in
  if initiator then (num_msgs % 2) = 1
  else (num_msgs % 2) = 0

[@(strict_on_arguments [0; 1])]
inline_for_extraction noextract
let receives_last_handshake (initiator : bool) (pattern : handshake_pattern) : Tot bool =
  not (sends_last_handshake initiator pattern)

/// Do we need to remember the fact that we received a transport message or not?
/// Only the case if it is a two-ways pattern and if the party is the last one to
/// send a message during the handshake.
[@(strict_on_arguments [0; 1])]
inline_for_extraction noextract
let save_received_transport (initiator : bool) (pattern : handshake_pattern) : Tot bool =
  if with_onorm #bool (length pattern.messages <= 1) then false // one-way pattern
  else with_onorm #bool (sends_last_handshake initiator pattern)

/// Confidentiality level for a sender - none if we can't send a message
/// (can be the case if the pattern is one-way).
[@(strict_on_arguments [0; 1; 2])]
noextract inline_for_extraction
val compute_transport_conf_level
  (initiator : bool) (pattern : handshake_pattern)
  (received_transport_message : bool) : option conf_level

#push-options "--fuel 1 --ifuel 1"
let compute_transport_conf_level initiator pattern received_transport_message =
  let levels = ac_levels pattern in
  let num_msgs = length pattern.messages in
  if num_msgs = 0 || None? levels then None
  else
    let levels = Some?.v levels in
    if num_msgs > 1 then
      // Two ways handshake pattern
      let ac_level =
        // First, we need to know whether we sent the last handshake message or not
        let sent_last_handshake = sends_last_handshake initiator pattern in
        // If sent the last message handshake message, then there is a case
        // disjunction on whether we received a transport message or not
        if sent_last_handshake then
          if received_transport_message then
            // Yes: level is the last one
            index levels (num_msgs+1)
          else
            // No: level is the last handshake level
            index levels (num_msgs-1)
        else
          // Level is the level before last
            index levels num_msgs
      in
      Some (snd ac_level)
    else
      // One way
      if initiator then
        Some (snd (index levels (length pattern.messages - 1)))
      else None
#pop-options

/// Authentication level for a receiver - none if we can't receive a message
/// (can be the case if the pattern is one-way).
[@(strict_on_arguments [0; 1])]
noextract inline_for_extraction
val compute_transport_auth_level
  (initiator : bool) (pattern : handshake_pattern) : option auth_level

#push-options "--fuel 1 --ifuel 1"
let compute_transport_auth_level initiator pattern =
  let levels = ac_levels pattern in
  let num_msgs = length pattern.messages in
  if num_msgs = 0 || None? levels then None
  else
    let levels = Some?.v levels in
    if num_msgs > 1 then
      // Two ways handshake pattern
      let ac_level =
        // If we received the last handshake message, the transport
        // authentication level is the last of the list of levels,
        // otherwise it is the one before last.
        // Note that for two-way patterns, ac_levels computes auth/conf levels
        // for all the handshake messages + two transport messages.
        let recv_last_handshake = not (sends_last_handshake initiator pattern) in
        if recv_last_handshake then index levels (num_msgs + 1)
        else index levels num_msgs
      in
      Some (fst ac_level)
    else
      // One way
      if not (initiator) then
        Some (fst (index levels (length pattern.messages - 1)))
      else None
#pop-options

