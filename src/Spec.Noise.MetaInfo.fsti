module Spec.Noise.MetaInfo
open FStar.Mul

open Spec.Noise.Base
open Spec.Noise.HandshakeFlags
open Spec.Noise.NonceCounter

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

/// Defines the information about the handshake state that we will carry around
/// in the implementation functions. We qualify this information as meta because:
/// - it is statically known
/// - it has an influence on computation (for example: encryption/decryption is
///   conditionned at several positions on the presence of a symmetric key - still:
///   note that part of the information is actually ghost)
/// - the structures carrying this information will be erased by post-processing and
///   inlining and thus won't appear in the generated code, and the branches testing
///   meta booleans will be simplified thus leading to correctly specialized code

// TODO: we could put the [is_psk] and [initiator] field inside the [meta_info].
// Or at leat initiator

(** state meta info *)
inline_for_extraction //noextract
type meta_info = {
  hsf : handshake_state_flags;
  nonce : nat;
}

/// [meta_info] is monotonous over a handshake execution

noextract
let less_than (smi1 smi2 : meta_info) : Tot bool =
  Spec.Noise.HandshakeFlags.less_than smi1.hsf smi2.hsf

inline_for_extraction noextract
type greater_smi (smi0 : meta_info) =
  smi1:meta_info{less_than smi0 smi1}

let smi_set_psk (psk : bool) (smi : meta_info) : Tot meta_info =
  { smi with hsf = { smi.hsf with psk = psk } }

let smi_set_sk (sk : bool) (smi : meta_info) : Tot meta_info =
  { smi with hsf = { smi.hsf with sk = sk; } }

let smi_or_set_psk (psk : bool) (smi : meta_info) : Tot meta_info =
  { smi with hsf = { smi.hsf with psk = psk || smi.hsf.psk } }

(*** Update functions *)
noextract
let receive_pretoken_update_smi (tk : premessage_token) (smi : meta_info) :
  Tot meta_info =
  { smi with hsf = receive_pretoken_update_hsf tk smi.hsf }

noextract
let receive_premessage_update_smi (pattern : list premessage_token)
                                  (smi : meta_info) :
  smi':greater_smi smi {
    let hsf, hsf' = smi.hsf, smi'.hsf in
    hsf'.sk == hsf.sk /\ hsf'.s == hsf.s /\ hsf'.e == hsf.e /\ hsf'.psk == hsf.psk} =
  { smi with hsf = receive_premessage_update_hsf pattern smi.hsf }

inline_for_extraction noextract
let send_token_update_smi (is_psk : bool) (tk : message_token)
                          (smi : meta_info) :
  Tot (greater_smi smi) =
  {
    hsf = send_token_update_hsf is_psk tk smi.hsf;
    nonce = token_update_nonce smi.hsf.sk is_psk tk smi.nonce;
  }

inline_for_extraction noextract
let receive_token_update_smi (is_psk : bool) (tk : message_token)
                             (smi : meta_info) :
  Tot (greater_smi smi) =
  {
    hsf = receive_token_update_hsf is_psk tk smi.hsf;
    nonce = token_update_nonce smi.hsf.sk is_psk tk smi.nonce;
  }

inline_for_extraction noextract
let token_update_smi (is_psk sender : bool) (tk : message_token)
                     (smi : meta_info) :
  Tot (greater_smi smi) =
  if sender then send_token_update_smi is_psk tk smi
            else receive_token_update_smi is_psk tk smi

inline_for_extraction noextract
let send_tokens_update_smi (is_psk : bool) (pattern : list message_token)
                            (smi : meta_info) :
  greater_smi smi =
  let hsf1 = send_tokens_update_hsf is_psk pattern smi.hsf in
  let nonce1 = tokens_update_nonce smi.hsf.sk is_psk pattern smi.nonce in
  { hsf = hsf1; nonce = nonce1; }

inline_for_extraction noextract
let receive_tokens_update_smi (is_psk : bool) (pattern : list message_token)
                               (smi : meta_info) :
  greater_smi smi =
  let hsf1 = receive_tokens_update_hsf is_psk pattern smi.hsf in
  let nonce1 = tokens_update_nonce smi.hsf.sk is_psk pattern smi.nonce in
  { hsf = hsf1; nonce = nonce1; }

inline_for_extraction noextract
let send_message_update_smi (is_psk : bool) (pattern : list message_token)
                            (smi : meta_info) :
  greater_smi smi =
  let smi1 = send_tokens_update_smi is_psk pattern smi in
  { smi1 with nonce = if smi1.hsf.sk then smi1.nonce + 1 else smi1.nonce }

inline_for_extraction noextract
let receive_message_update_smi (is_psk : bool) (pattern : list message_token)
                               (smi : meta_info) :
  greater_smi smi =
  let smi1 = receive_tokens_update_smi is_psk pattern smi in
  { smi1 with nonce = if smi1.hsf.sk then smi1.nonce + 1 else smi1.nonce }

(*** Crawlers *)
(**** Compute over lisf of tokens *)
// TODO: those crawlers are more annoying than anything: get rid of them
(* TODO: for now, those are not used *)
type message_tokens_crawler (a : Type) : Type =
  (send_smi : meta_info) -> (recv_smi : meta_info) ->
  (tk : message_token) -> (acc : a) -> a

[@(strict_on_arguments [6])]
inline_for_extraction noextract
let rec crawl_message_tokens (a : Type)
                             (crawler : message_tokens_crawler a)
                             (acc : a)
                             (is_psk : bool)
                             (send_smi recv_smi : meta_info)
                             (message : list message_token) :
  Tot a (decreases message) =
  match message with
  | [] -> acc
  | tk :: message' ->
    (* Update the accumulator *)
    let acc1 = crawler send_smi recv_smi tk acc in
    (* Update the flags *)
    let send_smi1 = send_token_update_smi is_psk tk send_smi in
    let recv_smi1 = receive_token_update_smi is_psk tk recv_smi in
    (* Recursive call *)
    crawl_message_tokens a crawler acc1 is_psk send_smi recv_smi message'

(**** Compute over list of messages *)
(* Handshake pattern crawler: allows to traverse the messages of a
 * handshake_pattern with the proper meta_info for the sender
 * and the receiver *)
type handshake_messages_crawler (a : Type) : Type =
  (is_psk : bool) -> (ir : bool) ->
  (send_smi0 : meta_info) -> (recv_smi0 : meta_info) ->
  (send_smi1 : greater_smi recv_smi0) -> (recv_smi1 : greater_smi send_smi0) ->
  (msg : list message_token) -> (acc : a) -> a

(* A boolean crawler with no accumulator *)
type handshake_messages_crawl_checker =
  (is_psk : bool) -> (ir : bool) ->
  (send_smi0 : meta_info) -> (recv_smi0 : meta_info) ->
  (send_smi1 : greater_smi recv_smi0) -> (recv_smi1 : greater_smi send_smi0) ->
  (msg : list message_token) -> bool

let crawl_messages_update_smi (is_psk : bool)
                              (msg : list message_token)
                              (send_smi recv_smi : meta_info) :
  (fp:(meta_info & meta_info){
    less_than send_smi (snd fp) /\ less_than recv_smi (fst fp)})=
  let recv_smi1 = send_message_update_smi is_psk msg send_smi in
  let send_smi1 = receive_message_update_smi is_psk msg recv_smi in
  send_smi1, recv_smi1

[@(strict_on_arguments [7])]
let rec crawl_handshake_messages (a : Type)
                                 (crawler : handshake_messages_crawler a)
                                 (acc : a)
                                 (is_psk ir : bool)
                                 (send_smi recv_smi : meta_info)
                                 (messages : list (list message_token)) :
  Tot a (decreases messages) =
  match messages with
  | [] -> acc
  | msg :: messages' ->
    (* Update the flags over the pattern, invert the sender and receiver *)
    let send_smi1, recv_smi1 = crawl_messages_update_smi is_psk msg send_smi recv_smi in
    (* Update the accumulator *)
    let acc1 = crawler is_psk ir send_smi recv_smi send_smi1 recv_smi1 msg acc in
    (* Recursive call: negate the direction and reverse the sender and receiver flags *)
    crawl_handshake_messages a crawler acc1 is_psk (not ir) send_smi1 recv_smi1 messages'

let crawl_forallb_handshake_messages (checker : handshake_messages_crawl_checker)
                                     (is_psk ir : bool)
                                     (send_smi recv_smi : meta_info)
                                     (messages : list (list message_token)) :
  Tot bool =
  let acc_checker is_psk ir sf0 rf0 sf1 rf1 msg acc =
    acc && checker is_psk ir sf0 rf0 sf1 rf1 msg
  in
  crawl_handshake_messages bool acc_checker true is_psk ir send_smi recv_smi messages

let and_crawler (checker : handshake_messages_crawl_checker)
                (is_psk ir : bool)
                (ssmi0 rsmi0 : meta_info)
                (ssmi1 : greater_smi rsmi0) (rsmi1 : greater_smi ssmi0)
                (msg : list message_token) (acc : bool) : Tot bool =
  acc && checker is_psk ir ssmi0 rsmi0 ssmi1 rsmi1 msg

let or_crawler (checker : handshake_messages_crawl_checker)
               (is_psk ir : bool)
               (ssmi0 rsmi0 : meta_info)
               (ssmi1 : greater_smi rsmi0) (rsmi1 : greater_smi ssmi0)
               (msg : list message_token) (acc : bool) : Tot bool =
  acc || checker is_psk ir ssmi0 rsmi0 ssmi1 rsmi1 msg

let forallb_handshake_messages (checker : handshake_messages_crawl_checker)
                               (is_psk ir : bool)
                               (send_smi recv_smi : meta_info)
                               (messages : list (list message_token)) :
  Tot bool =
  crawl_handshake_messages bool (and_crawler checker) true is_psk ir send_smi recv_smi messages

let existsb_handshake_messages (checker : handshake_messages_crawl_checker)
                               (is_psk ir : bool)
                               (send_smi recv_smi : meta_info)
                               (messages : list (list message_token)) :
  Tot bool =
  crawl_handshake_messages bool (or_crawler checker) false is_psk ir send_smi recv_smi messages

(**** Compute over whole pattern *)
(***** Definitions *)
(* Returns the meta info after partial evaluation of the messages *)
// TODO: we use splitAt. This is not the proper way of doing that: it makes
// using this function difficult in an implementation (see the "step" lemmas
// like handshake_pattern_smi_step_lem, which are necessary to correctly
// use those functions). The proper way of doing that is with a function
// recursive over i, which lookups messages with List.Tot.index messages i.
// Rough sketch:
// let rec handshake_messages_pre_smi ... i =
//   if i = 0 then
//     send_smi, recv_smi
//   else
//     let send_smi, recv_smi = handshake_messages_pre_smi ... (i-1) in
//     let message = List.Tot.index messages i in
//     crawl_messages_update_smi ... message ...
// This way, we have a nice-looking, natural to use function.
let handshake_messages_pre_smi (is_psk ir : bool)
                               (send_smi recv_smi : meta_info)
                               (messages : list (list message_token))
                               (i : nat{i <= List.length messages}) :
  Tot (meta_info & meta_info) =
  let begin_messages = fst (List.Tot.splitAt i messages) in
  (* We return a pair of meta info *)
  let a = meta_info & meta_info in
  let crawler : handshake_messages_crawler a =
    (fun is_psk ir ssmi0 rsmi0 ssmi1 rsmi1 msg acc ->
      ((ssmi1 <: meta_info), (rsmi1 <: meta_info))) in
  let acc0 : a = send_smi, recv_smi in
  crawl_handshake_messages a crawler acc0 is_psk ir send_smi recv_smi begin_messages

// TODO: use this in compute_premessages_post_smi instead of compute_hsk_flags
let compute_consume_premessages_hsf (hsk : handshake_pattern) :
  handshake_state_flags & handshake_state_flags =
  let hsf_init = compute_consume_premessages_hsf hsk true in
  let hsf_resp = compute_consume_premessages_hsf hsk false in
  hsf_init, hsf_resp

let compute_premessages_post_smi (hsk : handshake_pattern) (set_psk : bool) :
  meta_info & meta_info & bool =
  let hskf = compute_hsk_flags hsk in
  let is_psk = hskf.hsk_psk in
  let psk = set_psk in
  (* set the s and e flags for the initiator and the responder *)
  let is = hskf_uses_is hskf in
  let ie = hskf_uses_ie hskf in
  let rs = hskf_uses_rs hskf in
  let re = hskf_uses_re hskf in
  let hsf0 = handshake_state_cleared_flags in
  (* Note that the psk flag doesn't really matter here *)
  let ihsf = { hsf0 with s = is; e = ie; rs = hskf.hsk_prs; re = hskf.hsk_pre; psk = psk } in
  let rhsf = { hsf0 with s = rs; e = re; rs = hskf.hsk_pis; re = hskf.hsk_pie; psk = psk } in
  (* Return *)
  let ismi = { hsf = ihsf; nonce = 0; } in
  let rsmi = { hsf = rhsf; nonce = 0; } in
  ismi, rsmi, is_psk

let crawl_handshake_pattern_messages (hsk : handshake_pattern) (set_psk : bool)
                                     (a : Type) (acc0 : a)
                                     (crawler : handshake_messages_crawler a) :
  Tot a =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk set_psk in
  crawl_handshake_messages a crawler acc0 is_psk true ismi rsmi hsk.messages

let forallb_handshake_pattern_messages (hsk : handshake_pattern) (set_psk : bool)
                                       (checker : handshake_messages_crawl_checker) :
  Tot bool =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk set_psk in
  forallb_handshake_messages checker is_psk true ismi rsmi hsk.messages

(* Returns the meta info computed after the i first messages of the
 * handshake *)
let handshake_pattern_smi (hsk : handshake_pattern) (set_psk : bool)
                          (i : nat{i <= List.length hsk.messages}) :
  meta_info & meta_info =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk set_psk in
  handshake_messages_pre_smi is_psk true ismi rsmi hsk.messages i

(***** Compute over whole pattern: properties *)
(* A lemma which allows to reason step by step about the crawling computation *)
val crawl_handshake_messages_step_lem
  (a : Type)
  (crawler : handshake_messages_crawler a)
  (acc0 : a)
  (is_psk ir : bool)
  (ssmi rsmi : meta_info)
  (messages : list (list message_token))
  (i : nat{i < List.length messages}) :
  Lemma
  (ensures (
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi
                                                  messages i in
    let msg = List.Tot.index messages i in
    let messages1 = fst (List.Tot.splitAt i messages) in
    let messages2 = fst (List.Tot.splitAt (i+1) messages) in
    let ssmi2, rsmi2 = crawl_messages_update_smi is_psk msg ssmi1 rsmi1 in
    let crawl_fun = crawl_handshake_messages a crawler acc0 is_psk ir ssmi rsmi in
    let acc1 = crawl_fun messages1 in
    let acc2 = crawl_fun messages2 in
    let ir' = if is_even i then ir else not ir in
    acc2 == crawler is_psk ir' ssmi1 rsmi1 ssmi2 rsmi2 msg acc1))
  (decreases messages)

(* From the lemma above we deduce the following one *)
val handshake_messages_pre_smi_step_lem (is_psk ir : bool)
                                        (ssmi rsmi : meta_info)
                                        (messages : list (list message_token))
                                        (i : nat{i < List.length messages}) :
  Lemma(
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
    let ssmi2, rsmi2 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages (i+1) in
    let msg = List.Tot.index messages i in
    (ssmi2, rsmi2) == crawl_messages_update_smi is_psk msg ssmi1 rsmi1)

val handshake_pattern_smi_step_lem (hsk : handshake_pattern) (set_psk : bool)
                                   (i : nat{i < List.length hsk.messages}) :
  Lemma(
    let is_psk = (compute_hsk_flags hsk).hsk_psk in
    let ssmi1, rsmi1 = handshake_pattern_smi hsk set_psk i in
    let ssmi2, rsmi2 = handshake_pattern_smi hsk set_psk (i+1) in
    let msg = List.Tot.index hsk.messages i in
    (ssmi2, rsmi2) == crawl_messages_update_smi is_psk msg ssmi1 rsmi1)

val crawl_handshake_messages_pred_lem (a : Type)
                                      (crawler : handshake_messages_crawler a)
                                      (p : a -> prop)
                                      (acc : a)
                                      (is_psk ir : bool)
                                      (send_smi recv_smi : meta_info)
                                      (messages : list (list message_token)) :
  Lemma
  (requires
    (* Predicate valid on the first element *)
    (p acc) /\
    (* Step condition *)
    (forall acc0 msg ir ssmi0 rsmi0.
     let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi0 rsmi0 in
     let acc1 = crawler is_psk ir ssmi0 rsmi0 ssmi1 rsmi1 msg acc0 in
     p acc0 ==> p acc1))
  (ensures (p (crawl_handshake_messages a crawler acc is_psk ir send_smi recv_smi messages)))
  (decreases messages)

val forallb_handshake_messages_and_lem (checker : handshake_messages_crawl_checker)
                                       (b0 : bool)
                                       (is_psk ir : bool)
                                       (ssmi rsmi : meta_info)
                                       (msg : list message_token)
                                       (messages : list (list message_token)) :
  Lemma
  (ensures (
    crawl_handshake_messages bool (and_crawler checker) b0 is_psk
                             ir ssmi rsmi (msg :: messages) =
    (let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi rsmi in
     let ir1 = not ir in
     let b1 = b0 && (checker is_psk ir ssmi rsmi ssmi1 rsmi1 msg) in
     let b2 = forallb_handshake_messages checker is_psk ir1 ssmi1 rsmi1 messages in
     b1 && b2)))
  (decreases messages)

val existsb_handshake_messages_or_lem (checker : handshake_messages_crawl_checker)
                                      (b0 : bool)
                                      (is_psk ir : bool)
                                      (ssmi rsmi : meta_info)
                                      (msg : list message_token)
                                      (messages : list (list message_token)) :
  Lemma
  (ensures (
    crawl_handshake_messages bool (or_crawler checker) b0 is_psk
                             ir ssmi rsmi (msg :: messages) =
    (let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi rsmi in
     let ir1 = not ir in
     let b1 = b0 || (checker is_psk ir ssmi rsmi ssmi1 rsmi1 msg) in
     let b2 = existsb_handshake_messages checker is_psk ir1 ssmi1 rsmi1 messages in
     b1 || b2)))
  (decreases messages)

let checkerb_handshake_messages_one (checker : handshake_messages_crawl_checker)
                                    (is_psk ir : bool)
                                    (ssmi rsmi : meta_info)
                                    (messages : list (list message_token))
                                    (i : nat{i < List.length messages}) : Tot bool =
  let msg = List.Tot.index messages i in
  let ssmi0, rsmi0 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
  let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi0 rsmi0 in
  let ir1 = if is_even i then ir else not ir in
  checker is_psk ir1 ssmi0 rsmi0 ssmi1 rsmi1 msg

val forallb_handshake_messages_lem (checker : handshake_messages_crawl_checker)
                                   (is_psk ir : bool)
                                   (ssmi rsmi : meta_info)
                                   (messages : list (list message_token)) :
  Lemma
  (ensures (
    forallb_handshake_messages checker is_psk ir ssmi rsmi messages <==>
    (forall (i : nat{i < List.length messages}).
    checkerb_handshake_messages_one checker is_psk ir ssmi rsmi messages i)))
  (decreases messages)

val existsb_handshake_messages_lem (checker : handshake_messages_crawl_checker)
                                   (is_psk ir : bool)
                                   (ssmi rsmi : meta_info)
                                   (messages : list (list message_token)) :
  Lemma
  (ensures (
    existsb_handshake_messages checker is_psk ir ssmi rsmi messages <==>
    (exists (i : nat{i < List.length messages}).
    checkerb_handshake_messages_one checker is_psk ir ssmi rsmi messages i)))
  (decreases messages)

val forallb_handshake_pattern_messages_lem (hsk : handshake_pattern)
                                           (set_psk : bool)
                                           (checker : handshake_messages_crawl_checker) :
  Lemma (
    let ismi, rsmi, is_psk = compute_premessages_post_smi hsk set_psk in
    forallb_handshake_pattern_messages hsk set_psk checker <==>
    (forall (i : nat{i < List.length hsk.messages}).
    checkerb_handshake_messages_one checker is_psk true ismi rsmi hsk.messages i))

(** Monotonicity *)
// TODO: in the fsti, less_than refers to the local definition, in the fst it
// refers to Spec.Noise.HandshakeFlags.less_than, which forces me to use
// fully qualified names. Besides, if I use the local definition with
// the fully qualified names, F* detecs a cyclic dependency...
val handshake_messages_pre_smi_is_greater_than_input (is_psk ir : bool)
                                                     (ssmi rsmi : meta_info)
                                                     (messages : list (list message_token))
                                                     (i : nat) :
  Lemma
  (requires (i <= List.Tot.length messages))
  (ensures (
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
    let ssmi2, rsmi2 = if i % 2 = 0 then ssmi1, rsmi1 else rsmi1, ssmi1 in
    ssmi.hsf `Spec.Noise.HandshakeFlags.less_than` ssmi2.hsf /\
    rsmi.hsf `Spec.Noise.HandshakeFlags.less_than` rsmi2.hsf))
  (decreases messages)

val handshake_messages_pre_smi_is_increasing (is_psk ir : bool)
                                             (ssmi rsmi : meta_info)
                                             (messages : list (list message_token))
                                             (i j : nat) :
  Lemma
  (requires (i <= List.Tot.length messages /\ j <= List.Tot.length messages /\ i <= j))
  (ensures (
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
    let ssmi2, rsmi2 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages j in
    let ssmi3, rsmi3 = if (j - i) % 2 = 0 then ssmi2, rsmi2 else rsmi2, ssmi2 in
    ssmi1.hsf `Spec.Noise.HandshakeFlags.less_than` ssmi3.hsf /\
    rsmi1.hsf `Spec.Noise.HandshakeFlags.less_than` rsmi3.hsf))
  (decreases messages)

val handshake_pattern_smi_is_increasing (hsk : handshake_pattern) (set_psk : bool)
                                        (i j : (n:nat{n <= List.Tot.length hsk.messages})) :
  Lemma
  (requires (i <= j))
  (ensures (
    let ssmi1, rsmi1 = handshake_pattern_smi hsk set_psk i in
    let ssmi2, rsmi2 = handshake_pattern_smi hsk set_psk j in
    let ssmi3, rsmi3 = if (j - i) % 2 = 0 then ssmi2, rsmi2 else rsmi2, ssmi2 in
    ssmi1.hsf `Spec.Noise.HandshakeFlags.less_than` ssmi3.hsf /\
    rsmi1.hsf `Spec.Noise.HandshakeFlags.less_than` rsmi3.hsf))

(*** Handshake functions flags *)
(**** Initialization *)
let initialize_post_smi (hsk : handshake_pattern) (initiator : bool) (psk : bool)
                        : meta_info =
  let hskf = compute_hsk_flags hsk in
  let s = if initiator then hskf_uses_is hskf else hskf_uses_rs hskf in
  let e = if initiator then hskf_uses_ie hskf else hskf_uses_re hskf in
  let hsf =
  {
    sk = false;
    s = s;
    e = e;
    rs = false;
    re = false;
    psk = psk;
  }
  in
  { hsf = hsf; nonce = 0; }

(**** Premessages *)
inline_for_extraction noextract
let get_premessage (hsk : handshake_pattern) (ir : bool) :
  list premessage_token =
  let pre = if ir then hsk.premessage_ir else hsk.premessage_ri in
  opt_list_to_list_or_empty pre

let csend_premessage_pre_smi (hsk : handshake_pattern) (ir has_psk : bool) :
  smi:meta_info{smi.hsf.psk == has_psk} =
  let smi0 = initialize_post_smi hsk ir has_psk in
  (* If initiator to receiver: nothing has happened since initialization *)
  if ir then smi0 else
  (* Otherwise: we are the receiver, we may have received a premessage from
   * the initiator *)
  match hsk.premessage_ir with
  | None -> smi0
  | Some pre -> receive_premessage_update_smi pre smi0

(* The "primitive" post-smi for [csend_premessage]. Note that this is the
 * natural post-smi for [csend_premessage], but it is not trivially related
 * to the pre-smis at the beginning of the handshake (after the premessage
 * exchange), which is why we use a different one in the postcondition of
 * [csend_premessage]. *)
let csend_premessage_ppost_smi (hsk : handshake_pattern) (ir has_psk : bool) :
  smi:meta_info{smi.hsf.psk == has_psk} =
  (* Sending a premessage has no impact on the flags *)
  csend_premessage_pre_smi hsk ir has_psk

let creceive_premessage_pre_smi (hsk : handshake_pattern) (ir has_psk : bool) :
  smi:meta_info{smi.hsf.psk == has_psk} =
  let initiator = not ir in
  (* If initiator to receiver: nothing has happened since initialization. *)
  if ir then initialize_post_smi hsk initiator has_psk
  (* If receiver to initiator: we (may) have sent a premessage before receiving one *)
  else csend_premessage_ppost_smi hsk initiator has_psk

(* Same remark as for [csend_premessage_ppost_smi] *)
let creceive_premessage_ppost_smi (hsk : handshake_pattern) (ir has_psk : bool) :
  smi:meta_info{smi.hsf.psk == has_psk} =
  let smi0 = creceive_premessage_pre_smi hsk ir has_psk in
  let opt_pre = if ir then hsk.premessage_ir else hsk.premessage_ri in
  match opt_pre with
  | None -> smi0
  | Some pre -> receive_premessage_update_smi pre smi0

(* The postcondition after the premessages have been exchanged. *)
let cexchange_premessage_post_smi (hsk : handshake_pattern)
                                  (initiator has_psk : bool) :
  smi:meta_info{ smi.hsf.psk == has_psk} =
  let ir = if initiator then not initiator else initiator in
  if initiator then creceive_premessage_ppost_smi hsk ir has_psk
               else csend_premessage_ppost_smi hsk ir has_psk

(**** Messages *)
inline_for_extraction noextract
let get_message (hsk : handshake_pattern) (i : nat{i < List.length hsk.messages}) :
  list message_token =
  List.Tot.index hsk.messages i

let csend_message_pre_smi
  (hsk : handshake_pattern)
  (set_psk : bool)
  (i : nat{i <= List.length hsk.messages}) =
  fst (handshake_pattern_smi hsk set_psk i)

let creceive_message_pre_smi
  (hsk : handshake_pattern)
  (set_psk : bool)
  (i : nat{i <= List.length hsk.messages}) =
  snd (handshake_pattern_smi hsk set_psk i)

let csend_message_post_smi
  (hsk : handshake_pattern)
  (set_psk : bool)
  (i : nat{i < List.length hsk.messages}) =
  snd (handshake_pattern_smi hsk set_psk (i+1))

let creceive_message_post_smi
  (hsk : handshake_pattern)
  (set_psk : bool)
  (i : nat{i < List.length hsk.messages}) =
  fst (handshake_pattern_smi hsk set_psk (i+1))

(***** Consistency lemmas *)
(* This lemma is true by construction but shows the kind of properties we are looking for *)
val csend_receive_message_pre_post_smi_consistent_lem
  (hsk : handshake_pattern)
  (set_psk : bool)
  (i : nat{0 < i /\ i < List.length hsk.messages}) :
  Lemma(
    csend_message_pre_smi hsk set_psk i ==
      creceive_message_post_smi hsk set_psk (i-1) /\
    creceive_message_pre_smi hsk set_psk i ==
      csend_message_post_smi hsk set_psk (i-1))

(* Another needed property, less trivial than above *)
val csend_creceive_cexchange_smi_consistent_lem
  (hsk : handshake_pattern{
    (match hsk.premessage_ir with | Some pre -> List.length pre <= 2| None -> True) /\
    (match hsk.premessage_ri with | Some pre -> List.length pre <= 2 | None -> True)})
  (has_psk : bool) :
  Lemma(
    csend_message_pre_smi hsk has_psk 0 ==
      cexchange_premessage_post_smi hsk true has_psk /\
    creceive_message_pre_smi hsk has_psk 0 ==
      cexchange_premessage_post_smi hsk false has_psk)

(* The general post-smi functions for the premessages (allow a smooth transition
 * from the premessages processing to the actual handshake) *)
let csend_premessage_post_smi (hsk : handshake_pattern)
                              (ir has_psk : bool) : meta_info =
  (* If responder to initiator: no subsequent premessage *)
  if not ir then creceive_message_pre_smi hsk has_psk 0
  (* Otherwise, two cases: there is a subsequent premessage (from responder
   * to initiator) or there isnt *)
  else if Some? hsk.premessage_ri then csend_premessage_ppost_smi hsk ir has_psk
  else csend_message_pre_smi hsk has_psk 0

let creceive_premessage_post_smi (hsk : handshake_pattern)
                                 (ir has_psk : bool) : meta_info =
  (* If responder to initiator: no subsequent premessage *)
  if not ir then csend_message_pre_smi hsk has_psk 0
  (* Otherwise, two cases: there is a subsequent premessage (from responder
   * to initiator) or there isnt *)
  else if Some? hsk.premessage_ri then creceive_premessage_ppost_smi hsk ir has_psk
  else creceive_message_pre_smi hsk has_psk 0

let updt_sk_consistent_with_receive_tokens_update_smi
  (is_psk : bool) (pattern : list message_token) (smi : meta_info) :
  Lemma(let smi1 = receive_tokens_update_smi is_psk pattern smi in
        tokens_update_sym_key_flag smi.hsf.sk is_psk pattern == smi1.hsf.sk) =
  updt_sk_consistent_with_receive_tokens_update_hsf_lem is_psk pattern smi.hsf

(**** Decomposition lemma *)
val receive_tokens_update_smi_decompose_lem (is_psk : bool)
                                            (tokens1 tokens2 : list message_token)
                                            (smi : meta_info) :
  Lemma
  (requires True)
  (ensures (
    let smi1 = receive_tokens_update_smi is_psk tokens1 smi in
    let smi2 = receive_tokens_update_smi is_psk tokens2 smi1 in
    let smi2' = receive_tokens_update_smi is_psk (List.Tot.append tokens1 tokens2) smi in
    smi2' = smi2))

(**** Frame lemmas *)
(** We can set the psk later than initialization with no influence on
  * meta_info (besides the psk field) *)
val receive_pretoken_update_smi_frame_lem (tk : premessage_token)
                                          (smi : meta_info) :
  Lemma(
    forall sk s e psk.
    let hsf1 = { smi.hsf with sk = sk; s = s; e = e; psk = psk } in
    let smi1 = { smi with hsf = hsf1 } in
    let smi2 = receive_pretoken_update_smi tk smi in
    receive_pretoken_update_smi tk smi1 ==
      { smi2 with hsf = { smi2.hsf with sk = sk; s = s; e = e; psk = psk }})

val receive_premessage_update_smi_frame_lem (pattern : list premessage_token)
                                            (smi : meta_info) :
  Lemma(
    forall sk s e psk.
    let hsf1 = { smi.hsf with sk = sk; s = s; e = e; psk = psk } in
    let smi1 = { smi with hsf = hsf1 } in
    let smi2 = receive_premessage_update_smi pattern smi in
    receive_premessage_update_smi pattern smi1 ==
      { smi2 with hsf = { smi2.hsf with sk = sk; s = s; e = e; psk = psk }})

val receive_token_update_smi_frame_lem (is_psk : bool) (tk : message_token)
                                       (smi : meta_info) :
  Lemma(
    forall s e psk.
    let hsf1 = { smi.hsf with s = s; e = e; psk = psk } in
    let smi1 = { smi with hsf = hsf1 } in
    let smi2 = receive_token_update_smi is_psk tk smi in
    receive_token_update_smi is_psk tk smi1 ==
      { smi2 with hsf = { smi2.hsf with s = s; e = e; psk = psk }})

val receive_message_update_smi_frame_lem (is_psk : bool)
                                         (pattern : list message_token)
                                         (smi : meta_info) :
  Lemma(
    forall s e psk.
    let hsf1 = { smi.hsf with s = s; e = e; psk = psk } in
    let smi1 = { smi with hsf = hsf1 } in
    let smi2 = receive_message_update_smi is_psk pattern smi in
    receive_message_update_smi is_psk pattern smi1 ==
      { smi2 with hsf = { smi2.hsf with s = s; e = e; psk = psk }})

val initialize_post_smi_psk_frame_lem (hsk : handshake_pattern)
                                      (ir : bool) :
  Lemma(initialize_post_smi hsk ir true ==
          smi_set_psk true (initialize_post_smi hsk ir false))

val csend_premessage_pre_smi_psk_frame_lem (hsk : handshake_pattern)
                                           (ir : bool) :
  Lemma(csend_premessage_pre_smi hsk ir true ==
          smi_set_psk true (csend_premessage_pre_smi hsk ir false))

val csend_premessage_ppost_smi_psk_frame_lem (hsk : handshake_pattern)
                                             (ir : bool) :
  Lemma(csend_premessage_ppost_smi hsk ir true ==
          smi_set_psk true (csend_premessage_ppost_smi hsk ir false))

val creceive_premessage_pre_smi_psk_frame_lem (hsk : handshake_pattern)
                                              (ir : bool) :
  Lemma(creceive_premessage_pre_smi hsk ir true ==
          smi_set_psk true (creceive_premessage_pre_smi hsk ir false))

val creceive_premessage_ppost_smi_psk_frame_lem (hsk : handshake_pattern)
                                                (ir : bool) :
  Lemma(creceive_premessage_ppost_smi hsk ir true ==
          smi_set_psk true (creceive_premessage_ppost_smi hsk ir false))

val cexchange_premessage_post_smi_psk_frame_lem (hsk : handshake_pattern)
                                                (ir : bool) :
  Lemma(cexchange_premessage_post_smi hsk ir true ==
          smi_set_psk true (cexchange_premessage_post_smi hsk ir false))

val crawl_messages_update_flags_frame_lem (is_psk : bool)
                                          (ssmi rsmi : meta_info)
                                          (msg : list message_token) :
  Lemma(
    forall ss rs se re spsk rpsk.
    let ssmi' = { ssmi with hsf = { ssmi.hsf with s = ss; e = se; psk = spsk } } in
    let rsmi' = { rsmi with hsf = { rsmi.hsf with s = rs; e = re; psk = rpsk } } in
    let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi rsmi in
    let ssmi1', rsmi1' = crawl_messages_update_smi is_psk msg ssmi' rsmi' in
    (* Note that we invert the sender and receiver *)
    ssmi1' == { ssmi1 with hsf = { ssmi1.hsf with s = rs; e = re; psk = rpsk } } /\
    rsmi1' == { rsmi1 with hsf = { rsmi1.hsf with s = ss; e = se; psk = spsk } })

val handshake_messages_pre_smi_psk_frame_lem (is_psk ir : bool)
                                             (ssmi rsmi : meta_info)
                                             (messages : list (list message_token))
                                             (i : nat{i <= List.length messages}) :
  Lemma
  (ensures (
    let ssmi' = smi_set_psk true ssmi  in
    let rsmi' = smi_set_psk true rsmi in
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
    let ssmi1', rsmi1' = handshake_messages_pre_smi is_psk ir ssmi' rsmi' messages i in
    ssmi1' == smi_set_psk true ssmi1 /\ rsmi1' == smi_set_psk true rsmi1))
  (decreases i)

val handshake_pattern_smi_psk_frame_lem (hsk : handshake_pattern)
                                        (i : nat{i <= List.length hsk.messages}) :
  Lemma(
    let ssmi1, rsmi1 = handshake_pattern_smi hsk true i in
    let ssmi1', rsmi1' = handshake_pattern_smi hsk false i in
    ssmi1 == smi_set_psk true ssmi1' /\ rsmi1 == smi_set_psk true rsmi1')

val csend_creceive_message_pre_smi_psk_frame_lem (hsk : handshake_pattern)
                                                 (i : nat{i <= List.length hsk.messages}) :
  Lemma(
    csend_message_pre_smi hsk true i ==
      smi_set_psk true (csend_message_pre_smi hsk false i) /\
    creceive_message_pre_smi hsk true i ==
      smi_set_psk true (creceive_message_pre_smi hsk false i))

val csend_creceive_message_post_smi_psk_frame_lem (hsk : handshake_pattern)
                                                  (i : nat{i < List.length hsk.messages}) :
  Lemma(
    csend_message_post_smi hsk true i ==
      smi_set_psk true (csend_message_post_smi hsk false i) /\
    creceive_message_post_smi hsk true i ==
      smi_set_psk true (creceive_message_post_smi hsk false i))

(**** PSK flag equality lemmas *)
val send_receive_message_update_smi_same_sk_lem
  (is_psk : bool)
  (ssmi rsmi : meta_info)
  (msg : list message_token) :
  Lemma
  (requires (ssmi.hsf.sk == rsmi.hsf.sk))
  (ensures(
   let ssmi1 = send_message_update_smi is_psk msg ssmi in
   let rsmi1 = receive_message_update_smi is_psk msg rsmi in
   ssmi1.hsf.sk == rsmi1.hsf.sk))

val crawl_messages_update_flags_same_sk_lem
  (is_psk : bool)
  (ssmi rsmi : meta_info)
  (msg : list message_token) :
  Lemma
  (requires (ssmi.hsf.sk == rsmi.hsf.sk))
  (ensures(
   let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi rsmi in
   ssmi1.hsf.sk == rsmi1.hsf.sk))

val handshake_messages_pre_smi_same_sk_lem
  (is_psk ir : bool)
  (ssmi rsmi : meta_info)
  (messages : list (list message_token))
  (i : nat{i <= List.length messages}) :
  Lemma
  (requires (ssmi.hsf.sk == rsmi.hsf.sk))
  (ensures(
   let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
   ssmi1.hsf.sk == rsmi1.hsf.sk))
  (decreases messages)

val csend_creceive_message_pre_smi_same_sk_lem
  (hsk : handshake_pattern)
  (i : nat{i < List.length hsk.messages})
  (has_psk : bool) :
  Lemma(
    (csend_message_pre_smi hsk has_psk i).hsf.sk ==
      (creceive_message_pre_smi hsk has_psk i).hsf.sk)

