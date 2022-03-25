module Spec.Noise.MetaInfo
open FStar.Mul

open Spec.Noise.Base
open Spec.Noise.HandshakeFlags
open Spec.Noise.NonceCounter

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

(*** Crawlers *)
(**** Compute over whole pattern *)
#push-options "--fuel 2 --ifuel 2"
let rec crawl_handshake_messages_step_lem (a : Type)
                                          (crawler : handshake_messages_crawler a)
                                          (acc0 : a)
                                          (is_psk ir : bool)
                                          (ssmi rsmi : meta_info)
                                          (messages : list (list message_token))
                                          (i : nat{i < List.length messages}) =
  match messages with
  | [] -> ()
  | msg1 :: messages' ->
    if i = 0 then () else
    let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg1 ssmi rsmi in
    let acc1 = crawler is_psk ir ssmi rsmi ssmi1 rsmi1 msg1 acc0 in
    let ir' = not ir in
    crawl_handshake_messages_step_lem a crawler acc1 is_psk ir' ssmi1 rsmi1 messages' (i-1)
#pop-options

let handshake_messages_pre_smi_step_lem (is_psk ir : bool)
                                        (ssmi rsmi : meta_info)
                                        (messages : list (list message_token))
                                        (i : nat{i < List.length messages}) =
  let a = meta_info & meta_info in
  let crawler : handshake_messages_crawler a =
    (fun is_psk ir ssmi0 rsmi0 ssmi1 rsmi1 msg acc ->
      ((ssmi1 <: meta_info), (rsmi1 <: meta_info))) in
  let acc0 : a = ssmi, rsmi in
  crawl_handshake_messages_step_lem a crawler acc0 is_psk ir ssmi rsmi messages i

let handshake_pattern_smi_step_lem (hsk : handshake_pattern) (set_psk : bool)
                                   (i : nat{i < List.length hsk.messages}) =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk set_psk in
  handshake_messages_pre_smi_step_lem is_psk true ismi rsmi hsk.messages i

#push-options "--fuel 1"
let rec crawl_handshake_messages_pred_lem (a : Type)
                                          (crawler : handshake_messages_crawler a)
                                          (p : a -> prop)
                                          (acc : a)
                                          (is_psk ir : bool)
                                          (send_smi recv_smi : meta_info)
                                          (messages : list (list message_token)) =
  match messages with
  | [] -> ()
  | msg :: messages' ->
    let send_smi1, recv_smi1 = crawl_messages_update_smi is_psk msg send_smi recv_smi in
    let acc1 = crawler is_psk ir send_smi recv_smi send_smi1 recv_smi1 msg acc in
    crawl_handshake_messages_pred_lem a crawler p acc1 is_psk (not ir)
                                      send_smi1 recv_smi1 messages'
#pop-options

#push-options "--fuel 3 --ifuel 3"
let rec forallb_handshake_messages_and_lem (checker : handshake_messages_crawl_checker)
                                           (b0 : bool)
                                           (is_psk ir : bool)
                                           (ssmi rsmi : meta_info)
                                           (msg : list message_token)
                                           (messages : list (list message_token)) =
  match messages with
  | [] -> ()
  | [msg1] -> ()
  | msg1 :: messages1 ->
    let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi rsmi in
    let ir1 = not ir in
    let b1 = b0 && (checker is_psk ir ssmi rsmi ssmi1 rsmi1 msg) in
    forallb_handshake_messages_and_lem checker b1 is_psk ir1 ssmi1 rsmi1 msg1 messages1
#pop-options

#push-options "--z3rlimit 25 --fuel 3 --ifuel 3"
let rec existsb_handshake_messages_or_lem (checker : handshake_messages_crawl_checker)
                                          (b0 : bool)
                                          (is_psk ir : bool)
                                          (ssmi rsmi : meta_info)
                                          (msg : list message_token)
                                          (messages : list (list message_token)) =
  match messages with
  | [] -> ()
  | [msg1] -> ()
  | msg1 :: messages1 ->
    let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi rsmi in
    let ir1 = not ir in
    let b1 = b0 || (checker is_psk ir ssmi rsmi ssmi1 rsmi1 msg) in
    existsb_handshake_messages_or_lem checker b1 is_psk ir1 ssmi1 rsmi1 msg1 messages1
#pop-options

val forall_shift_nat_boundaries_lem (n : nat) (p : (x:nat{x < n}) -> prop) :
  Lemma ((forall (i : nat{i < n - 1}). p (i+1)) <==> (forall (j : nat{0 < j /\ j < n}). p j))

let forall_shift_nat_boundaries_lem (n : nat) (p : (x:nat{x < n}) -> prop) =
  let pi = forall (i : nat{i < n - 1}). p (i+1) in
  let pj = forall (j : nat{0 < j /\ j < n}). p j in
  (* The prove can easily prove the first implication *)
  assert(pj ==> pi);
  (* For the other, we use some trick to help Z3 instantiate the hypotheses *)
  let pj' = forall (j : nat{0 < j /\ j < n}). p ((j-1)+1) in
  assert(pi ==> pj');
  ()

val exists_shift_nat_boundaries_lem (n : nat) (p : (x:nat{x < n}) -> prop) :
  Lemma ((exists (i : nat{i < n - 1}). p (i+1)) <==> (exists (j : nat{0 < j /\ j < n}). p j))

let exists_shift_nat_boundaries_lem (n : nat) (p : (x:nat{x < n}) -> prop) =
  let pi = exists (i : nat{i < n - 1}). p (i+1) in
  let pj = exists (j : nat{0 < j /\ j < n}). p j in
  assert(pi ==> pj);
  (* Same as above *)
  let pj' = exists (j : nat{0 < j /\ j < n}). p ((j-1)+1) in
  assert(pi ==> pj');
  assert(pj' <==> pj);
  assert(pj' ==> pi);
  ()

let exists_join_nat_boundaries_lem (n : nat{n > 0}) (p : (x:nat{x < n}) -> prop) :
  Lemma (((p 0) \/ (exists (j : nat{0 < j /\ j < n}). p j)) <==>
        ((exists (j : nat{j < n}). p j))) = ()

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let rec forallb_handshake_messages_lem (checker : handshake_messages_crawl_checker)
                                       (is_psk ir : bool)
                                       (ssmi rsmi : meta_info)
                                       (messages : list (list message_token)) =
  match messages with
  | [] -> ()
  | msg1 :: messages1 ->
    let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg1 ssmi rsmi in
    let ir1 = not ir in
    forallb_handshake_messages_and_lem checker true is_psk ir ssmi rsmi msg1 messages1;
    forallb_handshake_messages_lem checker is_psk ir1 ssmi1 rsmi1 messages1;
    (* We still need to do a bit of work *)
    let b0 = forallb_handshake_messages checker is_psk ir ssmi rsmi (msg1 :: messages1) in
    let b1 = true && (checker is_psk ir ssmi rsmi ssmi1 rsmi1 msg1) in
    let b2 = forallb_handshake_messages checker is_psk ir1 ssmi1 rsmi1 messages1 in
    (* Check that we get what we were supposed to *)
    assert(b0 = (b1 && b2));
    (* Some asserts to check some equalities *)
    assert(forall (i : nat{i < List.length messages1}).
           List.Tot.index messages1 i == List.Tot.index messages (i+1));
    assert(forall (i : nat{i < List.length messages1}).
      handshake_messages_pre_smi is_psk ir ssmi1 rsmi1 messages1 i ==
      handshake_messages_pre_smi is_psk ir1 ssmi rsmi messages (i+1));
    assert(b2 <==>
      (forall (i : nat{i < List.length messages1}).
      checkerb_handshake_messages_one checker is_psk ir1 ssmi1 rsmi1 messages1 i));
    assert(
      (forall (i : nat{i < List.length messages1}).
      checkerb_handshake_messages_one checker is_psk ir1 ssmi1 rsmi1 messages1 i =
      checkerb_handshake_messages_one checker is_psk ir ssmi rsmi messages (i + 1)));
    assert(b1 <==>
      checkerb_handshake_messages_one checker is_psk ir ssmi rsmi messages 0);
    (* Here is the trick: we can prove that:
       [> b <==> forall i < (length messages)-1. P (i+1)
       But F* and Z3 don't manage to deduce from it:
       [> b <==> forall 0 < i < length messages. P i
       So we need to call a lemma *)
    let n = List.length messages in
    let p i : prop =
      checkerb_handshake_messages_one checker is_psk ir ssmi rsmi messages i == true in
    forall_shift_nat_boundaries_lem n p
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let rec existsb_handshake_messages_lem (checker : handshake_messages_crawl_checker)
                                       (is_psk ir : bool)
                                       (ssmi rsmi : meta_info)
                                       (messages : list (list message_token)) =
  match messages with
  | [] -> ()
  | msg1 :: messages1 ->
    let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg1 ssmi rsmi in
    let ir1 = not ir in
    existsb_handshake_messages_or_lem checker false is_psk ir ssmi rsmi msg1 messages1;
    existsb_handshake_messages_lem checker is_psk ir1 ssmi1 rsmi1 messages1;
    (* We still need to do a bit of work *)
    let b0 = existsb_handshake_messages checker is_psk ir ssmi rsmi (msg1 :: messages1) in
    let b1 = false || (checker is_psk ir ssmi rsmi ssmi1 rsmi1 msg1) in
    let b2 = existsb_handshake_messages checker is_psk ir1 ssmi1 rsmi1 messages1 in
    (* Check that we get what we were supposed to *)
    assert(b0 = (b1 || b2));
    (* Some asserts to check some equalities *)
    assert(forall (i : nat{i < List.length messages1}).
           List.Tot.index messages1 i == List.Tot.index messages (i+1));
    assert(forall (i : nat{i < List.length messages1}).
      handshake_messages_pre_smi is_psk ir ssmi1 rsmi1 messages1 i ==
      handshake_messages_pre_smi is_psk ir1 ssmi rsmi messages (i+1));
    assert(b2 <==>
      (exists (i : nat{i < List.length messages1}).
      checkerb_handshake_messages_one checker is_psk ir1 ssmi1 rsmi1 messages1 i));
    assert(
      (forall (i : nat{i < List.length messages1}).
      checkerb_handshake_messages_one checker is_psk ir1 ssmi1 rsmi1 messages1 i =
      checkerb_handshake_messages_one checker is_psk ir ssmi rsmi messages (i + 1)));
    (* Same thing as for the previous lemma: the prover doesn't manage to shift
     * the boundaries. *)
    let n = List.length messages in
    let p i : prop =
      checkerb_handshake_messages_one checker is_psk ir ssmi rsmi messages i == true in
    let pi = (exists (i : nat{i < List.length messages1}). p (i+1)) in
    let pj = (exists (j : nat{0 < j /\ j < List.length messages}). p j) in    
    exists_shift_nat_boundaries_lem n p;
    assert(pi <==> pj);
    (* Even now, we still need a bit of work *)
    exists_join_nat_boundaries_lem n p    
#pop-options

let forallb_handshake_pattern_messages_lem (hsk : handshake_pattern)
                                           (set_psk : bool)
                                           (checker : handshake_messages_crawl_checker) =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk set_psk in
  forallb_handshake_messages_lem checker is_psk true ismi rsmi hsk.messages

(** Monotonicity *)
#push-options "--fuel 1"
let rec handshake_messages_pre_smi_is_greater_than_input is_psk ir ssmi0 rsmi0 messages i =
  if i = 0 then ()
  else
    match messages with
    | [] -> ()
    | msg :: messages' ->
      let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi0 rsmi0 in
      handshake_messages_pre_smi_is_greater_than_input is_psk (not ir) ssmi1 rsmi1 messages' (i-1)
#pop-options

#push-options "--fuel 1"
let rec handshake_messages_pre_smi_is_increasing is_psk ir ssmi0 rsmi0 messages i j =
  if i = j then ()
  else if i = 0 then handshake_messages_pre_smi_is_greater_than_input is_psk ir ssmi0 rsmi0 messages j
  else
    match messages with
    | [] -> ()
    | msg :: messages' ->
      let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg ssmi0 rsmi0 in
      handshake_messages_pre_smi_is_increasing is_psk (not ir) ssmi1 rsmi1 messages' (i-1) (j-1)
#pop-options    

let handshake_pattern_smi_is_increasing hsk set_psk i j =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk set_psk in
  handshake_messages_pre_smi_is_increasing is_psk true ismi rsmi hsk.messages i j


(*** Handshake functions flags *)
(**** Messages *)
(***** Consistency lemmas *)

let csend_receive_message_pre_post_smi_consistent_lem
  (hsk : handshake_pattern)
  (set_psk : bool)
  (i : nat{0 < i /\ i < List.length hsk.messages}) = ()

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
let csend_creceive_cexchange_smi_consistent_lem
  (hsk : handshake_pattern{
    (match hsk.premessage_ir with | Some pre -> List.length pre <= 2| None -> True) /\
    (match hsk.premessage_ri with | Some pre -> List.length pre <= 2 | None -> True)})
  (has_psk : bool) = ()
#pop-options

(**** Decomposition lemma *)
let receive_tokens_update_smi_decompose_lem is_psk tokens1 tokens2 smi =
  receive_tokens_update_hsf_decompose_lem is_psk tokens1 tokens2 smi.hsf;
  tokens_update_nonce_decompose_lem smi.hsf.sk is_psk tokens1 tokens2 smi.nonce;
  updt_sk_consistent_with_receive_tokens_update_smi is_psk tokens1 smi

(**** Frame lemmas *)

let receive_pretoken_update_smi_frame_lem (tk : premessage_token)
                                          (smi : meta_info) =
  receive_pretoken_update_hsf_frame_lem tk smi.hsf

let receive_premessage_update_smi_frame_lem (pattern : list premessage_token)
                                            (smi : meta_info) =
  receive_premessage_update_hsf_frame_lem pattern smi.hsf

let receive_token_update_smi_frame_lem (is_psk : bool) (tk : message_token)
                                       (smi : meta_info) =
  receive_token_update_hsf_frame_lem is_psk tk smi.hsf

let receive_message_update_smi_frame_lem (is_psk : bool)
                                         (pattern : list message_token)
                                         (smi : meta_info) =
  receive_tokens_update_hsf_frame_lem is_psk pattern smi.hsf

let initialize_post_smi_psk_frame_lem (hsk : handshake_pattern)
                                      (ir : bool) = ()

let csend_premessage_pre_smi_psk_frame_lem (hsk : handshake_pattern)
                                           (ir : bool) =
  let smi0 = initialize_post_smi hsk ir false in
  let pre_ir = opt_list_to_list_or_empty hsk.premessage_ir in
  initialize_post_smi_psk_frame_lem hsk ir;
  receive_premessage_update_smi_frame_lem pre_ir smi0

let csend_premessage_ppost_smi_psk_frame_lem (hsk : handshake_pattern)
                                             (ir : bool) =
  csend_premessage_pre_smi_psk_frame_lem hsk ir

let creceive_premessage_pre_smi_psk_frame_lem (hsk : handshake_pattern)
                                              (ir : bool) =
  initialize_post_smi_psk_frame_lem hsk ir;
  csend_premessage_pre_smi_psk_frame_lem hsk ir

let creceive_premessage_ppost_smi_psk_frame_lem (hsk : handshake_pattern)
                                                (ir : bool) =
  let smi0 = creceive_premessage_pre_smi hsk ir false in
  let opt_pre = if ir then hsk.premessage_ir else hsk.premessage_ri in
  let pre = opt_list_to_list_or_empty opt_pre in
  creceive_premessage_pre_smi_psk_frame_lem hsk ir;
  receive_premessage_update_smi_frame_lem pre smi0

let cexchange_premessage_post_smi_psk_frame_lem (hsk : handshake_pattern)
                                                (ir : bool) =
  creceive_premessage_ppost_smi_psk_frame_lem hsk true;
  creceive_premessage_ppost_smi_psk_frame_lem hsk false;
  csend_premessage_ppost_smi_psk_frame_lem hsk true;
  csend_premessage_ppost_smi_psk_frame_lem hsk false

let crawl_messages_update_flags_frame_lem (is_psk : bool)
                                          (ssmi rsmi : meta_info)
                                          (msg : list message_token) =
  receive_message_update_smi_frame_lem is_psk msg rsmi

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let rec handshake_messages_pre_smi_psk_frame_lem (is_psk ir : bool)
                                                 (ssmi rsmi : meta_info)
                                                 (messages : list (list message_token))
                                                 (i : nat{i <= List.length messages}) =
  let ssmi' = smi_set_psk true ssmi  in
  let rsmi' = smi_set_psk true rsmi in
  match messages with
  | [] ->
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
    let ssmi1', rsmi1' = handshake_messages_pre_smi is_psk ir ssmi' rsmi' messages i in
    assert(ssmi1 == ssmi /\ rsmi1 == rsmi /\ ssmi1' == ssmi' /\ rsmi1' == rsmi')
  | msg1 :: messages1 ->
    if i = 0 then () else
    begin
    crawl_messages_update_flags_frame_lem is_psk ssmi rsmi msg1;    
    (* All steps at once *)
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
    let ssmi1', rsmi1' = handshake_messages_pre_smi is_psk ir ssmi' rsmi' messages i in
    (* Split at step one *)
    (* First step *)
    let ssmi2, rsmi2 = crawl_messages_update_smi is_psk msg1 ssmi rsmi in
    let ssmi2', rsmi2' = crawl_messages_update_smi is_psk msg1 ssmi' rsmi' in
    handshake_messages_pre_smi_psk_frame_lem is_psk (not ir) ssmi2 rsmi2 messages1 (i-1);
    (* Remaining steps *)
    let ssmi3, rsmi3 = handshake_messages_pre_smi is_psk (not ir) ssmi2 rsmi2 messages1 (i-1) in
    let ssmi3', rsmi3' = handshake_messages_pre_smi is_psk (not ir) ssmi2' rsmi2' messages1 (i-1) in
    assert(ssmi3 == ssmi1 /\ rsmi3 == rsmi1 /\ ssmi3' == ssmi1' /\ rsmi3' == rsmi1');
    assert(ssmi2' == smi_set_psk true ssmi2 /\ rsmi2' == smi_set_psk true rsmi2);
    assert(ssmi3' == smi_set_psk true ssmi3 /\ rsmi3' == smi_set_psk true rsmi3)
    end
#pop-options

let handshake_pattern_smi_psk_frame_lem (hsk : handshake_pattern)
                                        (i : nat{i <= List.length hsk.messages}) =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk false in
  handshake_messages_pre_smi_psk_frame_lem is_psk true ismi rsmi hsk.messages i

let csend_creceive_message_pre_smi_psk_frame_lem (hsk : handshake_pattern)
                                                 (i : nat{i <= List.length hsk.messages}) =
  handshake_pattern_smi_psk_frame_lem hsk i

let csend_creceive_message_post_smi_psk_frame_lem (hsk : handshake_pattern)
                                                  (i : nat{i < List.length hsk.messages}) =
  csend_creceive_message_pre_smi_psk_frame_lem hsk (i+1)

(**** PSK flag equality lemmas *)
let send_receive_message_update_smi_same_sk_lem
  (is_psk : bool)
  (ssmi rsmi : meta_info)
  (msg : list message_token) =
  send_receive_tokens_update_hsf_same_sk_lem is_psk ssmi.hsf rsmi.hsf msg

let crawl_messages_update_flags_same_sk_lem
  (is_psk : bool)
  (ssmi rsmi : meta_info)
  (msg : list message_token) =
  send_receive_message_update_smi_same_sk_lem is_psk ssmi rsmi msg 

#push-options "--fuel 1"
let rec handshake_messages_pre_smi_same_sk_lem
  (is_psk ir : bool)
  (ssmi rsmi : meta_info)
  (messages : list (list message_token))
  (i : nat{i <= List.length messages}) =
 match messages with
 | [] -> ()
 | msg1 :: messages1 ->
   if i = 0 then () else
   begin
   let ssmi1, rsmi1 = crawl_messages_update_smi is_psk msg1 ssmi rsmi in
   crawl_messages_update_flags_same_sk_lem is_psk ssmi rsmi msg1;
   handshake_messages_pre_smi_same_sk_lem is_psk (not ir) ssmi1 rsmi1 messages1 (i-1)
   end
#pop-options

let csend_creceive_message_pre_smi_same_sk_lem
  (hsk : handshake_pattern)
  (i : nat{i < List.length hsk.messages})
  (has_psk : bool) =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk has_psk in
  assert(ismi.hsf.sk == false /\ rsmi.hsf.sk == false);
  handshake_messages_pre_smi_same_sk_lem is_psk true ismi rsmi hsk.messages i

(**** Local key stability *)
// TODO
(*val handshake_messages_pre_smi_stable_local_keys (is_psk ir : bool)
                                                 (ssmi0 rsmi0 : meta_info)
                                                 (messages : list (list message_token))
                                                 (i : nat{i < List.length messages}) :
  Lemma(
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi0 rsmi0 messages i in
    let ssmi2, rsmi2 = if i % 2 = 0 then ssmi1, rsmi1 else rsmi1, ssmi1 in
    ssmi2.hsf.s = ssmi0.hsf.s /\ ssmi2.hsf.e = ssmi2.hsf.e /\ ssmi2.hsf.psk = ssmi0.hsf.psk /\
    rsmi2.hsf.s = rsmi0.hsf.s /\ rsmi2.hsf.e = rsmi2.hsf.e /\ rsmi2.hsf.psk = rsmi0.hsf.psk)*)

(*

val hskf_preserved_by_smi ir hskf0 ssmi0 rsmi0 msgs :
  (ensures
    let hskf1 = compute_hsk_msgs_flags hskf0 msgs in
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi0 rsmi0 messages i in
    hskf_locally_compatible_with_smi ir hskf0 ssmi1 /\
    hskf_locally_compatible_with_smi (not ir) hskf0 rsmi1


val handshake_messages_pre_smi_step_lem (is_psk ir : bool)
                                        (ssmi rsmi : meta_info)
                                        (messages : list (list message_token))
                                        (i : nat{i < List.length messages}) :
  Lemma(
    let ssmi1, rsmi1 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages i in
    let ssmi2, rsmi2 = handshake_messages_pre_smi is_psk ir ssmi rsmi messages (i+1) in
    let msg = List.Tot.index messages i in
    (ssmi2, rsmi2) == crawl_messages_update_smi is_psk msg ssmi1 rsmi1)


let handshake_pattern_smi (hsk : handshake_pattern) (set_psk : bool)
                          (i : nat{i <= List.length hsk.messages}) :
  meta_info & meta_info =
  let ismi, rsmi, is_psk = compute_premessages_post_smi hsk set_psk in
  handshake_messages_pre_smi is_psk true ismi rsmi hsk.messages i
*)
