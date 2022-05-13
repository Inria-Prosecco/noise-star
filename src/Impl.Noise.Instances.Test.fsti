module Impl.Noise.Instances.Test

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Sequence
module S = Lib.Sequence

module BS = Lib.ByteSequence
open Lib.Buffer
open LowStar.BufferOps

open Spec.Noise
module Spec = Spec.Noise.Instances
open Impl.Noise.Types
open Impl.Noise.FlatStructures
open Impl.Noise.PatternMessages
open Impl.Noise.Instances

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(* Align the .fst and the .fsti *)
private val _align_beg : unit

(*** IKpsk2 *)
(**** Handshake test *)
#push-options "--z3rlimit 50 --ifuel 1"
[@@ noextract_to "Karamel"] noextract
let perform_IKpsk2_handshake (is ie rs re : keypair Spec.wgc)
                             (psk : preshared_key)
                             (ts : Spec.timestamp) :
  Tot (option ((handshake_state Spec.wgc) & (handshake_state Spec.wgc))) =
  (* Initialize *)
  let pist = Spec.initialize_IKpsk2 Spec.protocol_IKpsk2_prologue is ie in
  let prst = Spec.initialize_IKpsk2 Spec.protocol_IKpsk2_prologue rs re in
  (* Exchange the premessage *)
  let prres = Spec.send_premessage_IKpsk2 prst in
  match prres with
  | Fail e -> None
  | Res (pmsg, rst0) ->
    if S.length pmsg > max_size_t then None else
    let pires = Spec.receive_premessage_IKpsk2 pmsg pist in
    match pires with
    | Fail e -> None
    | Res ist0 ->
    (* Create initiation *)
    match Spec.create_initiation_IKpsk2 ts ist0 with
    | Fail e  -> None
    | Res (msg, ist1) ->
      (* Consume initiation *)
      if S.length msg > max_size_t then None else
      match Spec.consume_initiation_IKpsk2 msg rst0 with
      | Fail e -> None
      | Res (ts', rst1) ->
        (* Set the preshared keys before the response message *)
        let ist1 = Spec.Noise.Base.set_psk psk ist1 in
        let rst1 = Spec.Noise.Base.set_psk psk rst1 in
        (* Create response *)
        match Spec.create_response_IKpsk2 rst1 with
        | Fail e -> None
        | Res (response, rst2) ->
          (* Consume response *)
          if S.length response > max_size_t then None else
          match Spec.consume_response_IKpsk2 response ist1 with
          | Fail e -> None
          | Res (eps, ist2) ->
            if S.length eps > 0 then None else
            Some (ist2, rst2)
#pop-options

[@@ noextract_to "Karamel"]
inline_for_extraction noextract
let timestamp_vsv = Spec.timestamp_size
let timestamp_vs = size timestamp_vsv
type timestamp_t = lbuffer uint8 timestamp_vs

[@@ noextract_to "Karamel"] noextract
let cperform_IKpsk2_handshake_init_pre_pre
  (pname : hashable_t wg_inc 37ul) (prologue : hashable_t wg_inc 34ul)
  (is ie rs re : keypair_t wg_inc)
  (ist rst : handshake_state_t wg_inc)
  (h : mem) =
  live h pname /\ live h prologue /\
  live h is /\ live h ie /\ live h rs /\ live h re /\
  live h ist /\ live h rst /\
  disjoint ist is /\ disjoint ist ie /\ disjoint ist rs /\ disjoint ist re /\
  disjoint ist pname /\ disjoint ist prologue /\
  disjoint rst is /\ disjoint rst ie /\ disjoint rst rs /\ disjoint rst re /\
  disjoint rst pname /\ disjoint rst prologue /\
  disjoint ist rst /\
  h.[|pname|] `S.equal` Spec.protocol_IKpsk2_name /\
  h.[|prologue|] `S.equal` Spec.protocol_IKpsk2_prologue /\
  h.[|ist|] `S.equal` (S.create (handshake_state_vsv wg_inc) (u8 0)) /\
  h.[|rst|] `S.equal` (S.create (handshake_state_vsv wg_inc) (u8 0))

[@@ noextract_to "Karamel"] noextract
let cperform_IKpsk2_handshake_initiation_pre
  (ts : timestamp_t)
  (ist rst : handshake_state_t wg_inc)
  (h : mem) =
  live h ts /\
  live h ist /\ live h rst /\
  disjoint ist ts /\ 
  disjoint rst ts /\
  disjoint ist rst

[@@ noextract_to "Karamel"] noextract
val cperform_IKpsk2_handshake
  (pname : hashable_t wg_inc 37ul) (prologue : hashable_t wg_inc 34ul)
  (is ie rs re : keypair_t wg_inc)
  (psk : preshared_key_t)
  (ts : timestamp_t)
  (ist rst : handshake_state_t wg_inc) :
  Stack (rtype (prim_error_code_return_type))
  (requires (fun h ->
   (* initialization, premessage *)  
   cperform_IKpsk2_handshake_init_pre_pre pname prologue is ie rs re ist rst h /\
   (* initiation, response *)
   cperform_IKpsk2_handshake_initiation_pre ts ist rst h /\
   (* set psk *)
   live h psk /\ live h ist /\ live h rst /\
   disjoint ist rst /\ disjoint ist psk /\ disjoint rst psk))
  (ensures (fun h0 r1 h1 ->
   modifies2 ist rst h0 h1 /\
   begin
   let ts_v = h0.[|ts|] in
   let psk_v = h0.[|psk|] in
   let is_v = eval_keypair h0 is in
   let ie_v = eval_keypair h0 ie in
   let rs_v = eval_keypair h0 rs in
   let re_v = eval_keypair h0 re in
   (**)
   let ismi = creceive_message_post_smi Spec.pattern_IKpsk2 true 1 in
   let rsmi = csend_message_post_smi Spec.pattern_IKpsk2 true 1 in
   (**)
   let ist1_v = eval_handshake_state h1 ist ismi in
   let rst1_v = eval_handshake_state h1 rst rsmi in
   let r1_v = perform_IKpsk2_handshake is_v ie_v rs_v re_v psk_v ts_v in
   match is_success r1, r1_v with
   | false, None -> True
   | true, Some (ist1'_v, rst1'_v) ->
     ist1'_v == ist1_v /\ rst1'_v == rst1_v
   | _ -> False
   end))
