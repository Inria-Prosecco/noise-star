module Impl.Noise.Instances.Test

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
module HST = FStar.HyperStack.ST

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

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(* Align the .fst and the .fsti *)
let _align_beg = ()

(*** IKpsk2 *)
(**** Handshake test *)
[@@ noextract_to "krml"] noextract
let perform_IKpsk2_handshake_init_pre_ (is ie rs re : keypair Spec.wgc) :
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
      Some (ist0, rst0)

[@@ noextract_to "krml"] noextract
let perform_IKpsk2_handshake_initiation_ (ist rst : handshake_state Spec.wgc)
                                         (ts : Spec.timestamp) :
  Tot (option ((handshake_state Spec.wgc) & (handshake_state Spec.wgc))) =
  (* Create initiation *)
  match Spec.create_initiation_IKpsk2 ts ist with
  | Fail e  -> None
  | Res (msg, ist1) ->
    (* Consume initiation *)
    if S.length msg > max_size_t then None else
    match Spec.consume_initiation_IKpsk2 msg rst with
    | Fail e -> None
    | Res (ts', rst1) ->
      Some(ist1, rst1)

[@@ noextract_to "krml"] noextract
let perform_IKpsk2_handshake_response_ (ist rst : handshake_state Spec.wgc) :
  Tot (option ((handshake_state Spec.wgc) & (handshake_state Spec.wgc))) =
  (* Create response *)
  match Spec.create_response_IKpsk2 rst with
  | Fail e  -> None
  | Res (msg, rst1) ->
    (* Consume response *)
    if S.length msg > max_size_t then None else
    match Spec.consume_response_IKpsk2 msg ist with
    | Fail e -> None
    | Res (eps, ist1) ->
      if S.length eps > 0 then None else
      Some(ist1, rst1)

[@@ noextract_to "krml"] noextract
let perform_IKpsk2_handshake_decomposed_
  (is ie rs re : keypair Spec.wgc)
  (psk : preshared_key)
  (ts : Spec.timestamp) :
  Tot (option ((handshake_state Spec.wgc) & (handshake_state Spec.wgc))) =
  match perform_IKpsk2_handshake_init_pre_ is ie rs re with
  | None -> None
  | Some (ist1, rst1) ->
    match perform_IKpsk2_handshake_initiation_ ist1 rst1 ts with
    | None -> None
    | Some (ist2, rst2) ->
      let ist3 = Spec.Noise.Base.set_psk psk ist2 in
      let rst3 = Spec.Noise.Base.set_psk psk rst2 in
      perform_IKpsk2_handshake_response_ ist3 rst3

let perform_IKpsk2_handshake_decompose_lem
  (is ie rs re : keypair Spec.wgc)
  (psk : preshared_key)
  (ts : Spec.timestamp) :
  Lemma(
    perform_IKpsk2_handshake is ie rs re psk ts ==
    perform_IKpsk2_handshake_decomposed_ is ie rs re psk ts)
  = ()

[@@ noextract_to "krml"] inline_for_extraction noextract
let premessage_IKpsk2_len : n:size_nat{n > 0} =
  assert_norm(premessage_vsv wg_inc Spec.pattern_IKpsk2 false > 0);
  premessage_vsv wg_inc Spec.pattern_IKpsk2 false

[@@ noextract_to "krml"] inline_for_extraction noextract
let initiation_IKpsk2_len :
  n:size_nat{n == pat_message_vsv wg_inc Spec.pattern_IKpsk2 12 0 /\ n > 0}
  =
  assert_norm(pat_message_vsv wg_inc Spec.pattern_IKpsk2 12 0 <= max_size_t);
  assert_norm(pat_message_vsv wg_inc Spec.pattern_IKpsk2 12 0 > 0);
  pat_message_vsv wg_inc Spec.pattern_IKpsk2 12 0

[@@ noextract_to "krml"] inline_for_extraction noextract
let response_IKpsk2_len :
  n:size_nat{n == pat_message_vsv wg_inc Spec.pattern_IKpsk2 0 1 /\ n > 0}
  =
  assert_norm(pat_message_vsv wg_inc Spec.pattern_IKpsk2 0 1 <= max_size_t);
  assert_norm(pat_message_vsv wg_inc Spec.pattern_IKpsk2 0 1 > 0);
  pat_message_vsv wg_inc Spec.pattern_IKpsk2 0 1

(** initialize and exchange premessages *)
[@@ noextract_to "krml"] noextract
let cperform_IKpsk2_handshake_init_pre_post
  (pname : hashable_t wg_inc 37ul) (prologue : hashable_t wg_inc 34ul)
  (is ie rs re : keypair_t wg_inc)
  (ist rst : handshake_state_t wg_inc)
  (h0 : mem) (r : unit) (h1 : mem) =
  let is_v = eval_keypair h0 is in
  let ie_v = eval_keypair h0 ie in
  let rs_v = eval_keypair h0 rs in
  let re_v = eval_keypair h0 re in
  (**)
  let ismi = csend_message_pre_smi Spec.pattern_IKpsk2 false 0 in
  let rsmi = creceive_message_pre_smi Spec.pattern_IKpsk2 false 0 in
  (**)
  let ist_v1 = eval_handshake_state h1 ist ismi in
  let rst_v1 = eval_handshake_state h1 rst rsmi in
  let r_v1 = perform_IKpsk2_handshake_init_pre_ is_v ie_v rs_v re_v in
  match r_v1 with
  | None -> False
  | Some (ist_v1', rst_v1') ->
    rst_v1' == rst_v1 /\ ist_v1' == ist_v1

[@@ noextract_to "krml"] noextract
let cperform_IKpsk2_handshake_init_pre_post_lem
  (pname : hashable_t wg_inc 37ul) (prologue : hashable_t wg_inc 34ul)
  (is ie rs re : keypair_t wg_inc)
  (ist rst : handshake_state_t wg_inc)
  (h0 h1 h2 h3 : mem) :
  Lemma
  (requires (
    h1.[|is|] `S.equal` h0.[|is|] /\
    h1.[|ie|] `S.equal` h0.[|ie|] /\
    h1.[|rs|] `S.equal` h0.[|rs|] /\
    h1.[|re|] `S.equal` h0.[|re|] /\
    h3.[|ist|] `S.equal` h2.[|ist|] /\
    h3.[|rst|] `S.equal` h2.[|rst|] /\
    cperform_IKpsk2_handshake_init_pre_post pname prologue is ie rs re ist rst h1 () h2))
  (ensures (
        cperform_IKpsk2_handshake_init_pre_post pname prologue is ie rs re ist rst h0 () h3)) =
  ()

[@@ noextract_to "krml"] inline_for_extraction noextract
val cperform_IKpsk2_handshake_init_pre_with_buffer
  (pname : hashable_t wg_inc 37ul) (prologue : hashable_t wg_inc 34ul)
  (pbuf : lbuffer uint8 (size premessage_IKpsk2_len))
  (is ie rs re : keypair_t wg_inc)
  (ist rst : handshake_state_t wg_inc) :
  Stack unit
  (requires (fun h ->
    cperform_IKpsk2_handshake_init_pre_pre pname prologue is ie rs re ist rst h /\
    live h pbuf /\ disjoint ist pbuf /\ disjoint rst pbuf))
  (ensures (fun h0 r h1 ->
    modifies3 pbuf ist rst h0 h1 /\
    cperform_IKpsk2_handshake_init_pre_post pname prologue is ie rs re ist rst h0 r h1))

(* TODO: why do we need ifuel 2 ?? *)
#push-options "--z3rlimit 100 --ifuel 2"
let cperform_IKpsk2_handshake_init_pre_with_buffer pname prologue pbuf is ie rs re
                                                   ist rst =
  (**) let h0 = HST.get () in
  (* initialization *)
  let is_priv = keypair_get_priv is in
  let is_pub = keypair_get_pub is in
  let ie_priv = keypair_get_priv ie in
  let ie_pub = keypair_get_pub ie in
  (**) prove_initialize_funct_pre_lem #wg_inc Spec.pattern_IKpsk2 true is_priv ie_priv null;
  initialize_IKpsk2 true 37ul pname 34ul prologue is_priv is_pub ie_priv ie_pub null ist;
  (**) let h1 = HST.get () in
  let rs_priv = keypair_get_priv rs in
  let rs_pub = keypair_get_pub rs in
  let re_priv = keypair_get_priv re in
  let re_pub = keypair_get_pub re in
  (**) prove_initialize_funct_pre_lem #wg_inc Spec.pattern_IKpsk2 false rs_priv re_priv null;
  initialize_IKpsk2 false 37ul pname 34ul prologue rs_priv rs_pub re_priv re_pub null rst;
  (* premessage *)
  (**) let h2 = HST.get () in
  send_premessage_IKpsk2 rst pbuf;
  (**) let h3 = HST.get () in
  receive_premessage_IKpsk2 ist pbuf;
  (**) let h4 = HST.get () in
  (**) let ismi : Ghost.erased _ = initialize_post_smi Spec.pattern_IKpsk2 true false in
  (**) let rsmi : Ghost.erased _ = csend_premessage_post_smi Spec.pattern_IKpsk2 false false in
  (**) assert(Ghost.reveal rsmi == creceive_message_pre_smi Spec.pattern_IKpsk2 false 0);
  (**) eval_handshake_state_same_lem h1 h3 ist ismi;
  (**) eval_handshake_state_same_lem h3 h4 rst rsmi
#pop-options

[@@ noextract_to "krml"] inline_for_extraction noextract
val cperform_IKpsk2_handshake_init_pre
  (pname : hashable_t wg_inc 37ul) (prologue : hashable_t wg_inc 34ul)
  (is ie rs re : keypair_t wg_inc)
  (ist rst : handshake_state_t wg_inc) :
  Stack unit
  (requires (fun h ->
    cperform_IKpsk2_handshake_init_pre_pre pname prologue is ie rs re ist rst h))
  (ensures (fun h0 r h1 ->
    modifies2 ist rst h0 h1 /\
    cperform_IKpsk2_handshake_init_pre_post pname prologue is ie rs re ist rst h0 r h1))

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
[@@ noextract_to "krml"] inline_for_extraction noextract
let cperform_IKpsk2_handshake_init_pre pname prologue is ie rs re
                                       ist rst =
  (**) let h0 = HST.get () in
  push_frame ();
  let pbuf = create (size premessage_IKpsk2_len) (u8 0) in
  (**) let h1 = HST.get () in
  cperform_IKpsk2_handshake_init_pre_with_buffer pname prologue pbuf is ie rs re
                                                 ist rst;
  (**) let h2 = HST.get () in
  pop_frame ();
  (**) let h3 = HST.get () in
  (**) assert(modifies2 ist rst h0 h3);
  (**) cperform_IKpsk2_handshake_init_pre_post_lem pname prologue is ie rs re ist rst h0 h1 h2 h3
#pop-options

(**  create initiation *)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
[@@ noextract_to "krml"] noextract
let cperform_IKpsk2_handshake_initiation_post
  (ts : timestamp_t)
  (ist rst : handshake_state_t wg_inc)
  (h0 : mem) (r : rtype (prim_error_code_return_type)) (h1 : mem) =
  let ts_v = h0.[|ts|] in
  let ismi0 = csend_message_pre_smi Spec.pattern_IKpsk2 false 0 in
  let rsmi0 = creceive_message_pre_smi Spec.pattern_IKpsk2 false 0 in
  let ismi1 = csend_message_post_smi Spec.pattern_IKpsk2 false 0 in
  let rsmi1 = creceive_message_post_smi Spec.pattern_IKpsk2 false 0 in
  let ist_v0 = eval_handshake_state h0 ist ismi0 in
  let rst_v0 = eval_handshake_state h0 rst rsmi0 in
  let ist_v1 = eval_handshake_state h1 ist ismi1 in
  let rst_v1 = eval_handshake_state h1 rst rsmi1 in
  let r_v1 = perform_IKpsk2_handshake_initiation_ ist_v0 rst_v0 ts_v in
  match is_success r, r_v1 with
  | false, None -> True
  | true, Some (ist_v1', rst_v1') ->
    ist_v1' == ist_v1 /\ rst_v1' == rst_v1
  | _ -> False

[@@ noextract_to "krml"] inline_for_extraction noextract
val cperform_IKpsk2_handshake_initiation_with_buffers
  (ibuf : lbuffer uint8 (size (initiation_IKpsk2_len)))
  (ts ts' : timestamp_t)
  (ist rst : handshake_state_t wg_inc) :
  Stack (rtype (prim_error_code_return_type))
  (requires (fun h ->
    cperform_IKpsk2_handshake_initiation_pre ts ist rst h /\
    live h ibuf /\ live h ts' /\
    disjoint ibuf ts' /\
    disjoint ibuf ts /\ disjoint ts ts' /\
    disjoint ist ibuf /\ disjoint rst ibuf /\
    disjoint ist ts' /\ disjoint rst ts'
   ))
  (ensures (fun h0 r h1 ->
    modifies4 ts' ibuf ist rst h0 h1 /\
    cperform_IKpsk2_handshake_initiation_post ts ist rst h0 r h1))

let cperform_IKpsk2_handshake_initiation_with_buffers ibuf ts ts' ist rst =
  (**) let h0 = HST.get () in
  let r1 = create_initiation_IKpsk2 ts ist ibuf in
  (**) let h1 = HST.get () in
  (**) assert(modifies2 ist ibuf h0 h1);
  (**) let _ = allow_inversion Impl.Noise.SendReceive.pattern_type_ops in
  (**) let _ = allow_inversion (eresult (Lib.ByteSequence.bytes & handshake_state Spec.wgc)) in
  (**) let _ = allow_inversion (eresult (hashable Spec.wgc & handshake_state Spec.wgc)) in
  // Brutal, but still better proof performance than ifuel 2.
  (**) let _foo #a #b: Lemma (inversion (a & b)) [ SMTPat (a & b) ] = allow_inversion (a & b) in
  let r =
    if is_success r1 then
      let r2 = consume_initiation_IKpsk2 ts' rst ibuf in
      (**) let h2 = HST.get () in
      (**) assert(modifies2 rst ts' h1 h2);
      (**) let rsmi0 : Ghost.erased _ = creceive_message_pre_smi Spec.pattern_IKpsk2 false 0 in
      (**) let ismi1 : Ghost.erased _ = csend_message_post_smi Spec.pattern_IKpsk2 false 0 in
      (**) eval_handshake_state_same_lem h0 h1 rst rsmi0;
      (**) eval_handshake_state_same_lem h1 h2 ist ismi1;
      r2
    else
      r1
  in
  (**) let h4 = HST.get () in
  norm_spec [ delta_only [ `%cperform_IKpsk2_handshake_initiation_post ] ]
    (cperform_IKpsk2_handshake_initiation_post ts ist rst h0 r h4);
  r
#pop-options

let cperform_IKpsk2_handshake_initiation_post_lem
  (ts : timestamp_t)
  (ist rst : handshake_state_t wg_inc)
  (r : rtype (prim_error_code_return_type)) (h0 h1 h2 h3 : mem) :
  Lemma
  (requires(
    h1.[|ts|] `S.equal` h0.[|ts|] /\
    h1.[|ist|] `S.equal` h0.[|ist|] /\
    h1.[|rst|] `S.equal` h0.[|rst|] /\
    h3.[|ist|] `S.equal` h2.[|ist|] /\
    h3.[|rst|] `S.equal` h2.[|rst|] /\
    cperform_IKpsk2_handshake_initiation_post ts ist rst h1 r h2
  ))
  (ensures(
    cperform_IKpsk2_handshake_initiation_post ts ist rst h0 r h3)) =
  let ismi0 = csend_message_pre_smi Spec.pattern_IKpsk2 false 0 in
  let rsmi0 = creceive_message_pre_smi Spec.pattern_IKpsk2 false 0 in
  let ismi1 = csend_message_post_smi Spec.pattern_IKpsk2 false 0 in
  let rsmi1 = creceive_message_post_smi Spec.pattern_IKpsk2 false 0 in
  eval_handshake_state_same_lem h0 h1 ist ismi0;
  eval_handshake_state_same_lem h0 h1 rst rsmi0;
  eval_handshake_state_same_lem h2 h3 ist ismi1;
  eval_handshake_state_same_lem h2 h3 rst rsmi1

[@@ noextract_to "krml"] inline_for_extraction noextract
val cperform_IKpsk2_handshake_initiation
  (ts : timestamp_t)
  (ist rst : handshake_state_t wg_inc) :
  Stack (rtype (prim_error_code_return_type))
  (requires (fun h ->
    cperform_IKpsk2_handshake_initiation_pre ts ist rst h
   ))
  (ensures (fun h0 r h1 ->
    modifies2 ist rst h0 h1 /\
    cperform_IKpsk2_handshake_initiation_post ts ist rst h0 r h1))

#push-options "--z3rlimit 100"
let cperform_IKpsk2_handshake_initiation ts ist rst =
  (**) let h0 = HST.get () in
  push_frame ();
  let ibuf = create (size initiation_IKpsk2_len) (u8 0) in
  let ts' = create timestamp_vs (u8 0) in
  (**) let h1 = HST.get () in
  let r = cperform_IKpsk2_handshake_initiation_with_buffers ibuf ts ts' ist rst in
  (**) let h2 = HST.get () in
  pop_frame ();
  (**) let h3 = HST.get () in
  assert(modifies2 ist rst h0 h3);
  cperform_IKpsk2_handshake_initiation_post_lem ts ist rst r h0 h1 h2 h3;
  r
#pop-options

(** set psk *)
[@@ noextract_to "krml"] inline_for_extraction noextract
val cperform_IKpsk2_handshake_set_psk
  (psk : preshared_key_t)
  (ist rst : handshake_state_t wg_inc) :
  Stack unit
  (requires (fun h ->
    live h psk /\ live h ist /\ live h rst /\
    disjoint ist rst /\ disjoint ist psk /\ disjoint rst psk
   ))
  (ensures (fun h0 r h1 ->
    modifies2 ist rst h0 h1 /\
    begin
    let psk_v = eval_preshared_key h0 psk in
    let ismi0 = creceive_message_pre_smi Spec.pattern_IKpsk2 false 1 in
    let rsmi0 = csend_message_pre_smi Spec.pattern_IKpsk2 false 1 in
    let ismi1 = creceive_message_pre_smi Spec.pattern_IKpsk2 true 1 in
    let rsmi1 = csend_message_pre_smi Spec.pattern_IKpsk2 true 1 in
    let ist_v0 = eval_handshake_state h0 ist ismi0 in
    let rst_v0 = eval_handshake_state h0 rst rsmi0 in
    let ist_v1 = eval_handshake_state h1 ist ismi1 in
    let rst_v1 = eval_handshake_state h1 rst rsmi1 in
    ist_v1 == Spec.Noise.Base.set_psk psk_v ist_v0 /\
    rst_v1 == Spec.Noise.Base.set_psk psk_v rst_v0
    end))

#push-options "--z3rlimit 100"
let cperform_IKpsk2_handshake_set_psk psk ist rst =
  cset_psk_IKpsk2 true psk ist;
  cset_psk_IKpsk2 false psk rst
#pop-options

(** create response *)
[@@ noextract_to "krml"] noextract
let cperform_IKpsk2_handshake_response_pre
  (ist rst : handshake_state_t wg_inc)
  (h : mem) =
  live h ist /\ live h rst /\
  disjoint ist rst

[@@ noextract_to "krml"] noextract
let cperform_IKpsk2_handshake_response_post
  (ist rst : handshake_state_t wg_inc)
  (h0 : mem) (r : rtype (prim_error_code_return_type)) (h1 : mem) =
  let ismi0 = creceive_message_pre_smi Spec.pattern_IKpsk2 true 1 in
  let rsmi0 = csend_message_pre_smi Spec.pattern_IKpsk2 true 1 in
  let ismi1 = creceive_message_post_smi Spec.pattern_IKpsk2 true 1 in
  let rsmi1 = csend_message_post_smi Spec.pattern_IKpsk2 true 1 in
  let ist_v0 = eval_handshake_state h0 ist ismi0 in
  let rst_v0 = eval_handshake_state h0 rst rsmi0 in
  let ist_v1 = eval_handshake_state h1 ist ismi1 in
  let rst_v1 = eval_handshake_state h1 rst rsmi1 in
  let r_v1 = perform_IKpsk2_handshake_response_ ist_v0 rst_v0 in
  match is_success r, r_v1 with
  | false, None -> True
  | true, Some (ist_v1', rst_v1') ->
    ist_v1' == ist_v1 /\ rst_v1' == rst_v1
  | _ -> False

[@@ noextract_to "krml"] inline_for_extraction noextract
val cperform_IKpsk2_handshake_response_with_buffers
  (rbuf : lbuffer uint8 (size response_IKpsk2_len))
  (ist rst : handshake_state_t wg_inc) :
  Stack (rtype (prim_error_code_return_type))
  (requires (fun h ->
    cperform_IKpsk2_handshake_response_pre ist rst h /\
    live h rbuf /\
    disjoint ist rbuf /\ disjoint rst rbuf
   ))
  (ensures (fun h0 r h1 ->
    modifies3 rbuf ist rst h0 h1 /\
    cperform_IKpsk2_handshake_response_post ist rst h0 r h1))

#push-options "--z3rlimit 100 --ifuel 0 --fuel 0"
let cperform_IKpsk2_handshake_response_with_buffers rbuf ist rst =
  (**) let _ = allow_inversion Impl.Noise.SendReceive.pattern_type_ops in
  // Brutal, but still better proof performance than ifuel 2.
  (**) let _foo #a #b: Lemma (inversion (a & b)) [ SMTPat (a & b) ] = allow_inversion (a & b) in
  (**) let _bar #a: Lemma (inversion (eresult a)) [ SMTPat (eresult a) ] = allow_inversion (eresult a) in

  (**) let h0 = HST.get () in
  let r1 = create_response_IKpsk2 rst rbuf in
  (**) let h1 = HST.get () in
  (**) assert(modifies2 rst rbuf h0 h1);
  (**) let rsmi0 : Ghost.erased _ = csend_message_pre_smi Spec.pattern_IKpsk2 true 1 in
  (**) let rsmi1 : Ghost.erased _ = csend_message_post_smi Spec.pattern_IKpsk2 true 1 in
  (**) let rst0_v : Ghost.erased _ = eval_handshake_state h0 rst rsmi0 in
  (**) let rst1_v : Ghost.erased _ = eval_handshake_state h1 rst rsmi1 in
  (**) let null_v : Ghost.erased _ = h0.[|null <: lbuffer uint8 0ul|] in
  (**) assert(
    match to_prim_error_code r1,
          Spec.Noise.csend_message Spec.wgc Spec.pattern_IKpsk2 1 null_v rst0_v with
    | CDH_error, Fail DH -> True
    | CSuccess, Res (out_v, st1'_v) ->
      Ghost.reveal rst1_v == st1'_v /\
      length rbuf == S.length out_v /\
      S.equal (( .[||] ) h1 rbuf) out_v
    | _ -> False);
  (**) assert(null_v `S.equal` BS.lbytes_empty);
  let r =
    if is_success r1 then
      begin
      let r2 = consume_response_IKpsk2 ist rbuf in
      (**) let h2 = HST.get () in
      (**) assert(modifies1 ist h1 h2);
      (**) let ismi0 : Ghost.erased _ = creceive_message_pre_smi Spec.pattern_IKpsk2 true 1 in
      (**) let ismi1 : Ghost.erased _ = creceive_message_post_smi Spec.pattern_IKpsk2 true 1 in
      (**) let ist1_v : Ghost.erased _ = eval_handshake_state h1 ist ismi0 in
      (**) let ist2_v : Ghost.erased _ = eval_handshake_state h2 ist ismi1 in
      (**) let rbuf_v : Ghost.erased _ = h1.[|rbuf|] in
      (**) assert(
        match to_prim_error_code r2,
              Spec.Noise.creceive_message Spec.wgc Spec.pattern_IKpsk2 1 rbuf_v ist1_v with
        | CDH_error, Fail DH | CDecrypt_error, Fail Decryption -> True
        | CSuccess, Res (null_v2', st1'_v) ->
          Ghost.reveal ist2_v == st1'_v /\
          S.length null_v2' == 0 /\ S.equal null_v2' BS.lbytes_empty
        | _ -> False
      );
      (**) eval_handshake_state_same_lem h1 h2 rst rsmi1;
      (**) eval_handshake_state_same_lem h0 h1 ist ismi0;
      r2
      end
    else r1
  in
  let h1 = HST.get () in
  norm_spec [ delta_only [ `%cperform_IKpsk2_handshake_response_post ] ]
    (cperform_IKpsk2_handshake_response_post ist rst h0 r h1);
  r
#pop-options

let cperform_IKpsk2_handshake_response_post_lem
  (ist rst : handshake_state_t wg_inc)
  (r : rtype (prim_error_code_return_type)) (h0 h1 h2 h3 : mem) :
  Lemma
  (requires(
    h1.[|ist|] `S.equal` h0.[|ist|] /\
    h1.[|rst|] `S.equal` h0.[|rst|] /\
    h3.[|ist|] `S.equal` h2.[|ist|] /\
    h3.[|rst|] `S.equal` h2.[|rst|] /\
    cperform_IKpsk2_handshake_response_post ist rst h1 r h2
  ))
  (ensures(
    cperform_IKpsk2_handshake_response_post ist rst h0 r h3)) =
  let ismi0 = creceive_message_pre_smi Spec.pattern_IKpsk2 true 1 in
  let rsmi0 = csend_message_pre_smi Spec.pattern_IKpsk2 true 1 in
  let ismi1 = creceive_message_post_smi Spec.pattern_IKpsk2 true 1 in
  let rsmi1 = csend_message_post_smi Spec.pattern_IKpsk2 true 1 in
  eval_handshake_state_same_lem h0 h1 ist ismi0;
  eval_handshake_state_same_lem h0 h1 rst rsmi0;
  eval_handshake_state_same_lem h2 h3 ist ismi1;
  eval_handshake_state_same_lem h2 h3 rst rsmi1

[@@ noextract_to "krml"] inline_for_extraction noextract
val cperform_IKpsk2_handshake_response
  (ist rst : handshake_state_t wg_inc) :
  Stack (rtype (prim_error_code_return_type))
  (requires (fun h ->
    cperform_IKpsk2_handshake_response_pre ist rst h
   ))
  (ensures (fun h0 r h1 ->
    modifies2 ist rst h0 h1 /\
    cperform_IKpsk2_handshake_response_post ist rst h0 r h1))

let cperform_IKpsk2_handshake_response ist rst =
  (**) let h0 = HST.get () in
  push_frame ();
  let rbuf = create (size response_IKpsk2_len) (u8 0) in
  (**) let h1 = HST.get () in
  let r = cperform_IKpsk2_handshake_response_with_buffers rbuf ist rst in
  (**) let h2 = HST.get () in
  pop_frame ();
  (**) let h3 = HST.get () in
  assert(modifies2 ist rst h0 h3);
  cperform_IKpsk2_handshake_response_post_lem ist rst r h0 h1 h2 h3;
  r

let cperform_IKpsk2_handshake pname prlg is ie rs re psk ts ist rst =
  let eq_lem (is ie rs re : keypair Spec.wgc) (psk : preshared_key)
             (ts : Spec.timestamp) :
    Lemma(
      perform_IKpsk2_handshake is ie rs re psk ts ==
      perform_IKpsk2_handshake_decomposed_ is ie rs re psk ts)
    [SMTPat(perform_IKpsk2_handshake is ie rs re psk ts)]
  = perform_IKpsk2_handshake_decompose_lem is ie rs re psk ts in
  cperform_IKpsk2_handshake_init_pre pname prlg is ie rs re ist rst;
  let r1 = cperform_IKpsk2_handshake_initiation ts ist rst in
  if not (is_success r1) then r1
  else
    begin
    cperform_IKpsk2_handshake_set_psk psk ist rst;
    cperform_IKpsk2_handshake_response ist rst
    end

