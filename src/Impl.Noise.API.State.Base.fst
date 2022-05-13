module Impl.Noise.API.State.Base

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

open Lib.Sequence
module S = Lib.Sequence
module L = FStar.List
module Seq = FStar.Seq

open Lib.Buffer
open LowStar.BufferOps

module LB = Lib.Buffer
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module G = FStar.Ghost

open Spec.Noise
open Spec.Noise.API
friend Spec.Noise.Base.Definitions
friend Spec.Noise.API.State.Definitions
friend Spec.Noise.API.State
open Spec.Noise.API.State.Definitions
friend Spec.Noise.API.State.Lemmas
open Spec.Noise.API.State.Lemmas
module Spec = Spec.Noise.API.State

open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.SendReceive
open Impl.Noise.RecursivePremessages
open Impl.Noise.RecursiveMessages
open Impl.Noise.FlatStructures
open Impl.Noise.CryptoPrimitives
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate

module UInt64 = FStar.UInt64

open Meta.Noise

module St = Impl.Noise.Stateful

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(*** Type definitions *)

/// For namespace purposes
open Spec.Noise.HandshakeFlags
open Spec.Noise.WellFormedness
open Spec.Noise.MetaInfo

/// Configurations

let invert_state_t
  (nc : iconfig)
  (ks : key_slots)
  (recv_tpt_msg_t : Type0)
  (spriv_t spub_t epriv_t epub_t rs_t re_t psk_t
   send_key_t send_nonce_t receive_key_t receive_nonce_t : Type0) :
  Lemma
  (inversion (state_t_raw nc ks recv_tpt_msg_t spriv_t spub_t epriv_t epub_t rs_t re_t psk_t
   send_key_t send_nonce_t receive_key_t receive_nonce_t))
  [SMTPat (state_t_raw nc ks recv_tpt_msg_t spriv_t spub_t epriv_t epub_t rs_t re_t psk_t
   send_key_t send_nonce_t receive_key_t receive_nonce_t)] =
  allow_inversion (state_t_raw nc ks recv_tpt_msg_t spriv_t spub_t epriv_t epub_t rs_t re_t psk_t
   send_key_t send_nonce_t receive_key_t receive_nonce_t)

let state_t_handshake_core_footprint (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator{IMS_Handshake? st}) :
  GTot B.loc =
  match st with
  | IMS_Handshake step k ck h spriv spub epriv epub rs re psk ->
    B.loc_union_l [
      B.loc_addr_of_buffer (k <: buffer uint8);
      B.loc_addr_of_buffer (ck <: buffer uint8);
      B.loc_addr_of_buffer (h <: buffer uint8);
      lbuffer_or_unit_to_loc epriv;
      lbuffer_or_unit_to_loc epub;
      lbuffer_or_unit_to_loc rs;
      lbuffer_or_unit_to_loc re;
      lbuffer_or_unit_to_loc psk
    ]

let state_t_handshake_footprint (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator{IMS_Handshake? st}) :
  GTot B.loc =
  match st with
  | IMS_Handshake step k ck h spriv spub epriv epub rs re psk ->
    B.loc_union_l [
      B.loc_addr_of_buffer (k <: buffer uint8);
      B.loc_addr_of_buffer (ck <: buffer uint8);
      B.loc_addr_of_buffer (h <: buffer uint8);
      lbuffer_or_unit_to_loc spriv;
      lbuffer_or_unit_to_loc spub;
      lbuffer_or_unit_to_loc epriv;
      lbuffer_or_unit_to_loc epub;
      lbuffer_or_unit_to_loc rs;
      lbuffer_or_unit_to_loc re;
      lbuffer_or_unit_to_loc psk
    ]

let state_t_transport_footprint (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator{IMS_Transport? st}) :
  GTot B.loc =
  match st with
  | IMS_Transport h recv_tpt_msg send_key send_nonce receive_key receive_nonce ->
    B.loc_union_l [
      B.loc_addr_of_buffer (h <: buffer uint8);
      lbuffer_or_unit_to_loc send_key;
      lbuffer_or_unit_to_loc receive_key
    ]

let state_t_core_footprint (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator) : GTot B.loc =
  if IMS_Handshake? st then state_t_handshake_core_footprint st
  else state_t_transport_footprint st

let state_t_footprint (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator) : GTot B.loc =
  if IMS_Handshake? st then state_t_handshake_footprint st
  else state_t_transport_footprint st

let state_t_handshake_footprint_inclusion_lem #isc st = ()

let state_t_transport_footprint_inclusion_lem #isc st = ()

let state_t_footprint_full_inclusion_lem #isc st = ()

let state_t_footprint_inclusion_lem #isc st = ()

let state_t_handshake_get_rs #isc st =
  [@inline_let]
  let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk = st in
  st_rs


/// The stateful part of the state_t handshake invariant
let state_t_handshake_invariant_stateful
  (#isc : isconfig) (#initiator : bool) (m : mem) (st : state_t isc initiator{IMS_Handshake? st}) :
  GTot Type0 =
  let IMS_Handshake step k ck h spriv spub epriv epub rs re psk = st in

  // Liveness
  live m k /\
  live m ck /\
  live m h /\ 
  lbuffer_or_unit_live m spriv /\
  lbuffer_or_unit_live m spub /\
  lbuffer_or_unit_live m epriv /\
  lbuffer_or_unit_live m epub /\
  lbuffer_or_unit_live m rs /\
  lbuffer_or_unit_live m re /\
  lbuffer_or_unit_live m psk /\

  // Freeable
  lbuffer_or_unit_freeable rs /\
  lbuffer_or_unit_freeable psk /\
  B.freeable (k <: buffer uint8) /\
  B.freeable (ck <: buffer uint8) /\
  B.freeable (h <: buffer uint8) /\
  lbuffer_or_unit_freeable epriv /\
  lbuffer_or_unit_freeable epub /\
  lbuffer_or_unit_freeable re /\

  // Disjointness
  begin
  let k_loc = B.loc_addr_of_buffer (k <: buffer uint8) in
  let ck_loc = B.loc_addr_of_buffer (ck <: buffer uint8) in
  let h_loc = B.loc_addr_of_buffer (h <: buffer uint8) in
  let spriv_loc = lbuffer_or_unit_to_loc spriv in
  let spub_loc = lbuffer_or_unit_to_loc spub in
  let epriv_loc = lbuffer_or_unit_to_loc epriv in
  let epub_loc = lbuffer_or_unit_to_loc epub in
  let rs_loc = lbuffer_or_unit_to_loc rs in
  let re_loc = lbuffer_or_unit_to_loc re in
  let psk_loc = lbuffer_or_unit_to_loc psk in
  B.all_disjoint [k_loc; ck_loc; h_loc; spriv_loc; spub_loc; epriv_loc; epub_loc; rs_loc; re_loc; psk_loc]
  end

let state_t_transport_invariant_stateful
  (#isc : isconfig) (#initiator : bool) (m : mem) (st : state_t isc initiator{IMS_Transport? st}) :
  GTot Type0 =
  let IMS_Transport h recv_tpt_msg send_key send_nonce receive_key receive_nonce = st in

  live m h /\
  lbuffer_or_unit_live m send_key /\
  lbuffer_or_unit_live m receive_key /\

  B.freeable (h <: buffer uint8) /\
  lbuffer_or_unit_freeable send_key /\
  lbuffer_or_unit_freeable receive_key /\

  begin
  let h_loc = B.loc_addr_of_buffer (h <: buffer uint8) in
  let sk_loc = lbuffer_or_unit_to_loc send_key in
  let rk_loc = lbuffer_or_unit_to_loc receive_key in
  B.all_disjoint [h_loc; sk_loc; rk_loc]
  end

let state_t_invariant_stateful (#isc : isconfig) (#initiator : bool) (m : mem) (st : state_t isc initiator) : GTot Type0 =
  if IMS_Handshake? st then state_t_handshake_invariant_stateful m st
  else state_t_transport_invariant_stateful m st

let state_t_handshake_invariant_stateful_live_rs #isc m st = ()

/// Build a meta handshake state from a state_t
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let state_t_get_hsm (#isc : isconfig) (#initiator : bool) (st : state_t isc initiator{IMS_Handshake? st}) :
  Tot (handshake_state_m (isc_get_nc isc)) =
  [@inline_let]
  let IMS_Handshake step k ck h spriv spub epriv epub rs re psk = st in
  [@inline_let]
  let ssm = mk_ssm k ck h in
  [@inline_let]
  let s = mk_keypair_m (lbuffer_or_unit_to_lbuffer_or_null spriv)
                       (lbuffer_or_unit_to_lbuffer_or_null spub) in
  [@inline_let]
  let e = mk_keypair_m (lbuffer_or_unit_to_lbuffer_or_null epriv)
                       (lbuffer_or_unit_to_lbuffer_or_null epub) in
  [@inline_let]
  let rs = lbuffer_or_unit_to_lbuffer_or_null rs in
  [@inline_let]
  let re = lbuffer_or_unit_to_lbuffer_or_null re in
  [@inline_let]
  let psk = lbuffer_or_unit_to_lbuffer_or_null psk in
  mk_hsm ssm s e rs re psk

/// Interpretation as high level types

let isc_valid_meta_info (isc : isconfig) (smi : meta_info) : bool =
  ks_valid_meta_info (isc_get_ks isc) smi

let isc_valid_meta_info_lem (isc : isconfig) (smi : meta_info) = ()

let state_t_get_hash_lem #isc #initiator st h = ()

let handshake_state_t_v_with_smi (#isc : isconfig) (#initiator : bool) (m : mem)
                                 (st : state_t isc initiator{IMS_Handshake? st})
                                 (smi : meta_info) =
  let IMS_Handshake step k ck h spriv spub epriv epub rs re psk = st in
  let hsm = state_t_get_hsm st in
  let hst = eval_handshake_state_m m hsm smi in
  let status = step_to_status initiator (UInt32.v step) in
  {
    Spec.st_pattern = isc_get_pattern isc;
    Spec.st_initiator = initiator;
    Spec.st_hs_state = IS_Handshake status hst;
  }

let transport_state_t_v (#isc : isconfig) (#initiator : bool) (m : mem)
                        (st : state_t isc initiator{state_t_is_transport st}) =
  let IMS_Transport h recv_tpt_msg send_key send_nonce receive_key receive_nonce = st in
  let h = as_seq m h in
  let recv_tpt_message = bool_or_gbool_to_gbool recv_tpt_msg in
  let send_cs =
    if isc_get_send isc then
      let send_key = lbuffer_or_unit_to_opt_lseq m send_key in
      let send_nonce = UInt64.v send_nonce in
      Some (Mkcipher_state send_key send_nonce)
    else
      None
  in
  let receive_cs =
    if isc_get_receive isc then
      let receive_key = lbuffer_or_unit_to_opt_lseq m receive_key in
      let receive_nonce = UInt64.v receive_nonce in
      Some (Mkcipher_state receive_key receive_nonce)
    else
      None
  in
  {
    Spec.st_pattern = isc_get_pattern isc;
    Spec.st_initiator = initiator;
    Spec.st_hs_state = IS_Transport h recv_tpt_message send_cs receive_cs;
  }

let handshake_state_t_frame_invariant #isc l st smi h0 h1 = ()

let transport_state_t_frame_invariant #isc l st h0 h1 = ()

(*** Protocol name *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let compute_protocol_name_length
  (nc : config) (pattern_name : string{check_pattern_name pattern_name}) :
  Pure size_nat
  (requires True)
  (ensures (fun l ->
    l == Seq.length (Spec.compute_protocol_name_byteseq pattern_name nc) /\
    l > 0 /\
    is_hashable_size nc l)) =
  with_onorm(protocol_name_length (String.length pattern_name) nc)

#push-options "--fuel 1 --ifuel 1"
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let compute_protocol_name_alloca
  (nc : iconfig) (pattern_name : string{check_pattern_name pattern_name}) :
  StackInline (hashable_t nc (size (compute_protocol_name_length (get_config nc) pattern_name)))
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 ->
    let b : buffer uint8 = b in
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (B.loc_addr_of_buffer b) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (B.loc_addr_of_buffer b)) /\
    B.live h1 b /\
    as_seq #MUT #uint8 #(size (compute_protocol_name_length (get_config nc) pattern_name)) h1 b ==
    Spec.compute_protocol_name_byteseq pattern_name (get_config nc))) =
  [@inline_let]
  let l = with_onorm(compute_protocol_name_length (get_config nc) pattern_name) in
  (**) assert(is_hashable_size (get_config nc) l);
  [@inline_let]
  let s : list uint8 = with_norm (compute_protocol_name_bytes_list pattern_name (get_config nc)) in
  (**) assert(List.Tot.length s > 0);
  (**) assert(List.Tot.length s <= max_size_t);
  (**) let h0 = ST.get () in
  (**) normalize_term_spec(List.Tot.length s);
  LB.createL #uint8 s
#pop-options

(**** Premessages *)

/// We don't support premessages which contain ephemerals for now
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_send_premessage_none :
  #nc : iconfig ->
  smi : Ghost.erased meta_info ->
  st : valid_hsm nc smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h -> hsm_inv h st smi))
  (ensures (
     fun h0 r h1 ->
     modifies0 h0 h1 /\
     begin
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi in
     let r1_v = Spec.process_send_premessage None st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Some (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

let process_send_premessage_none #nc smi st = success _

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_send_premessage_s :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : Ghost.erased meta_info ->
  st : valid_hsm nc smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h -> hsm_inv h st smi /\
                    has_pretoken smi PS /\
                    get_hash_pre nc))
  (ensures (
     fun h0 r h1 ->
     ssm_modifies0 (hsm_get_sym_state st) h0 h1 /\
     begin
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi in
     let r1_v = Spec.process_send_premessage (Some [PS]) st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Some (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

let process_send_premessage_s #nc ssi smi st =
  (**) let h0 = ST.get () in
  (**) process_send_premessage_s_lem #(get_config nc) (eval_handshake_state_m h0 st smi);
  [@inline_let] let k = kpm_get_pub (hsm_get_static st) in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  (**) hash_max_input_norm_lem (get_config nc);
  ssi_get_mix_hash ssi smi.hsf.sk (public_key_vs nc) k sym_st smi.nonce

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_send_premessage :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : Ghost.erased meta_info ->
  tks : option (list premessage_token){tks = None || tks = Some [PS]} ->
  st : valid_hsm nc smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h -> hsm_inv h st smi /\
                    (if tks = Some [PS] then (has_pretoken smi PS /\ get_hash_pre nc)
                    else True)))
  (ensures (
     fun h0 r h1 ->
     ssm_modifies0 (hsm_get_sym_state st) h0 h1 /\
     begin
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi in
     let r1_v = Spec.process_send_premessage tks st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Some (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

let process_send_premessage #nc ssi smi tks st =
  match tks with
  | None -> process_send_premessage_none #nc smi st
  | Some [PS] -> process_send_premessage_s #nc ssi smi st

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_receive_premessage_none :
  #nc : iconfig ->
  smi : Ghost.erased meta_info ->
  #rsb : bool ->
  rs : public_key_t_or_unit nc rsb ->
  st : valid_hsm nc smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h -> hsm_inv h st smi))
  (ensures (
     fun h0 r h1 ->
     modifies0 h0 h1 /\
     begin
     let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi in
     let r1_v = Spec.process_receive_premessage None rs_v None st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Some (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

let process_receive_premessage_none #nc smi #rsb rs st = success _

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_receive_premessage_s :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : Ghost.erased meta_info ->
  rs : public_key_t_or_unit nc true ->
  st : valid_receive_pretoken_hsm nc PS smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h ->
    hsm_inv h st smi /\
    lbuffer_or_unit_live h rs /\
    ssm_loc_disjoint (hsm_get_sym_state st) (lbuffer_or_unit_to_loc rs) /\
    B.loc_disjoint (B.loc_buffer (hsm_get_remote_static st <: buffer uint8))
                   (lbuffer_or_unit_to_loc rs) /\
    no_remote_pretoken smi PS /\
    get_hash_pre nc))
  (ensures (
     fun h0 r h1 ->
     B.(modifies (loc_union (ssm_loc (hsm_get_sym_state st))
                            (loc_buffer (hsm_get_remote_static st <: buffer uint8))) h0 h1) /\
     begin
     let smi1 = receive_pretoken_update_smi PS smi in
     let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi1 in
     let r1_v = Spec.process_receive_premessage (Some [PS]) rs_v None st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Some (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

let process_receive_premessage_s #nc ssi smi rs st =
  (**) let h0 = ST.get () in
  (**) Spec.process_receive_premessage_s_lem #(get_config nc)
                                             (lbuffer_or_unit_to_opt_lseq h0 rs)
                                             None
                                             (eval_handshake_state_m h0 st smi);
  [@inline_let] let k = hsm_get_remote_static st in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  update_sub #MUT #uint8 #(public_key_vs nc) k 0ul (public_key_vs nc) rs;
  (**) hash_max_input_norm_lem (get_config nc);
  ssi_get_mix_hash ssi smi.hsf.sk (public_key_vs nc) (rs <: buffer uint8) sym_st smi.nonce

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_receive_premessage :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : Ghost.erased meta_info ->
  tks : option (list premessage_token){tks = None || tks = Some [PS]} ->
  #rsb : bool ->
  rs : public_key_t_or_unit nc rsb ->
  st : valid_hsm nc smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h ->
    hsm_inv h st smi /\
    begin
    Some? tks ==>
    (lbuffer_or_unit_live h rs /\
     ssm_loc_disjoint (hsm_get_sym_state st) (lbuffer_or_unit_to_loc rs) /\
     B.loc_disjoint (B.loc_buffer (hsm_get_remote_static st <: buffer uint8))
                    (lbuffer_or_unit_to_loc rs) /\
     rsb = true /\
     no_remote_pretoken smi PS /\
     get_hash_pre nc /\
     is_valid_hsm (receive_pretoken_update_smi PS smi) st)
    end))
  (ensures (
     fun h0 r h1 ->
     begin
     match tks with
     | None -> B.(modifies loc_none h0 h1)
     | Some [PS] ->
       B.(modifies (loc_union
         (ssm_loc (hsm_get_sym_state st))
         (loc_buffer (hsm_get_remote_static st <: buffer uint8))) h0 h1)
     end /\
     begin
     let smi1 : meta_info = if Some? tks then receive_pretoken_update_smi PS smi else smi in
     let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi1 in
     let r1_v = Spec.process_receive_premessage tks rs_v None st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Some (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

let process_receive_premessage #nc ssi smi tks #rsb rs (* #reb re *) st =
  match tks with
  | None -> process_receive_premessage_none #nc smi rs st
  | Some [PS] -> process_receive_premessage_s #nc ssi smi rs st


[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_initiator_premessages :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : Ghost.erased meta_info ->
  pattern:wf_handshake_pattern{handshake_pattern_is_valid pattern} ->
  #rsb : bool ->
  rs : public_key_t_or_unit nc rsb ->
  st : valid_hsm nc smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h ->
    hsm_inv h st smi /\
    (* I -> R *)
    begin
    pattern.premessage_ir = Some [PS] ==>
    (has_pretoken smi PS /\ get_hash_pre nc)
    end /\
    (* R -> I *)
    begin
    pattern.premessage_ri = Some [PS] ==>
    (lbuffer_or_unit_live h rs /\
     ssm_loc_disjoint (hsm_get_sym_state st) (lbuffer_or_unit_to_loc rs) /\
     B.loc_disjoint (B.loc_buffer (hsm_get_remote_static st <: buffer uint8))
                    (lbuffer_or_unit_to_loc rs) /\
     rsb = true /\
     no_remote_pretoken smi PS /\
     get_hash_pre nc /\
     is_valid_hsm (receive_pretoken_update_smi PS smi) st)
    end))
  (ensures (
     fun h0 r h1 ->
     begin
     match pattern.premessage_ri with
     | None -> ssm_modifies0 (hsm_get_sym_state st) h0 h1
     | Some [PS] ->
       B.(modifies (loc_union
         (ssm_loc (hsm_get_sym_state st))
         (loc_buffer (hsm_get_remote_static st <: buffer uint8))) h0 h1)
     end /\
     begin
     let smi1 : meta_info =
       if Some? pattern.premessage_ri
       then receive_pretoken_update_smi PS smi else smi
     in
     let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi1 in
     let r1_v = Spec.process_initiator_premessages pattern rs_v None st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Res (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

let process_initiator_premessages #nc ssi smi pattern #rsb rs st =
  [@inline_let] let Mkhandshake_pattern _ premessage_ir premessage_ri _ = pattern in
  process_send_premessage ssi smi premessage_ir st;
  process_receive_premessage ssi smi premessage_ri rs st


[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_responder_premessages :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : Ghost.erased meta_info ->
  pattern:wf_handshake_pattern{handshake_pattern_is_valid pattern} ->
  #rsb : bool ->
  rs : public_key_t_or_unit nc rsb ->
  st : valid_hsm nc smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h ->
    let smi_ri : meta_info =
      if pattern.premessage_ir = Some [PS] then receive_pretoken_update_smi PS smi
      else smi
    in
    hsm_inv h st smi /\
    (* I -> R *)
    begin
    pattern.premessage_ir = Some [PS] ==>
    (lbuffer_or_unit_live h rs /\
     ssm_loc_disjoint (hsm_get_sym_state st) (lbuffer_or_unit_to_loc rs) /\
     B.loc_disjoint (B.loc_buffer (hsm_get_remote_static st <: buffer uint8))
                    (lbuffer_or_unit_to_loc rs) /\
     rsb = true /\
     no_remote_pretoken smi PS /\
     get_hash_pre nc /\
     is_valid_hsm (receive_pretoken_update_smi PS smi) st)
    end /\
    (* R -> I *)
    begin
    pattern.premessage_ri = Some [PS] ==>
    (has_pretoken smi_ri PS /\ get_hash_pre nc)
    end))
  (ensures (
     fun h0 r h1 ->
     begin
     match pattern.premessage_ir with
     | None -> ssm_modifies0 (hsm_get_sym_state st) h0 h1
     | Some [PS] ->
       B.(modifies (loc_union
         (ssm_loc (hsm_get_sym_state st))
         (loc_buffer (hsm_get_remote_static st <: buffer uint8))) h0 h1)
     end /\
     begin
     let smi1 : meta_info =
       if Some? pattern.premessage_ir
       then receive_pretoken_update_smi PS smi else smi
     in
     let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi1 in
     let r1_v = Spec.process_responder_premessages pattern rs_v None st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Res (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

#push-options "--fuel 2 --ifuel 2"
let process_responder_premessages #nc ssi smi pattern #rsb rs st =
  [@inline_let] let Mkhandshake_pattern _ premessage_ir premessage_ri _ = pattern in
  process_receive_premessage ssi smi premessage_ir rs st;
  process_send_premessage ssi smi premessage_ri st
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let process_premessages_update_smi
  (pattern : wf_handshake_pattern{handshake_pattern_is_valid pattern})
  (initiator : bool)
  (smi : meta_info) : Tot meta_info =
  [@inline_let] let send_pre, recv_pre = get_send_recv_premsgs pattern initiator in
  if Some? recv_pre then receive_pretoken_update_smi PS smi else smi

let process_premessages_smi_pre
  (#nc : iconfig)
  (smi : Ghost.erased meta_info)
  (pattern:wf_handshake_pattern{handshake_pattern_is_valid pattern})
  (initiator : bool)
  (rsb : bool)
  (st : valid_hsm nc smi)
  =
  let send_pre, recv_pre = get_send_recv_premsgs pattern initiator in
  (send_pre = Some [PS] ==> has_pretoken smi PS) /\
  (recv_pre = Some [PS] ==>
   rsb = true && no_remote_pretoken smi PS
   && is_valid_hsm (receive_pretoken_update_smi PS smi) st)  

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val process_premessages :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  smi : Ghost.erased meta_info ->
  pattern:wf_handshake_pattern{handshake_pattern_is_valid pattern} ->
  initiator : bool ->
  #rsb : bool ->
  rs : public_key_t_or_unit nc rsb ->
  st : valid_hsm nc smi ->
  Stack (rtype tokens_premessage_return_type)
  (requires (fun h ->
    let smi_ri : meta_info =
      if pattern.premessage_ir = Some [PS] then receive_pretoken_update_smi PS smi
      else smi
    in
    hsm_inv h st smi /\

    lbuffer_or_unit_live h rs /\
    ssm_loc_disjoint (hsm_get_sym_state st) (lbuffer_or_unit_to_loc rs) /\
    B.loc_disjoint (B.loc_buffer (hsm_get_remote_static st <: buffer uint8))
                   (lbuffer_or_unit_to_loc rs) /\
    get_hash_pre nc /\

    process_premessages_smi_pre #nc smi pattern initiator rsb st))

  (ensures (
     fun h0 r h1 ->
    let send_pre, recv_pre = get_send_recv_premsgs pattern initiator in
     begin
     match recv_pre with
     | None -> ssm_modifies0 (hsm_get_sym_state st) h0 h1
     | Some [PS] ->
       B.(modifies (loc_union
         (ssm_loc (hsm_get_sym_state st))
         (loc_buffer (hsm_get_remote_static st <: buffer uint8))) h0 h1)
     end /\
     begin
     let smi1 : meta_info = process_premessages_update_smi pattern initiator smi in
     let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
     let st0_v = eval_handshake_state_m h0 st smi in
     let st1_v = eval_handshake_state_m h1 st smi1 in
     let r1_v = Spec.process_premessages pattern initiator rs_v None st0_v in
     match to_prim_error_code r, r1_v with
     | CSuccess, Res (st1'_v) ->
       st1_v == st1'_v
     | _ -> False
     end))

let process_premessages #nc ssi smi pattern initiator #rsb rs st =
  if initiator then process_initiator_premessages ssi smi pattern rs st
  else process_responder_premessages ssi smi pattern rs st

(*** Create state *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_state_t_malloc :
     #isc:isconfig
  -> r:HS.rid
  -> initiator:bool
  -> step:UInt32.t
  -> spriv:sprivate_key_t isc
  -> spub:spublic_key_t isc ->
  ST (st:state_t isc initiator{IMS_Handshake? st})
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    lbuffer_or_unit_live h0 spriv /\
    lbuffer_or_unit_live h0 spub /\
    B.loc_disjoint (region_to_loc r) (lbuffer_or_unit_to_loc spriv) /\
    B.loc_disjoint (region_to_loc r) (lbuffer_or_unit_to_loc spub) /\
    B.loc_disjoint (lbuffer_or_unit_to_loc spriv) (lbuffer_or_unit_to_loc spub)))
  (ensures (fun h0 st h1 ->
    B.(modifies loc_none h0 h1) /\
    state_t_handshake_invariant_stateful h1 st /\
    region_includes r (state_t_core_footprint st) /\
    B.fresh_loc (state_t_core_footprint st) h0 h1 /\
    begin
    let IMS_Handshake step' st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk = st in
    let nc = isc_get_nc isc in
    step' == step /\
    as_seq h1 st_ck == Seq.create (chaining_key_vsv nc) (u8 0) /\
    as_seq h1 st_h == Seq.create (hash_vsv nc) (u8 0) /\
    st_spriv == spriv /\
    st_spub == spub
    end))

let mk_state_t_malloc #isc r initiator step spriv spub =
  (**) let h0 = ST.get () in
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let pattern = isc_get_pattern isc in
  (**) let r_state = r in
  (**) let r_pname = r in
  let st_k : aead_key_t = (B.malloc r_state (u8 0) aead_key_vs <: buffer uint8) in
  let st_ck : chaining_key_t nc = (B.malloc r_state (u8 0) (chaining_key_vs nc) <: buffer uint8) in
  let st_h : hash_t nc = (B.malloc r_state (u8 0) (hash_vs nc) <: buffer uint8) in
  let st_spriv = spriv in // sharing public keys with the device
  let st_spub = spub in // sharing public keys with the device
  let st_epriv : eprivate_key_t isc = lbuffer_or_unit_malloc r_state (u8 0) in
  let st_epub : epublic_key_t isc = lbuffer_or_unit_malloc r_state (u8 0) in
  let st_rs : rspublic_key_t isc = lbuffer_or_unit_malloc r_state (u8 0) in
  let st_re : republic_key_t isc = lbuffer_or_unit_malloc r_state (u8 0) in
  let st_psk : psk_t isc = lbuffer_or_unit_malloc r_state (u8 0) in

  (**) assert(region_includes r_state (B.loc_addr_of_buffer (st_k <: buffer uint8))); // Needed
  (**) assert(region_includes r_state (B.loc_addr_of_buffer (st_ck <: buffer uint8))); // Needed
  (**) assert(region_includes r_state (B.loc_addr_of_buffer (st_h <: buffer uint8))); // Needed
  (**) assert(region_includes r_state (lbuffer_or_unit_to_loc st_epriv)); // Needed
  (**) assert(region_includes r_state (lbuffer_or_unit_to_loc st_epub)); // Needed
  (**) assert(region_includes r_state (lbuffer_or_unit_to_loc st_rs)); // Needed
  (**) assert(region_includes r_state (lbuffer_or_unit_to_loc st_re)); // Needed
  (**) assert(region_includes r_state (lbuffer_or_unit_to_loc st_psk)); // Needed

  [@inline_let]
  let st = IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                         st_epriv st_epub st_rs st_re st_psk in

  (**) let h1 = ST.get () in
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  (**) assert(B.(modifies loc_none h0 h1));
  (**) assert(state_t_handshake_invariant_stateful h1 st);

  st

// Note that the sm_result should disappear at extraction time

/// Every flag true for the hsf must be true for the key_slots (meaning we can store
/// the key).
let hsf_smaller_than_key_slots (hsf : handshake_state_flags) (ks : key_slots) : Tot bool =
  (not hsf.Spec.Noise.s || ks.ks_s) &&
  (not hsf.Spec.Noise.e || ks.ks_e) &&
  (not hsf.Spec.Noise.rs || ks.ks_rs) &&
  (not hsf.Spec.Noise.re || ks.ks_re) &&
  (not hsf.Spec.Noise.psk || ks.ks_psk)

let create_state_smi (isc : isconfig) (rsb pskb : bool) : meta_info =
  create_state_smi_compute (isc_get_ks isc) rsb pskb

let create_state_smi_lem (isc : isconfig) (rsb pskb : bool) = ()

let create_state_smi_pre
  (isc:isconfig{isc_has_valid_pattern isc})
  (initiator rsb pskb : bool) : Tot bool =
  let pattern = isc_get_pattern isc in
  let send_pre, recv_pre = get_send_recv_premsgs pattern initiator in
  let has_s = isc_get_s isc in
  let has_rs = isc_get_rs isc in
  create_state_smi_pre_aux pattern has_s has_rs initiator rsb

let create_state_smi_pre_lem
  (isc:isconfig{isc_has_valid_pattern isc})
  (initiator rsb pskb : bool) = ()

let create_state_smi_valid_lem (isc : isconfig{isc_has_valid_pattern isc})
                               (initiator rsb pskb : bool) = ()

val create_state_smi_process_premessages_lem
  (isc:isconfig{isc_has_valid_pattern isc})
  (initiator rsb pskb : bool) :
  Lemma
  (requires (create_state_smi_pre isc initiator rsb pskb))
  (ensures (
    let pattern = isc_get_pattern isc in
    let smi1 = create_state_smi isc false pskb in
    let smi2 = process_premessages_update_smi pattern initiator smi1 in
    let smi2' = create_state_smi isc rsb pskb in
    smi2 = smi2'
  ))

let create_state_smi_process_premessages_lem isc initiator rsb pskb = ()

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_state_t_create_state_no_alloc :
     #isc:isconfig{isc_has_valid_pattern isc}
  -> ssi:ss_impls (isc_get_nc isc)
  -> initialize:initialize_handshake_state_st (isc_get_nc isc)
  -> initiator:bool // This parameter is meta
  -> prlg_len:hashable_size_t (isc_get_nc isc)
  -> prlg:hashable_t (isc_get_nc isc) prlg_len
  -> pname_len:hashable_size_t (isc_get_nc isc)
  -> pname:hashable_t (isc_get_nc isc) pname_len
  -> epriv:eprivate_key_t isc
  -> epub:epublic_key_t isc
  -> #rsb:bool
  -> rs:public_key_t_or_unit (isc_get_nc isc) (rsb && isc_get_rs isc)
  -> #pskb:bool
  -> psk:preshared_key_t_or_unit (pskb && isc_get_psk isc)
  -> st:state_t isc initiator{IMS_Handshake? st} ->
  Stack unit
  (requires (fun h0 ->
    let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk = st in
    let pattern = isc_get_pattern isc in

    lbuffer_or_unit_live h0 epriv /\
    lbuffer_or_unit_live h0 epub /\
    lbuffer_or_unit_live h0 rs /\
    lbuffer_or_unit_live h0 psk /\
    live h0 prlg /\
    live h0 pname /\
    state_t_handshake_invariant_stateful h0 st /\

    B.loc_disjoint (state_t_footprint st) (lbuffer_or_unit_to_loc epriv) /\
    B.loc_disjoint (state_t_footprint st) (lbuffer_or_unit_to_loc epub) /\
    B.loc_disjoint (lbuffer_or_unit_to_loc epriv) (lbuffer_or_unit_to_loc epub) /\
    B.loc_disjoint (state_t_footprint st) (lbuffer_or_unit_to_loc rs) /\
    B.loc_disjoint (state_t_footprint st) (lbuffer_or_unit_to_loc psk) /\
    B.loc_disjoint (state_t_footprint st) (B.loc_buffer (prlg <: buffer uint8)) /\
    B.loc_disjoint (state_t_footprint st) (B.loc_buffer (pname <: buffer uint8)) /\

    B.as_seq h0 (pname <: buffer uint8) ==
      compute_protocol_name_byteseq (isc_get_pattern isc).name (isc_get_config isc) /\

    create_state_smi_pre isc initiator rsb pskb /\

    UInt32.v step = 0 /\
    as_seq h0 st_h == Seq.create (hash_vsv (isc_get_nc isc)) (u8 0) /\
    get_hash_pre (isc_get_nc isc)))

  (ensures (fun h0 res h1 ->
    B.(modifies (state_t_core_footprint st) h0 h1) /\
    state_t_handshake_invariant_stateful h1 st /\
    begin
    let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk = st in
    let s_v = mk_keypair_from_keys_or_unit h0 st_spriv st_spub in
    let e_v = mk_keypair_from_keys_or_unit h0 epriv epub in
    let prlg_v = as_seq h0 prlg in
    let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
    let psk_v = lbuffer_or_unit_to_opt_lseq h0 psk in
    match create_state (isc_get_pattern isc) prlg_v initiator s_v e_v rs_v psk_v with
    | Res st'_v ->
      let smi = create_state_smi isc rsb pskb in
      handshake_state_t_v_with_smi h1 st smi == st'_v
    | _ -> False
    end))

#push-options "--z3rlimit 200"
let mk_state_t_create_state_no_alloc #isc ssi initialize initiator prlg_len prlg 
                                     pname_len pname epriv epub #rsb rs
                                     #pskb psk st =
  (**) let h0 = ST.get () in

  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let pattern = isc_get_pattern isc in
  [@inline_let]
  let Mkhandshake_pattern pattern_name pre_ir pre_ri messages = pattern in
  [@inline_let]
  let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk = st in
  [@inline_let] let st_s = mk_keypair_m_from_keys_or_unit st_spriv st_spub in
  [@inline_let] let st_e = mk_keypair_m_from_keys_or_unit st_epriv st_epub in
  [@inline_let] let ssm = mk_ssm st_k st_ck st_h in
  [@inline_let]
  let hsm = mk_hsm ssm st_s st_e (lbuffer_or_unit_to_lbuffer_or_null st_rs)
                                 (lbuffer_or_unit_to_lbuffer_or_null st_re)
                                 (lbuffer_or_unit_to_lbuffer_or_null st_psk) in
  (**) assert(
  (**)   initialize_handshake_state_pre pname_len pname
  (**)     prlg_len prlg
  (**)     #false () () // Don't copy the local static keys: already copied
  (**)     #(isc_get_e isc) epriv epub
  (**)     #false () #false () // Remote keys: copied when receiving premessages
  (**)     #(pskb && isc_get_psk isc) psk
  (**)     hsm h0);

  initialize pname_len pname
             prlg_len prlg
             #false () () // Don't copy the local static keys: already copied
             #(isc_get_e isc) epriv epub
             #false () #false () // Remote keys: copied when receiving premessages
             #(pskb && isc_get_psk isc) psk
             hsm;

  [@inline_let]
  let smi1 : Ghost.erased meta_info = create_state_smi isc false pskb in // note that we ignore rs for now

  // Checking that we got the correct state - note that we don't give the psk
  // nor the static identity to initialize above, because they have already
  // been copied: this is the non trivial part of the assertion.
  (**) let h1 = ST.get () in
  (**) assert(B.(modifies (state_t_core_footprint st) h0 h1));
  (**) assert(state_t_handshake_invariant_stateful h1 st);

  begin
  (**) let pname_v = compute_protocol_name_byteseq (isc_get_pattern isc).name (isc_get_config isc) in
  (**) let prologue_v = as_seq h0 prlg in
  (**) let s_v = mk_keypair_from_keys_or_unit h0 st_spriv st_spub in
  (**) let e_v = mk_keypair_from_keys_or_unit h0 epriv epub in
  (**) let psk_v = lbuffer_or_unit_to_opt_lseq h0 psk in
  (**) let st1_v = initialize_handshake_state pname_v prologue_v s_v e_v None None psk_v in
  (**) initialize_handshake_state_s_psk_frame_lem pname_v prologue_v s_v e_v None None psk_v;
  (**) assert(
  (**)   eval_symmetric_state_m h1 ssm false 0 == st1_v.sym_state /\
  (**)   mk_keypair_from_keys_or_unit h1 st_spriv st_spub == st1_v.static /\
  (**)   mk_keypair_from_keys_or_unit h1 st_epriv st_epub == st1_v.ephemeral /\
  (**)   st1_v.remote_static == None /\
  (**)   st1_v.remote_ephemeral == None /\
  (**)   (pskb ==> lbuffer_or_unit_to_opt_lseq h1 st_psk == st1_v.preshared)
  (**)   );
  (**) let st1'_v = eval_handshake_state_m h1 hsm smi1 in
  (**) assert(st1'_v.sym_state == st1_v.sym_state);
  (**) assert(st1'_v.static == st1_v.static);
  (**) assert(st1'_v.ephemeral == st1_v.ephemeral);
  (**) assert(st1'_v.remote_static == st1_v.remote_static);
  (**) assert(st1'_v.remote_ephemeral == st1_v.remote_ephemeral);
  (**) assert(pskb ==> st1'_v.preshared == st1_v.preshared);
  (**) assert(st1'_v == st1_v)
  end;

  (* Premessages *)
  begin
  (**) let smi2 = process_premessages_update_smi pattern initiator smi1 in
  (**) assert(smi2 = create_state_smi isc rsb pskb)
  end;

  process_premessages #nc ssi smi1 pattern initiator #(rsb && isc_get_rs isc) rs hsm;

  (**) let h2 = ST.get () in
  (**) assert(B.(modifies (state_t_core_footprint st) h1 h2));

  (* Return *)
  (**) assert(B.(modifies (state_t_core_footprint st) h0 h2));
  (**) assert(lbuffer_or_unit_to_opt_lseq h2 st_spriv == lbuffer_or_unit_to_opt_lseq h0 st_spriv);
  (**) assert(lbuffer_or_unit_to_opt_lseq h2 st_spub == lbuffer_or_unit_to_opt_lseq h0 st_spub);
  (**) assert(state_t_handshake_invariant_stateful h2 st);

  (**) assert(
    let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk = st in
    let s_v = mk_keypair_from_keys_or_unit h0 st_spriv st_spub in
    let e_v = mk_keypair_from_keys_or_unit h0 epriv epub in
    let prlg_v = as_seq h0 prlg in
    let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
    let psk_v = lbuffer_or_unit_to_opt_lseq h0 psk in
    match create_state (isc_get_pattern isc) prlg_v initiator s_v e_v rs_v psk_v with
    | Res st'_v ->
      let smi = create_state_smi isc rsb pskb in
      handshake_state_t_v_with_smi h2 st smi == st'_v
    | _ -> False)
#pop-options

#push-options "--z3rlimit 300"
let mk_state_t_create_state =
  fun #isc ssi initialize r initiator prlg_len prlg
    spriv spub epriv epub #rsb rs #pskb psk ->
  (**) let h0 = ST.get () in
  // Trick to use a region <> root (necessary to prove that it is disjoint from the stack frame)
  (**) let r_state = new_region r in
  (**) assert(region_includes_region r r_state);
  let st = mk_state_t_malloc #isc r_state initiator 0ul spriv spub in
  (**) assert(region_includes r (state_t_core_footprint st));
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let pattern_name = with_onorm ((isc_get_pattern isc).name) in
  [@inline_let] let pname_len = size (compute_protocol_name_length (get_config nc) pattern_name) in
  (**) let h1 = ST.get () in
  (**) push_frame ();
  ST.recall_region r_state;
  (**) let h2 = ST.get () in
  let pname : lbuffer uint8 pname_len = compute_protocol_name_alloca nc pattern_name in
  mk_state_t_create_state_no_alloc #isc ssi initialize initiator prlg_len prlg 
                                   pname_len pname epriv epub #rsb rs
                                   #pskb psk st;
  (**) pop_frame ();
  (**) let h3 = ST.get () in
  (**) B.(modifies_only_not_unused_in loc_none h0 h3);
  st
#pop-options

(*** Free *)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_state_t_handshake_free :
     #isc:isconfig
  -> #initiator:bool
  -> st:state_t isc initiator{IMS_Handshake? st} ->
  ST unit
  (requires (fun h0 ->
    state_t_handshake_invariant_stateful h0 st))
  (ensures (fun h0 res h1 ->
    B.(modifies (state_t_handshake_core_footprint st) h0 h1)))

let mk_state_t_handshake_free #isc #initiator st =
  [@inline_let]
  let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk = st in
  B.free (st_k <: buffer uint8);
  B.free (st_ck <: buffer uint8);
  B.free (st_h <: buffer uint8);
  lbuffer_or_unit_free st_epriv;
  lbuffer_or_unit_free st_epub;
  lbuffer_or_unit_free st_rs;
  lbuffer_or_unit_free st_re;
  lbuffer_or_unit_free st_psk

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_state_t_transport_free :
     #isc:isconfig
  -> #initiator:bool
  -> st:state_t isc initiator{IMS_Transport? st} ->
  ST unit
  (requires (fun h0 ->
    state_t_transport_invariant_stateful h0 st))
  (ensures (fun h0 res h1 ->
    B.(modifies (state_t_transport_footprint st) h0 h1)))

let mk_state_t_transport_free #isc #initiator st =
  [@inline_let]
  let IMS_Transport st_h recv_tpt_msg send_key send_nonce receive_key receive_nonce = st in
  B.free (st_h <: buffer uint8);
  lbuffer_or_unit_free send_key;
  lbuffer_or_unit_free receive_key

let mk_state_t_free #isc #initiator st =
  match st with
  | IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                  st_epriv st_epub st_rs st_re st_psk ->
    (* mk_state_t_handshake_free also performs a match on st. By reconstructing
     * st we make sure it nicely reduces and doesn't lead to two matches in the
     * extracted code *)
    [@inline_let]
    let st = IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                  st_epriv st_epub st_rs st_re st_psk in
    mk_state_t_handshake_free #isc #initiator st
  | IMS_Transport st_h recv_tpt_msg send_key send_nonce receive_key receive_nonce ->
    [@inline_let]
    let st = IMS_Transport st_h recv_tpt_msg send_key send_nonce receive_key receive_nonce in
    mk_state_t_transport_free #isc #initiator st

(*** Handshake read/write utilities *)

#push-options "--z3rlimit 100"
let check_input_output_len nc smi is_psk pat payload_len msg_len =
  [@inline_let] let has_sym_key = with_onorm(smi.hsf.sk) in
  [@inline_let]
  let l1 = with_onorm(tokens_message_size (get_config nc) has_sym_key is_psk pat) in
  [@inline_let]
  let has_sym_key' = with_onorm(tokens_update_sym_key_flag has_sym_key is_psk pat) in
  // If there is a symmetric key, we encrypt the payload (and thus add an AEAD tag)
  [@inline_let]
  let aead_length = if has_sym_key' then aead_tag_vsv else 0 in
  // In practice, will always be smaller
  if l1 + aead_length > max_size_t then false
  else
    begin
    [@inline_let]
    let max1 = min2 (plain_message_check_max nc) (max_size_t - l1 - aead_length) in
    FStar.UInt32.(payload_len <=^ size max1) &&
    begin
    (**) assert(size_v payload_len + aead_tag_size <= max_size_t);
    FStar.UInt32.(msg_len =^ size (l1 + aead_length) +^ payload_len)
    end
    end
#pop-options

// Given a payload_len, compute the length of a message.
// Return true if succeeded, false if the lengths are not valid.
// Note that we don't prove much about the computed length value.
// For simplicity, we make the function pure, because otherwise
// we can't extract it without post-processing.
// The reason is that, as it is recursive, we need to wrap it in
// a normalization call. In case the function is stateful, the lifting
// makes the normalization call useless.
// Also, note that it doesn't extract correctly if i is strict. It may be
// dangerous, but as we only use [compute_messagei_len] in
// [mk_state_t_compute_next_message_len], it is ok.
// TODO: investigate why the unfolding gets stuck if i is strict
// TODO: rewrite to not use options (possible if we apply the normalization
// on partial applications)
[@@ (strict_on_arguments [0]); noextract_to "Karamel"] inline_for_extraction noextract
val compute_messagei_len
  (isc:isconfig) (i : nat) (step : size_t)
  (payload_len : size_t) :
  Pure (option size_t)
  (requires (
    i <= List.Tot.length (isc_get_pattern isc).messages /\
    size_v step >= i))
  (ensures (fun s ->
    let nc = isc_get_config isc in
    let pat = isc_get_pattern isc in
    (**) normalize_term_spec(List.Tot.length pat.messages);
    match s with
    | Some s ->
      size_v step < List.Tot.length pat.messages /\
      size_v s = 
        size_v payload_len + compute_message_length nc pat (size_v step)
    | None -> True))
  (decreases (List.Tot.length (isc_get_pattern isc).messages - i))

let rec compute_messagei_len isc i step payload_len =
  (**) normalize_term_spec(List.Tot.length (isc_get_pattern isc).messages);
  [@inline_let] let n = with_onorm #nat (List.Tot.length (isc_get_pattern isc).messages) in
  // This if will reduce at extraction
  if i = n then None
  else if size i = step then
    begin
    [@inline_let] let nc = isc_get_nc isc in
    [@inline_let]
    let l1 = with_onorm #nat (compute_message_length (isc_get_config isc) (isc_get_pattern isc) i) in
    // This if will reduce at extraction
    if l1 > max_size_t then None
    else
      begin
      [@inline_let]
      let max1 = min2 (plain_message_check_max nc) (max_size_t - l1) in
      (**) assert(max1 <= max_size_t);
      if FStar.UInt32.(payload_len <=^ size max1) then
        Some (FStar.UInt32.(payload_len +^ size l1))
      else None
      end
    end
  else
    norm [zeta; delta_only[`%compute_messagei_len]; iota; primops]
      (compute_messagei_len isc (i+1) step payload_len)

let mk_state_t_compute_next_message_len #isc #initiator st payload_len out =
  (**) normalize_term_spec(List.Tot.length (isc_get_pattern isc).messages);
  match st with
  | IMS_Handshake step _ _ _ _ _ _ _ _ _ _ ->
    [@inline_let]
    let res =
      norm [zeta; delta_only[`%compute_messagei_len]; iota; primops]
        (compute_messagei_len isc 0 step payload_len)
    in
    begin match res with
    | Some l -> B.upd out 0ul l; true
    | _ -> false
    end
  | IMS_Transport _ _ _ _ _ _ ->
    if FStar.UInt32.(payload_len <=^ size (max_size_t - aead_tag_vsv)) then
      begin
      B.upd out 0ul FStar.UInt32.(payload_len +^ aead_tag_vs);
      true
      end
    else false

[@@ (strict_on_arguments [0]); noextract_to "Karamel"] inline_for_extraction noextract
val compute_payloadi_len
  (isc:isconfig) (i : nat) (step : size_t)
  (message_len : size_t) :
  Pure (option size_t)
  (requires (
    i <= List.Tot.length (isc_get_pattern isc).messages /\
    size_v step >= i))
  (ensures (fun s ->
    let nc = isc_get_config isc in
    let pat = isc_get_pattern isc in
    (**) normalize_term_spec(List.Tot.length pat.messages);
    match s with
    | Some s ->
      size_v step < List.Tot.length pat.messages /\
      size_v s + compute_message_length nc pat (size_v step) = 
        size_v message_len
    | None -> True))
  (decreases (List.Tot.length (isc_get_pattern isc).messages - i))

let rec compute_payloadi_len isc i step message_len =
  (**) normalize_term_spec(List.Tot.length (isc_get_pattern isc).messages);
  [@inline_let] let n = with_onorm #nat (List.Tot.length (isc_get_pattern isc).messages) in
  // This if will reduce at extraction
  if i = n then None
  else if size i = step then
    begin
    [@inline_let] let nc = isc_get_nc isc in
    [@inline_let]
    let l1 = with_onorm #nat (compute_message_length (isc_get_config isc) (isc_get_pattern isc) i) in
    // This if will reduce at extraction
    if l1 > max_size_t then None
    else
      begin
      if FStar.UInt32.(message_len >=^ size l1) then
        Some (FStar.UInt32.(message_len -^ size l1))
      else
        None
      end
    end
  else
    norm [zeta; delta_only[`%compute_payloadi_len]; iota; primops]
      (compute_payloadi_len isc (i+1) step message_len)

let mk_state_t_compute_next_decrypted_payload_length #isc #initiator st message_len payload_len =
  (**) normalize_term_spec(List.Tot.length (isc_get_pattern isc).messages);
  match st with
  | IMS_Handshake step _ _ _ _ _ _ _ _ _ _ ->
    [@inline_let]
    let res =
      norm [zeta; delta_only[`%compute_payloadi_len]; iota; primops]
        (compute_payloadi_len isc 0 step message_len)
    in
    begin match res with
    | Some l -> B.upd payload_len 0ul l; true
    | _ -> false
    end
  | IMS_Transport _ _ _ _ _ _ ->
    if FStar.UInt32.(message_len >=^ size aead_tag_vsv) then
      begin
      B.upd payload_len 0ul FStar.UInt32.(message_len -^ aead_tag_vs);
      true
      end
    else false

let mk_state_t_compute_next_decrypted_payload_length_option
  #isc #initiator st message_len =
  (**) normalize_term_spec(List.Tot.length (isc_get_pattern isc).messages);
  match st with
  | IMS_Handshake step _ _ _ _ _ _ _ _ _ _ ->
    norm [zeta; delta_only[`%compute_payloadi_len]; iota; primops]
      (compute_payloadi_len isc 0 step message_len)
  | IMS_Transport _ _ _ _ _ _ ->
    if FStar.UInt32.(message_len >=^ size aead_tag_vsv) then
      Some (FStar.UInt32.(message_len -^ aead_tag_vs))
    else None

let state_t_set_stuck #isc st =
  [@inline_let] let n = with_onorm(List.Tot.length (isc_get_pattern isc).messages) in
  match st with
  | IMS_Handshake step k ck h spriv spub epriv epub rs re psk ->
    IMS_Handshake (size (n+1))  k ck h spriv spub epriv epub rs re psk
  | IMS_Transport h recv_tpt_msg send_key send_nonce receive_key receive_nonce ->
    IMS_Transport h recv_tpt_msg send_key send_nonce receive_key receive_nonce

let state_t_set_stuck_with_invariant #isc h st = state_t_set_stuck #isc st

(*** Handshake write message *)

let send_message_pre
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
  (st : valid_hsm nc smi)
  (outlen : size_t) (out : lbuffer uint8 outlen)
  (h : mem) : Type0 =
  send_message_tokens_with_payload_pre #nc smi initiator is_psk pattern payload_len payload
                                       st outlen out h

let send_message_post
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
  (st : valid_send_message_hsm nc is_psk pattern smi)
  (outlen : size_t) (out : lbuffer uint8 outlen) 
  (h0 : mem) (r : rtype (send_message_return_type smi is_psk pattern)) (h1 : mem) =
  send_message_tokens_with_payload_post #nc smi initiator is_psk pattern payload_len payload
                                        st outlen out h0 r h1    

let send_message_pre_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
  (st : valid_hsm nc smi)
  (outlen : size_t) (out : lbuffer uint8 outlen)
  (h : mem) = ()

let send_message_post_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_len : plain_message_len_t nc) (payload : plain_message_t nc payload_len)
  (st : valid_send_message_hsm nc is_psk pattern smi)
  (outlen : size_t) (out : lbuffer uint8 outlen) 
  (h0 : mem) (r : rtype (send_message_return_type smi is_psk pattern)) (h1 : mem) = ()

#push-options "--z3rlimit 500 --ifuel 1"
let mk_state_t_handshake_write #isc smi i send_message
                               payload_len payload st outlen out =
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let initiator = i%2=0 in
  [@inline_let]
  let is_psk = with_onorm (check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let]
  let pattern = isc_get_pattern isc in
  [@inline_let]
  let pat = with_onorm (List.Tot.index pattern.messages i) in
  if not (check_input_output_len nc smi is_psk pat payload_len outlen) then Fail CInput_size
  else
    begin
    (**) assert(size_v payload_len + aead_tag_size + hash_vsv nc <= max_size_t);
    (**) assert(size_v outlen = (message_vsv nc smi is_psk pat (size_v payload_len) <: nat));

    [@inline_let]
    let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk = st in
    [@inline_let]
    let hsm = state_t_get_hsm st in

    (**) let h0 = ST.get () in

    begin
    (**) let nc = isc_get_nc isc in
    (**) assert(send_message_tokens_with_payload_pre smi initiator is_psk pat
    (**)                                        payload_len payload hsm outlen out h0)
    end;

    let res = send_message payload_len payload hsm outlen out in
    (**) let h1 = ST.get () in
    if is_success res then
      begin
      
      (* The proof fails if we omit this block of assertions *)
      begin
      (**) let st0_v = handshake_state_t_v_with_smi h0 st smi in
      (**) let payload_v = as_seq h0 payload in
      (**) let message_pat = pat in
      (**) let status' = Handshake_receive (i+1) in
      (**) let hs_st = IS_Handshake?.st st0_v.Spec.st_hs_state in
      (**) let res =
      (**)   send_message_tokens_with_payload st0_v.Spec.st_initiator is_psk
      (**)                                    message_pat payload_v hs_st
      (**) in
      (**) assert(Res? res);
      (**) let Res (msg_v, st1_v) = res in
      (**) assert(msg_v == as_seq h1 out)
      end;
      
      [@inline_let] let step' = UInt32.add step (UInt32.uint_to_t 1) in
      [@inline_let]
      let st1 =
        IMS_Handshake step' st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk in
      Res st1
      end
    else
      match to_prim_error_code res with
      | CDH_error -> Fail CDH_error
    end
#pop-options

(*** Handshake read message *)

let receive_message_pre
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_outlen : plain_message_len_t nc)
  (payload_out : plain_message_t nc payload_outlen)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h : mem) : Type0 =
  receive_message_tokens_with_payload_pre
    #nc smi initiator is_psk pattern payload_outlen payload_out st inlen input h

let receive_message_post
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_outlen : plain_message_len_t nc)
  (payload_out : plain_message_t nc payload_outlen)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h0 : mem) (r : rtype (receive_message_return_type smi is_psk pattern))
  (h1 : mem) : Type0 =
  receive_message_tokens_with_payload_post
    #nc smi initiator is_psk pattern payload_outlen payload_out st inlen input h0 r h1

let receive_message_pre_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_outlen : plain_message_len_t nc)
  (payload_out : plain_message_t nc payload_outlen)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h : mem) = ()

let receive_message_post_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (payload_outlen : plain_message_len_t nc)
  (payload_out : plain_message_t nc payload_outlen)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h0 : mem) (r : rtype (receive_message_return_type smi is_psk pattern))
  (h1 : mem) = ()

let receive_message_tokens_nout_pre
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (st : valid_hsm nc smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h : mem) : Type0 =
  Impl.Noise.SendReceive.receive_message_tokens_nout_pre
    #nc smi initiator is_psk pattern st inlen input h

let receive_message_tokens_nout_post
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t)
  (input : lbuffer uint8 inlen)
  (h0 : mem) (r : rtype (receive_tokens_return_type smi is_psk pattern))
  (h1 : mem) =
  Impl.Noise.SendReceive.receive_message_tokens_nout_post
    #nc smi initiator is_psk pattern st inlen input h0 r h1

let receive_message_tokens_nout_pre_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (st : valid_hsm nc smi)
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h : mem) = ()

let receive_message_tokens_nout_post_lem
  (#nc : iconfig) (smi : meta_info) (initiator is_psk : bool)
  (pattern : list message_token)
  (st : valid_receive_message_hsm nc is_psk pattern smi)
  (inlen : size_t)
  (input : lbuffer uint8 inlen)
  (h0 : mem) (r : rtype (receive_tokens_return_type smi is_psk pattern))
  (h1 : mem) = ()


(**** receive_lookup: no S *)

[@@ noextract_to "Karamel"] noextract
val mk_receive_lookup_message_tokens_with_payload_no_S_no_vst_pre :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem -> Type0

let mk_receive_lookup_message_tokens_with_payload_no_S_no_vst_pre
  #isc smi i payload_outlen payload_out st inlen input =
  fun h0 ->
  let initiator = (i%2=1) in

  state_t_handshake_invariant_stateful h0 st /\

  live h0 payload_out /\
  live h0 input /\
  LB.disjoint payload_out input /\
  B.loc_disjoint (state_t_footprint st) (B.loc_buffer (payload_out <: buffer uint8)) /\
  B.loc_disjoint (state_t_footprint st) (B.loc_buffer (input <: buffer uint8)) /\

  get_aead_pre (isc_get_nc isc) /\
  get_dh_pre (isc_get_nc isc) /\
  get_hash_pre (isc_get_nc isc) /\

  mk_state_t_handshake_read_no_S_smi_pre isc smi i /\

  handshake_state_t_valid_values initiator i st false

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_receive_lookup_message_tokens_with_payload_no_S_no_vst :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> receive_message:receive_message_st isc smi i
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->

  Stack s_error_code_or_success
  (requires (fun h0 ->
    mk_receive_lookup_message_tokens_with_payload_no_S_no_vst_pre
      #isc smi i payload_outlen payload_out st inlen input h0))

  (ensures (fun h0 res h1 ->
    B.(modifies (loc_union (state_t_core_footprint st)
                           (loc_buffer (payload_out <: buffer uint8))) h0 h1) /\

    begin
    let pattern = isc_get_pattern isc in
    let pat = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    let post_smi = receive_message_update_smi is_psk pat smi in
    let st0_v = handshake_state_t_v_with_smi h0 st smi in
    let input_v = as_seq h0 input in
    let res_v' =
      receive_lookup_message_tokens_with_payload_no_S_no_vst #(isc_get_sc isc) input_v
                                                             pat st0_v in
    match res with
    | CSuccess ->
      Res? res_v' /\
      begin
      let Res (payload'_v, st1'_v) = res_v' in
      res = CSuccess /\
      handshake_state_t_v_with_smi h1 st post_smi == st1'_v /\
      as_seq h1 payload_out == payload'_v
      end
    | _ ->
      (check_input_output_len (isc_get_nc isc) smi is_psk pat payload_outlen inlen ==> Fail? res_v') /\
      state_t_handshake_invariant_stateful h1 st
    | _ -> False
    end))

#push-options "--z3rlimit 400"
let mk_receive_lookup_message_tokens_with_payload_no_S_no_vst
  #isc smi i receive_message
  payload_outlen payload_out st inlen input =
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let initiator = i%2=1 in
  [@inline_let]
  let is_psk = with_onorm (check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let]
  let pattern = isc_get_pattern isc in
  [@inline_let]
  let pat = with_onorm (List.Tot.index pattern.messages i) in

  if not (check_input_output_len nc smi is_psk pat payload_outlen inlen) then CInput_size
  else
    begin
    (**) assert(size_v payload_outlen + aead_tag_size + hash_vsv nc <= max_size_t);
    (**) assert(size_v inlen = (message_vsv nc smi is_psk pat (size_v payload_outlen) <: nat));

    [@inline_let]
    let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk = st in
    [@inline_let]
    let hsm = state_t_get_hsm st in

    (**) let h0 = ST.get () in

    begin
    (**) let nc = isc_get_nc isc in
    (**) assert(receive_message_tokens_with_payload_pre smi initiator is_psk pat
    (**)                                        payload_outlen payload_out hsm inlen input h0)
    end;

    let res = receive_message payload_outlen payload_out hsm inlen input in
    (**) let h1 = ST.get () in
    if is_success res then
      begin
      
      [@inline_let] let step' = UInt32.add step (UInt32.uint_to_t 1) in

      begin
      (**) let pattern = isc_get_pattern isc in
      (**) let pat = List.Tot.index pattern.messages i in
      (**) let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
      (**) let post_smi = receive_message_update_smi is_psk pat smi in
      (**) let st0_v = handshake_state_t_v_with_smi h0 st smi in
      (**) let hs_st = IS_Handshake?.st st0_v.Spec.st_hs_state in
      (**) let input_v = as_seq h0 input in
      (**) let res = receive_message_tokens_with_payload initiator is_psk pat input_v hs_st in
      (**) assert(Res? res);
      (**) let Res (payload_v, st1_v) = res in
      (**) assert(payload_v == as_seq h1 payload_out);
      (**) let res' =
      (**)   receive_lookup_message_tokens_with_payload_no_S_no_vst #(isc_get_sc isc) input_v
      (**)                                                          pat st0_v in
      (**) assert(Res? res');
      (**) let payload'_v, st1'_v = Res?.v res' in
      (**) let st1_v = handshake_state_t_v_with_smi h1 st post_smi in
      (**) let IS_Handshake status hs_st_v = st1_v.Spec.st_hs_state in
      (**) let IS_Handshake status' hs_st'_v = st1'_v.Spec.st_hs_state in
      (**) assert(status' == status);
      (**) assert(hs_st'_v == hs_st_v)
      end;

      CSuccess
      end
    else
      // Note: can only be CDH_error or Decrypt_error
      convert_subtype res
    end
#pop-options

[@@ noextract_to "Karamel"] noextract
val mk_receive_lookup_message_tokens_with_payload_no_S_pre :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem -> Type0

let mk_receive_lookup_message_tokens_with_payload_no_S_pre
  #isc smi i vfunct vst payload_outlen payload_out st inlen input =
  fun h0 ->
  let vst_footprint = vfunct.vst.St.footprint vst in

  mk_receive_lookup_message_tokens_with_payload_no_S_no_vst_pre
    #isc smi i payload_outlen payload_out st inlen input h0 /\

  vfunct.vst.St.invariant h0 vst /\
  
  B.loc_disjoint (state_t_footprint st) vst_footprint /\
  B.loc_disjoint vst_footprint (B.loc_buffer (payload_out <: buffer uint8)) /\
  B.loc_disjoint vst_footprint (B.loc_buffer (input <: buffer uint8))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_receive_lookup_message_tokens_with_payload_no_S :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> receive_message:receive_message_st isc smi i
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->

  Stack s_error_code_or_success
  (requires (fun h0 ->
    mk_receive_lookup_message_tokens_with_payload_no_S_pre
      #isc smi i vfunct vst payload_outlen payload_out st inlen input h0))

  (ensures (fun h0 res h1 ->
    B.(modifies (loc_union (state_t_core_footprint st)
                           (loc_buffer (payload_out <: buffer uint8))) h0 h1) /\

    (* This equality is an immediate consequence of the framing rules,
     * but we add it here for convenience *)
    vfunct.vst.St.v () h1 vst ==
      vfunct.vst.St.v () h0 vst /\

    vfunct.vst.St.v () h1 vst == vfunct.vst.St.v () h0 vst /\ // sanity check

    begin
    let pattern = isc_get_pattern isc in
    let pat = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    let post_smi = receive_message_update_smi is_psk pat smi in
    let vst0_v = vfunct.vst.St.v () h0 vst in
    let st0_v = handshake_state_t_v_with_smi h0 st smi in
    let input_v = as_seq h0 input in
    let res_v' =
      receive_lookup_message_tokens_with_payload_no_S #(isc_get_sc isc) input_v
                                                      pat st0_v vst0_v in
    begin match res with
    | CSuccess -> //, Res (pinfo, payload'_v, st1'_v) ->
      Res? res_v' /\
      begin
      let Res (pinfo, payload'_v, st1'_v) = res_v' in
      handshake_state_t_v_with_smi h1 st post_smi == st1'_v /\
      as_seq h1 payload_out == payload'_v /\
      state_t_handshake_invariant_stateful h1 st /\
      pinfo == None
      end
    | _ ->
      (check_input_output_len (isc_get_nc isc) smi is_psk pat payload_outlen inlen ==> Fail? res_v') /\
      state_t_handshake_invariant_stateful h1 st
    | _ -> False
    end
    end))

let mk_receive_lookup_message_tokens_with_payload_no_S
  #isc smi i receive_message
  vfunct vst payload_outlen payload_out st inlen input =
  (**) let h0 = ST.get () in
  let r =
    mk_receive_lookup_message_tokens_with_payload_no_S_no_vst
      #isc smi i receive_message
      payload_outlen payload_out st inlen input
  in
  (**) let h1 = ST.get () in
  (**) vfunct.vst.St.frame_invariant
  (**)   B.(loc_union (state_t_core_footprint st)
  (**)   (loc_buffer (payload_out <: buffer uint8))) vst h0 h1;
  r

(**** receive_lookup: with S *)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_check_remote_static :
     #isc:isconfig
  -> smi:meta_info
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> st:handshake_state_m (isc_get_nc isc) ->
  ST bool

  (requires (fun h0 ->
    let recv_psk = isc_lookups_psk isc in
    let psk = hsm_get_preshared st in

    hsm_inv h0 st smi /\
    vfunct.vst.St.invariant h0 vst /\
    (isc_get_pinfo isc).St.invariant h0 pinfo /\

    (recv_psk ==> not (g_is_null (hsm_get_preshared st))) /\
    smi.hsf.rs /\
    not smi.hsf.psk /\
            
    begin
    let vst_footprint = vfunct.vst.St.footprint vst in
    let st_loc = hsm_loc st in
    let pinfo_loc = (isc_get_pinfo isc).St.footprint pinfo in
    B.all_disjoint [vst_footprint; st_loc; pinfo_loc]
    end))

  (ensures (fun h0 res h1 ->
    let recv_psk = isc_lookups_psk isc in
    let psk = hsm_get_preshared st in
    let psk_loc =
      if recv_psk then B.loc_buffer (psk <: buffer uint8) else B.loc_none in
    B.(modifies
        (loc_union psk_loc
          ((isc_get_pinfo isc).St.footprint pinfo)) h0 h1) /\

    hsm_inv h1 st smi /\
    vfunct.vst.St.invariant h1 vst /\
    (isc_get_pinfo isc).St.invariant h1 pinfo /\
    ((isc_get_pinfo isc).St.freeable h0 pinfo ==>
     (isc_get_pinfo isc).St.freeable h1 pinfo) /\

    vfunct.vst.St.v () h1 vst == vfunct.vst.St.v () h0 vst /\ // sanity check

    begin
    let vst0_v = vfunct.vst.St.v () h0 vst in
    let st0_v = eval_handshake_state_m h0 st smi in
    let post_smi = smi_set_psk (recv_psk || smi.hsf.psk) smi in
    match Spec.check_remote_static (Stateful_vstate?.validate_spec vfunct)
                                   vst0_v st0_v with
    | Fail _ ->
      not res /\
      eval_handshake_state_m h1 st smi == st0_v
    | Res (st1_v, pinfo_v) ->
      res /\
      eval_handshake_state_m h1 st post_smi == st1_v /\
      pinfo_v == (isc_get_pinfo isc).St.v () h1 pinfo
    | _ -> False
    end))

let mk_check_remote_static #isc smi vfunct vst pinfo st =
  (**) let h0 = ST.get () in
  [@inline_let] let recv_psk = isc_lookups_psk isc in
  [@inline_let]
  let psk : preshared_key_t_or_unit recv_psk =
    if recv_psk then hsm_get_preshared st else () in
  [@inline_let]
  let validate = Stateful_vstate?.validate vfunct in
  let r = validate vst (hsm_get_remote_static st) pinfo psk in
  (**) let h1 = ST.get () in
  begin
  (**) let recv_psk = isc_lookups_psk isc in
  (**) let psk = hsm_get_preshared st in
  (**) let psk_loc =
  (**)   if recv_psk then B.loc_buffer (psk <: buffer uint8) else B.loc_none in
  (**) let l = B.loc_union psk_loc ((isc_get_pinfo isc).St.footprint pinfo) in
  (**) vfunct.vst.St.frame_invariant l vst h0 h1
  end;
  r

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_end :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> initiator:bool
  -> is_psk:bool
  -> tokens:list message_token
  -> receive_end:
     receive_message_st_aux (isc_get_nc isc)
                            (smi_set_psk (isc_lookups_psk isc || smi.hsf.psk) smi)
                            initiator is_psk tokens
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:handshake_state_m (isc_get_nc isc)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->

  ST (s_result_code unit)
  (requires (fun h0 ->
    let recv_psk = isc_lookups_psk isc in

    hsm_inv h0 st smi /\
    vfunct.vst.St.invariant h0 vst /\
    (isc_get_pinfo isc).St.invariant h0 pinfo /\

    live h0 payload_out /\
    live h0 input /\
    
    begin
    let payload_out_loc = B.loc_buffer (payload_out <: buffer uint8) in
    let input_loc = B.loc_buffer (input <: buffer uint8) in
    let vst_footprint = vfunct.vst.St.footprint vst in
    let st_loc = hsm_loc st in
    let pinfo_loc = (isc_get_pinfo isc).St.footprint pinfo in
    B.all_disjoint [payload_out_loc; input_loc; vst_footprint; st_loc; pinfo_loc]
    end /\

    get_aead_pre (isc_get_nc isc) /\
    get_dh_pre (isc_get_nc isc) /\
    get_hash_pre (isc_get_nc isc) /\

    smi.hsf.rs /\
    not smi.hsf.psk /\
    (recv_psk ==> not (g_is_null (hsm_get_preshared st))) /\

    begin
    let nc = isc_get_nc isc in
    let post_smi =
      receive_message_update_smi is_psk tokens (smi_or_set_psk recv_psk smi) in
    let has_sym_key = smi.hsf.sk in
    let tks_msg_length =
      size_v inlen - tokens_message_size (get_config nc) has_sym_key is_psk tokens in

    is_valid_hsm post_smi st /\
    check_receive_message_smi (smi_or_set_psk recv_psk smi) initiator is_psk tokens /\
    tokens_message_size (get_config nc) smi.hsf.sk is_psk tokens <= max_size_t /\
    
    is_plain_message_length (get_config nc) (size_v payload_outlen) /\
    size_v payload_outlen + aead_tag_size + hash_vsv nc <= max_size_t /\
    size_v inlen = message_vsv nc smi is_psk tokens (size_v payload_outlen) /\
    is_hashable_size (get_config nc) tks_msg_length

    end))

  (ensures (fun h0 res h1 ->
    B.(modifies (loc_union (hsm_loc_only_remote st)
      (loc_union (loc_buffer ((hsm_get_preshared st) <: buffer uint8))
        (loc_union (loc_buffer (payload_out <: buffer uint8))
                   ((isc_get_pinfo isc).St.footprint pinfo)))) h0 h1) /\

    // TODO: see comment in mk_state_t_handshake_read_no_S_post
    live h1 payload_out /\ live h1 input /\

    hsm_inv h1 st smi /\
    vfunct.vst.St.invariant h1 vst /\
    (isc_get_pinfo isc).St.invariant h1 pinfo /\

    (* Those equalities are an immediate consequence of the framing rules,
     * but we add them here for convenience *)
    ((isc_get_pinfo isc).St.freeable h0 pinfo ==>
     (isc_get_pinfo isc).St.freeable h1 pinfo) /\

    vfunct.vst.St.v () h1 vst == vfunct.vst.St.v () h0 vst /\ // sanity check

    begin
    let recv_psk = isc_lookups_psk isc in
    let post_smi =
      receive_message_update_smi is_psk tokens (smi_or_set_psk recv_psk smi) in
    let vst0_v = vfunct.vst.St.v () h0 vst in
    let st0_v = eval_handshake_state_m h0 st smi in
    let input_v = as_seq h0 input in
    let res_v' =
      hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_end
        #(isc_get_sc isc) input_v tokens initiator is_psk st0_v vst0_v in
    begin match res with
    | Res () ->
      Res? res_v' /\
      begin
      let Res (pinfo_v, payload'_v, st1'_v) = res_v' in
      eval_handshake_state_m h1 st post_smi == st1'_v /\
      as_seq h1 payload_out == payload'_v /\
      Some ((isc_get_pinfo isc).St.v () h1 pinfo) == pinfo_v
      end
    | Fail _ -> Fail? res_v'
    | _ -> False
    end
    end))

#push-options "--z3rlimit 200"
let mk_hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_end
  #isc smi initiator is_psk tokens receive_end vfunct vst
  pinfo payload_outlen payload_out st inlen input =
  (**) let h0 = ST.get () in
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let has_sym_key = with_onorm(smi.hsf.sk) in
  [@inline_let] let has_sym_key' = with_onorm(tokens_update_sym_key_flag has_sym_key is_psk tokens) in
  [@inline_let] let recv_psk = isc_lookups_psk isc in
  [@inline_let]
  let psk : preshared_key_t_or_unit recv_psk =
    if recv_psk then hsm_get_preshared st else () in

  [@inline_let] let smi1 = with_norm(smi_or_set_psk recv_psk smi) in
  [@inline_let] let smi2 = with_norm(receive_message_update_smi is_psk tokens smi1) in

  (**) assert(
  (**)   size_v inlen >=
  (**)   tokens_message_size (get_config nc) has_sym_key is_psk tokens
  (**)   + opt_encrypt_size has_sym_key' 0);

  if mk_check_remote_static #isc smi vfunct vst pinfo st then
    begin
    (**) let h1 = ST.get () in
    (**) assert(check_receive_message_smi smi1 initiator is_psk tokens);
    (**) assert(
    (**)   receive_message_tokens_with_payload_pre smi1 initiator is_psk
    (**)     tokens payload_outlen payload_out st inlen input h1);

    let r2 = receive_end payload_outlen payload_out st inlen input in
    (**) let h2 = ST.get () in

    begin
    (**) let vst0_v = vfunct.vst.St.v () h0 vst in
    (**) let st0_v = eval_handshake_state_m h0 st smi in
    (**) let st1_v = eval_handshake_state_m h1 st smi1 in
    (**) let vst1_v = vfunct.vst.St.v () h1 vst in
    (**) let pinfo_v = (isc_get_pinfo isc).St.v () h1 pinfo in
    (**) let check_remote_static_res =
    (**)   check_remote_static (Stateful_vstate?.validate_spec vfunct)
    (**)           vst0_v st0_v in
    (**) assert(
    (**)   match check_remote_static_res with
    (**)   | Res (st1'_v, pinfo'_v) ->
    (**)     st1_v == st1'_v /\
    (**)     pinfo_v == pinfo'_v
    (**)   | _ -> False);
    (**) let st2_v = eval_handshake_state_m h2 st smi2 in
    (**) let input_v = as_seq h0 input in
    (**) let res_v = receive_message_tokens_with_payload initiator is_psk tokens input_v st1_v in
    (**) assert(
    (**)   if is_success r2 then
    (**)     Res? res_v /\
    (**)     begin
    (**)     let Res (payload_out_v', st2'_v) = res_v in
    (**)     is_success r2 /\G.reveal st2_v == st2'_v /\
    (**)     Lib.Sequence.length payload_out_v' == Lib.Sequence.length h2.[|payload_out|] /\
    (**)     Lib.Sequence.equal payload_out_v' h2.[|payload_out|]
    (**)     end
    (**)   else True);
    (**) assert(
    (**)   hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_end
    (**)     #(isc_get_sc isc) input_v tokens initiator is_psk st0_v vst0_v ==
    (**)   begin
    (**)   match check_remote_static_res with
    (**)   | Fail e -> Fail e
    (**)   | Res (hs_st'', pinfo) ->
    (**)     match receive_message_tokens_with_payload initiator is_psk tokens input_v hs_st'' with
    (**)     | Fail e -> Fail (error_to_s_error e)
    (**)     | Res (msg'', hs_st''') -> Res (Some pinfo, msg'', hs_st''')
    (**)   end)
    end;

    begin
    (**) let l = B.loc_union (hsm_loc_only_remote st) (B.loc_buffer (payload_out <: buffer uint8)) in
    (**) vfunct.vst.St.frame_invariant l vst h1 h2;
    (**) (isc_get_pinfo isc).St.frame_invariant l pinfo h1 h2;
    (**) vfunct.vst.St.frame_invariant l vst h1 h2;
    (**) St.opt_frame_freeable (isc_get_pinfo isc) l pinfo h1 h2
    end;

    if is_success r2 then Res ()
    else Fail (to_prim_error_code r2)
    end
  else
    Fail CRs_rejected_by_policy
#pop-options

(* In the following function, we don't do dynamic checks on purpose: it will be
 * wrapped into another function which will make the link between the "nout"
 * versions of the receive functions and the "classical" one, and will perform
 * the dynamic checks to prove the preconditions. *)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end :
     #isc:isconfig
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> initiator:bool
  -> is_psk:bool
  -> tokens_beg:list message_token
  -> tokens_end:list message_token
  -> receive_beg:receive_message_tokens_nout_st_aux (isc_get_nc isc) smi initiator is_psk tokens_beg
  -> receive_end:
    receive_message_st_aux (isc_get_nc isc)
                           (smi_or_set_psk (isc_lookups_psk isc) (receive_tokens_update_smi is_psk tokens_beg smi))
                           initiator is_psk tokens_end
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:handshake_state_m (isc_get_nc isc)
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->

  ST (s_result_code unit)
  (requires (fun h0 ->
    let recv_psk = isc_lookups_psk isc in

    hsm_inv h0 st smi /\
    vfunct.vst.St.invariant h0 vst /\
    (isc_get_pinfo isc).St.invariant h0 pinfo /\

    live h0 payload_out /\
    live h0 input /\
    
    begin
    let payload_out_loc = B.loc_buffer (payload_out <: buffer uint8) in
    let input_loc = B.loc_buffer (input <: buffer uint8) in
    let vst_footprint = vfunct.vst.St.footprint vst in
    let st_loc = hsm_loc st in
    let pinfo_loc = (isc_get_pinfo isc).St.footprint pinfo in
    B.all_disjoint [payload_out_loc; input_loc; vst_footprint; st_loc; pinfo_loc]
    end /\

    get_aead_pre (isc_get_nc isc) /\
    get_dh_pre (isc_get_nc isc) /\
    get_hash_pre (isc_get_nc isc) /\
    (recv_psk ==> not (g_is_null (hsm_get_preshared st))) /\

    begin
    let nc = isc_get_nc isc in
    let tokens = List.append tokens_beg tokens_end in
    let smi1 = receive_tokens_update_smi is_psk tokens_beg smi in
    let smi2 = smi_or_set_psk recv_psk smi1 in
    let post_smi = smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi) in
    let has_sym_key = smi.hsf.sk in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    let tks_msg_length =
      size_v inlen - tokens_message_size (get_config nc) has_sym_key is_psk tokens in
    
    List.Tot.mem S tokens /\
    splitAtFirstElem S tokens = (tokens_beg, tokens_end) /\
    isc_valid_meta_info isc post_smi /\
    is_valid_hsm post_smi st /\
    check_receive_message_smi smi initiator is_psk tokens_beg /\
    check_receive_message_smi smi2 initiator is_psk tokens_end /\
    tokens_message_size (get_config nc) smi.hsf.sk is_psk tokens <= max_size_t /\

    is_plain_message_length (get_config nc) (size_v payload_outlen) /\
    size_v payload_outlen + aead_tag_size + hash_vsv nc <= max_size_t /\
    size_v inlen = message_vsv nc smi is_psk tokens (size_v payload_outlen) /\
    is_hashable_size (get_config nc) tks_msg_length /\

    not smi1.hsf.psk /\
    smi1.hsf.rs

    end))

  (ensures (fun h0 res h1 ->
    B.(modifies
      (loc_union (hsm_loc_only_remote st)
      (loc_union (loc_buffer ((hsm_get_preshared st) <: buffer uint8))
      (loc_union (loc_buffer (payload_out <: buffer uint8))
                 ((isc_get_pinfo isc).St.footprint pinfo)))) h0 h1) /\

    // TODO: see comment in mk_state_t_handshake_read_no_S_post
    live h1 payload_out /\ live h1 input /\

    hsm_inv h1 st smi /\
    vfunct.vst.St.invariant h1 vst /\
    (isc_get_pinfo isc).St.invariant h1 pinfo /\

    ((isc_get_pinfo isc).St.freeable h0 pinfo ==>
     (isc_get_pinfo isc).St.freeable h1 pinfo) /\

    vfunct.vst.St.v () h1 vst == vfunct.vst.St.v () h0 vst /\ // sanity check

    begin
    let recv_psk = isc_lookups_psk isc in
    let tokens = List.Tot.append tokens_beg tokens_end in
    let post_smi = smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi) in
    let vst0_v = vfunct.vst.St.v () h0 vst in
    let st0_v = eval_handshake_state_m h0 st smi in
    let input_v = as_seq h0 input in
    let res_v' =
      hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end
        #(isc_get_sc isc) input_v tokens initiator is_psk st0_v vst0_v in

    begin match res,  res_v' with
    | Res (), Res (pinfo_v, payload'_v, st1'_v) ->
      eval_handshake_state_m h1 st post_smi == st1'_v /\
      as_seq h1 payload_out == payload'_v /\
      Some ((isc_get_pinfo isc).St.v () h1 pinfo) == pinfo_v
    | Fail _, Fail _ -> True
    | _ -> False
    end
    end))

#restart-solver
let decompose_receive_tokens_update_smi_lem_eq (recv_psk is_psk : bool)
                                               (tokens_beg tokens_end : list message_token)
                                               (smi : meta_info) :
  Lemma(
    let tokens = List.Tot.append tokens_beg tokens_end in
    let smi1 = receive_tokens_update_smi is_psk tokens_beg smi in
    let smi2 = smi_or_set_psk recv_psk smi1 in
    let smi3 = receive_message_update_smi is_psk tokens_end smi2 in
    let smi3' = smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi) in
    smi1.hsf.psk = smi.hsf.psk /\
    smi3 = smi3' /\
    tokens_update_sym_key_flag smi.hsf.sk is_psk tokens_beg = smi1.hsf.sk /\
    tokens_update_sym_key_flag smi2.hsf.sk is_psk tokens_end = smi3.hsf.sk) =
  let tokens = List.Tot.append tokens_beg tokens_end in
  let smi1 = receive_tokens_update_smi is_psk tokens_beg smi in
  let smi2 = smi_or_set_psk recv_psk smi1 in
  let smi3 = receive_message_update_smi is_psk tokens_end smi2 in
  let smi3' = smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi) in
  receive_tokens_update_smi_decompose_lem is_psk tokens_beg tokens_end smi;
  receive_tokens_update_hsf_frame_lem is_psk tokens_end smi1.hsf;  
  updt_sk_consistent_with_receive_tokens_update_hsf_lem is_psk tokens_beg smi.hsf;
  updt_sk_consistent_with_receive_tokens_update_hsf_lem is_psk tokens_end smi2.hsf

// TODO: this proof is too big
#restart-solver
#push-options "--z3rlimit 1000 --ifuel 0"
let mk_hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end
  #isc smi initiator is_psk tokens_beg tokens_end receive_beg receive_end
  vfunct vst pinfo payload_outlen payload_out st inlen input =
  (**) let h0 = ST.get () in
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let tokens = with_onorm(List.Tot.append tokens_beg tokens_end) in
  [@inline_let] let has_sym_key = with_onorm(smi.hsf.sk) in
  [@inline_let] let has_sym_key' = with_onorm(tokens_update_sym_key_flag has_sym_key is_psk tokens) in
  [@inline_let] let recv_psk = isc_lookups_psk isc in
  [@inline_let]
  let psk : preshared_key_t_or_unit recv_psk =
    if recv_psk then hsm_get_preshared st else () in

  (**) assert(
  (**)   size_v inlen >=
  (**)   tokens_message_size (get_config nc) has_sym_key is_psk tokens
  (**)   + opt_encrypt_size has_sym_key' 0);

  [@inline_let]
  let msg1_length : nat =
    with_onorm(tokens_message_size (get_config nc) has_sym_key is_psk tokens_beg) in
  (**) tokens_message_size_decompose_lem (get_config nc) has_sym_key is_psk tokens_beg tokens_end;
  (**) assert(msg1_length <= size_v inlen);
  (**) assert(msg1_length <= max_size_t);
  (**) assert(size_v inlen - msg1_length >= 0);
  [@inline_let]
  let msg1_len = size msg1_length in
  [@inline_let]
  let msg2_len = FStar.UInt32.(inlen -^ msg1_len) in

  let msg1 = sub input 0ul msg1_len in
  let msg2 = sub input msg1_len msg2_len in

  (**) let h1 = ST.get () in

  [@inline_let] let smi1 = with_onorm(receive_tokens_update_smi is_psk tokens_beg smi) in
  [@inline_let] let smi2 = with_onorm(smi_or_set_psk recv_psk smi1) in
  [@inline_let] let smi3 = with_onorm(receive_message_update_smi is_psk tokens_end smi2) in
  [@inline_let] let smi3' = with_onorm(smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi)) in

  (**) decompose_receive_tokens_update_smi_lem_eq recv_psk is_psk tokens_beg tokens_end smi;
  (**) assert((smi3 <: meta_info) = (smi3' <: meta_info));
  (**) assert(tokens_update_sym_key_flag smi.hsf.sk is_psk tokens_beg = smi1.hsf.sk);
  (**) assert(tokens_update_sym_key_flag smi2.hsf.sk is_psk tokens_end = smi3.hsf.sk);

  (**) tokens_update_sym_key_flag_decompose_lem has_sym_key is_psk tokens_beg tokens_end;
  (**) assert(
  (**)   size_v msg2_len ==
  (**)   tokens_message_size (isc_get_config isc) smi1.hsf.sk is_psk tokens_end +
  (**)   opt_encrypt_size (tokens_update_sym_key_flag smi1.hsf.sk is_psk tokens_end)
  (**)                    (size_v payload_outlen));

  (* Consume the first part of the message *)
  (**) assert(less_than smi1 smi3');
  (**) assert(is_valid_hsm (receive_message_update_smi is_psk tokens_beg smi) st);
  (**) assert(check_receive_message_smi smi initiator is_psk tokens_beg);
  (**) assert(receive_message_tokens_nout_pre smi initiator is_psk tokens_beg st msg1_len msg1 h1); // OK
  let r1 = receive_beg st msg1_len msg1 in

  (**) let h2 = ST.get () in
  (**) vfunct.vst.St.frame_invariant (hsm_loc_only_remote st) vst h1 h2;
  (**) (isc_get_pinfo isc).St.frame_invariant (hsm_loc_only_remote st) pinfo h1 h2;
  (**) St.opt_frame_freeable (isc_get_pinfo isc) (hsm_loc_only_remote st) pinfo h1 h2;

  (**) assert(isc_valid_meta_info isc smi1);
  (**) assert(check_receive_message_smi smi2 initiator is_psk tokens_end);

  (**) assert(not smi.hsf.psk);

  if is_success r1 then
    begin
    mk_hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_end
      #isc smi1 initiator is_psk tokens_end receive_end vfunct vst pinfo
      payload_outlen payload_out st msg2_len msg2
    end
  else
    Fail (to_prim_error_code r1)
#pop-options  

/// We separately define the different parts of the receive lookup function
/// precondition, so as to reuse it in several places.

val mk_receive_lookup_message_tokens_with_payload_with_S_stateful_pre :
     #isc:isconfig
  -> #initiator:bool
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc initiator{IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem -> Type0

let mk_receive_lookup_message_tokens_with_payload_with_S_stateful_pre
  #isc #initiator vfunct vst pinfo payload_outlen payload_out st inlen input =
  fun h0 ->

  state_t_handshake_invariant_stateful h0 st /\
  vfunct.vst.St.invariant h0 vst /\
  (isc_get_pinfo isc).St.invariant h0 pinfo /\

  live h0 payload_out /\
  live h0 input /\

  begin
  let payload_out_loc = B.loc_buffer (payload_out <: buffer uint8) in
  let input_loc = B.loc_buffer (input <: buffer uint8) in
  let vst_footprint = vfunct.vst.St.footprint vst in
  let st_loc = state_t_handshake_footprint st in
  let pinfo_loc = (isc_get_pinfo isc).St.footprint pinfo in
  B.all_disjoint [payload_out_loc; input_loc; vst_footprint; st_loc; pinfo_loc]
  end /\

  get_aead_pre (isc_get_nc isc) /\
  get_dh_pre (isc_get_nc isc) /\
  get_hash_pre (isc_get_nc isc)

[@@ noextract_to "Karamel"] noextract unfold
val mk_receive_lookup_message_tokens_nout_with_payload_with_S_pre :
     #isc:isconfig
  -> #initiator:bool
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc initiator{IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0:mem -> Type0

let mk_receive_lookup_message_tokens_nout_with_payload_with_S_pre
  #isc #initiator smi i vfunct vst pinfo payload_outlen payload_out st inlen input =
  fun h0 ->
  let recv_psk = isc_lookups_psk isc in

  mk_receive_lookup_message_tokens_with_payload_with_S_stateful_pre
    #isc vfunct vst pinfo payload_outlen payload_out st inlen input h0 /\

  mk_state_t_handshake_read_with_S_smi_pre isc smi i /\

  handshake_state_t_valid_values initiator i st false

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_receive_lookup_message_tokens_with_payload_with_S :
     #isc:isconfig
  -> #initiator:bool
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> impls:receive_split_message_impls isc smi i
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc initiator{IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->

  ST (s_result_code unit)
  (requires (fun h0 ->
   mk_receive_lookup_message_tokens_nout_with_payload_with_S_pre
     #isc smi i vfunct vst pinfo payload_outlen payload_out st inlen input h0))

  (ensures (fun h0 res h1 ->
    let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk = st in
    B.(modifies (loc_union (state_t_handshake_core_footprint st)
                (loc_union (loc_buffer (payload_out <: buffer uint8))
                           ((isc_get_pinfo isc).St.footprint pinfo))) h0 h1) /\

    // TODO: see comment in mk_state_t_handshake_read_no_S_post
    live h1 payload_out /\ live h1 input /\

    state_t_handshake_invariant_stateful h0 st /\
    vfunct.vst.St.invariant h1 vst /\
    (isc_get_pinfo isc).St.invariant h1 pinfo /\

    ((isc_get_pinfo isc).St.freeable h0 pinfo ==>
     (isc_get_pinfo isc).St.freeable h1 pinfo) /\

    vfunct.vst.St.v () h1 vst == vfunct.vst.St.v () h0 vst /\ // sanity check

    begin
    let recv_psk = isc_lookups_psk isc in
    let pattern = isc_get_pattern isc in
    let tokens = List.Tot.index pattern.messages i in
    let is_psk = check_hsk_is_psk (isc_get_pattern isc) in
    let post_smi = smi_or_set_psk recv_psk (receive_message_update_smi is_psk tokens smi) in
    let vst0_v = vfunct.vst.St.v () h0 vst in
    let st0_v = handshake_state_t_v_with_smi h0 st smi in
    let input_v = as_seq h0 input in
    let res_v' =
      receive_lookup_message_tokens_with_payload_with_S
        #(isc_get_sc isc) input_v tokens st0_v vst0_v in

    begin match res with
    | Res () ->
      Res? res_v' /\
      begin
      let Res (pinfo_v, payload'_v, st1'_v) = res_v' in
      handshake_state_t_v_with_smi h1 st post_smi == st1'_v /\
      as_seq h1 payload_out == payload'_v /\
      Some ((isc_get_pinfo isc).St.v () h1 pinfo) == pinfo_v /\
      state_t_invariant_stateful h1 st
      end
    | Fail _ ->
      (check_input_output_len (isc_get_nc isc) smi is_psk tokens payload_outlen inlen ==>
       Fail? res_v') /\
      state_t_invariant_stateful h1 st
    | _ -> False
    end
    end))

#restart-solver
#push-options "--z3rlimit 400"
let mk_receive_lookup_message_tokens_with_payload_with_S
  #isc #initiator smi i impls vfunct vst pinfo payload_outlen payload_out st inlen input =
  (**) let h0 = ST.get () in
  [@inline_let] let nc = isc_get_nc isc in
  [@inline_let] let recv_psk = isc_lookups_psk isc in
  [@inline_let] let pattern = isc_get_pattern isc in
  [@inline_let] let tokens = with_onorm(List.Tot.index pattern.messages i) in
  [@inline_let] let is_psk = with_onorm(check_hsk_is_psk (isc_get_pattern isc)) in
  [@inline_let] let tokens_beg = with_onorm(fst(splitAtFirstElem S tokens)) in
  [@inline_let] let tokens_end = with_onorm(snd(splitAtFirstElem S tokens)) in
  (**) splitAtFirstElem_append_lem S tokens;
  (**) assert(List.Tot.append tokens_beg tokens_end = tokens);
  [@inline_let] let receive_beg, receive_end = impls in

  [@inline_let] let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                      st_epriv st_epub st_rs st_re st_psk = st in
  [@inline_let] let hsm = state_t_get_hsm st in

  if not (check_input_output_len nc smi is_psk tokens payload_outlen inlen) then Fail CInput_size
  else
    begin

    begin
    (**) let has_sym_key = smi.hsf.sk in
    (**) let tks_msg_length = size_v inlen - tokens_message_size (get_config nc) has_sym_key is_psk tokens in
    (**) assert(is_plain_message_length (get_config nc) (size_v payload_outlen));
    (**) assert(size_v payload_outlen + aead_tag_size + hash_vsv nc <= max_size_t);
    (**) assert(size_v inlen = message_vsv nc smi is_psk tokens (size_v payload_outlen));
    (**) assert(is_hashable_size (get_config nc) tks_msg_length)
    end;

    begin
    (**) let vst0_v = vfunct.vst.St.v () h0 vst in
    (**) let st0_v = handshake_state_t_v_with_smi h0 st smi in
    (**) let input_v = as_seq h0 input in
    (**) receive_lookup_message_tokens_nout_with_payload_with_S_eq
    (**)  #(isc_get_sc isc) input_v tokens st0_v vst0_v
    end;

    mk_hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end
      #isc smi initiator is_psk tokens_beg tokens_end
      (convert_type receive_beg) (convert_type receive_end) vfunct vst
      pinfo payload_outlen payload_out hsm inlen input
    
    end
#pop-options

(**** handshake read *)

/// Sanity check: we have to duplicate some information between the .fst and the .fsti,
/// by merging some preconditions together. However, we want the resulting precondition
/// to be equivalent to the merged ones.
val mk_state_t_handshake_read_no_S_pre_eq_lem :
     #isc:isconfig{isc_has_valid_pattern isc}
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem -> Lemma
  (mk_state_t_handshake_read_no_S_pre #isc smi i vfunct vst payload_outlen payload_out st inlen input h0
   <==>
   (let initiator = (i%2 = 1) in
    mk_receive_lookup_message_tokens_with_payload_no_S_pre
      #isc smi i vfunct vst payload_outlen payload_out st inlen input h0))

let mk_state_t_handshake_read_no_S_pre_eq_lem =
  fun #isc smi i vfunct vst payload_outlen payload_out st inlen input h0 -> ()

let mk_state_t_handshake_read_no_S
  #isc smi i receive_message vfunct vst payload_outlen payload_out
  st inlen input =
  [@inline_let]
  let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk = st in
  
  let r =
    mk_receive_lookup_message_tokens_with_payload_no_S #isc smi
      i receive_message vfunct vst payload_outlen payload_out st inlen input
  in
  match r with
  | CSuccess ->
    [@inline_let] let step' = UInt32.add step (UInt32.uint_to_t 1) in
    [@inline_let]
    let st =
      IMS_Handshake step' st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk
    in
    Res st
  | _ -> Fail r

val mk_state_t_handshake_read_with_S_pre_lem :
     #isc:isconfig{isc_has_valid_pattern isc}
  -> smi:meta_info{isc_valid_meta_info isc smi}
  -> i:nat{i < List.Tot.length (isc_get_pattern isc).messages}
  -> vfunct:isc_validate isc
  -> vst:vfunct.vst.St.s ()
  -> pinfo:(isc_get_pinfo isc).St.s ()
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st:state_t isc (i%2=1){IMS_Handshake? st}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> h0 : mem
  -> Lemma
  (mk_state_t_handshake_read_with_S_pre
     #isc smi i vfunct vst pinfo payload_outlen payload_out st inlen input h0 <==>
   (let initiator = (i%2 = 1) in
    mk_receive_lookup_message_tokens_nout_with_payload_with_S_pre
      #isc smi i vfunct vst pinfo payload_outlen payload_out st inlen input h0))

let mk_state_t_handshake_read_with_S_pre_lem =
  fun #isc smi i vfunct vst pinfo payload_outlen payload_out st inlen input h0 -> ()

let mk_state_t_handshake_read_with_S
  #isc smi i impls vfunct vst pinfo payload_outlen payload_out
  st inlen input =
  [@inline_let]
  let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk = st in
  
  let r =
    mk_receive_lookup_message_tokens_with_payload_with_S #isc smi
      i impls vfunct vst pinfo payload_outlen payload_out st inlen input
  in
  match r with
  | Res () ->
    [@inline_let] let step' = UInt32.add step (UInt32.uint_to_t 1) in
    [@inline_let]
    let st =
      IMS_Handshake step' st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk
    in
    Res st
  | Fail e -> Fail e

(*** Split *)

#restart-solver
#push-options "--z3rlimit 600"
let mk_state_t_split #isc #initiator smi split r st =
  (**) let h0 = ST.get () in

  [@inline_let]
  let IMS_Handshake step st_k st_ck st_h st_spriv st_spub
                    st_epriv st_epub st_rs st_re st_psk = st in

  let k1 : lbuffer uint8 aead_key_vs = (B.malloc r (u8 0) aead_key_vs <: buffer uint8) in
  let k2 : lbuffer uint8 aead_key_vs = (B.malloc r (u8 0) aead_key_vs <: buffer uint8) in
  (**) let h1 = ST.get () in
  (**) assert(B.(modifies loc_none h0 h1));

  [@inline_let]
  let ss = mk_ssm st_k st_ck st_h in
  split ss k1 k2;
  (**) let h2 = ST.get () in
  (**) assert(
  (**)   let ss_v = eval_symmetric_state_m h1 ss smi.hsf.sk smi.nonce in
  (**)   let cst1_v, cst2_v = Spec.Noise.Base.Definitions.split ss_v in
  (**)   eval_cipher_state_m h2 k1 true 0 == cst1_v /\
  (**)   eval_cipher_state_m h2 k2 true 0 == cst2_v);
  (**) assert(
  (**)   let ss_v = eval_symmetric_state_m h1 ss smi.hsf.sk smi.nonce in
  (**)   let cst1_v, cst2_v = Spec.Noise.Base.Definitions.split ss_v in
  (**)   Some (B.as_seq h2 (k1 <: buffer uint8) <: aead_key) == cst1_v.Spec.Noise.Base.k /\
  (**)   Some (B.as_seq h2 (k2 <: buffer uint8) <: aead_key) == cst2_v.Spec.Noise.Base.k);

  (**) [@inline_let] let kl : G.erased _ =
  (**)   (B.loc_union (B.loc_addr_of_buffer (k1 <: buffer uint8))
  (**)                (B.loc_addr_of_buffer (k2 <: buffer uint8))) in
  (**) assert(B.(modifies ((B.loc_union (state_t_core_footprint st) kl)) h1 h2));
  (**) B.(modifies_only_not_unused_in (state_t_core_footprint st) h0 h2);
  (**) assert(B.(modifies (state_t_core_footprint st) h0 h2));

  begin
  (**) let st0_v = handshake_state_t_v_with_smi h0 st smi in
  (**) let cs1, cs2 = Spec.Noise.Base.split (IS_Handshake?.st st0_v.Spec.st_hs_state).sym_state in
  (**) assert(Some?.v cs1.Spec.Noise.Base.k == as_seq h2 k1);
  (**) assert(Some?.v cs2.Spec.Noise.Base.k == as_seq h2 k2)
  end;

  [@inline_let]
  let (send_key, receive_key) : aead_key_t & aead_key_t = if initiator then k1, k2 else k2, k1 in

  [@inline_let]
  let send_key_or_unit : type_or_unit aead_key_t (isc_get_send isc) =
    if isc_get_send isc then send_key else () in
  [@inline_let]
  let send_nonce : type_or_unit aead_nonce_t (isc_get_send isc) =
    if isc_get_send isc then UInt64.uint_to_t 0 else () in
  [@inline_let]
  let receive_key_or_unit : type_or_unit aead_key_t (isc_get_receive isc) =
    if isc_get_receive isc then receive_key else () in
  [@inline_let]
  let receive_nonce : type_or_unit aead_nonce_t (isc_get_receive isc) =
    if isc_get_receive isc then UInt64.uint_to_t 0 else () in

  if isc_get_send isc then () else B.free (send_key <: buffer uint8);
  if isc_get_receive isc then () else B.free (receive_key <: buffer uint8);

  (**) let h3 = ST.get () in
  (**) assert(B.(modifies kl h2 h3));
  (**) B.(modifies_only_not_unused_in (state_t_core_footprint st) h0 h3);
  (**) assert(B.(modifies (state_t_core_footprint st) h0 h3));

  B.free (st_k <: buffer uint8);
  B.free (st_ck <: buffer uint8);
  lbuffer_or_unit_free st_epriv;
  lbuffer_or_unit_free st_epub;
  lbuffer_or_unit_free st_rs;
  lbuffer_or_unit_free st_re;
  lbuffer_or_unit_free st_psk;

  (**) let h4 = ST.get () in

  [@inline_let]
  let st' = IMS_Transport st_h (bool_to_bool_or_gbool false) send_key_or_unit send_nonce
                          receive_key_or_unit receive_nonce in

  (**) assert(state_t_transport_invariant_stateful h3 st');

  begin
  (**) let st0_v = handshake_state_t_v_with_smi h0 st smi in
  (**) let st1_v = transport_state_t_v h4 st' in
  (**) let r_v = Spec.split st0_v in
  (**) assert(Res? r_v);
  (**) let st1'_v = Res?.v r_v in
  (**) assert(st1'_v.Spec.st_pattern == st1_v.Spec.st_pattern);
  (**) assert(st1'_v.Spec.st_initiator == st1_v.Spec.st_initiator);
  (**) assert(IS_Transport? st1'_v.Spec.st_hs_state);
  (**) assert(IS_Transport? st1_v.Spec.st_hs_state);
  (**) let IS_Transport h recv_tpt send receive = st1_v.Spec.st_hs_state in
  (**) let IS_Transport h' recv_tpt' send' receive' = st1'_v.Spec.st_hs_state in
  (**) assert(h == h');
  (**) assert(recv_tpt = recv_tpt');
  (**) assert(send == send');
  (**) assert(receive == receive')
  end;

  st'
#pop-options

(*** Transport *)
(**** Utilities*)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let aaead_check_size (a : aead_alg) (plen clen : size_t) :
  Pure bool (requires True)
  (ensures (fun b ->
    b <==>
    begin
    size_v plen <= aaead_max_input a /\
    size_v plen + aead_tag_size <= max_size_t /\
    size_v clen = size_v plen + aead_tag_size
    end)) =
  (**) assert(aaead_max_input a + aead_tag_size <= max_size_t);
  [@inline_let] let b = 
  FStar.UInt32.(plen <=^ size (with_onorm(aaead_max_input a))) &&
  FStar.UInt32.(clen =^ plen +^ size aead_tag_size)
  in
  (**) assert(b ==> size_v plen <= aaead_max_input a);
  (**) assert(b ==> size_v plen + aead_tag_size <= max_size_t);
  (**) assert(b ==> size_v clen = size_v plen + aead_tag_size);
  b

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let aead_check_size (nc : iconfig) (plen clen : size_t) =
  aaead_check_size (get_aead_alg (get_config nc)) plen clen

(**** Transport write *)

let mk_state_t_transport_write #isc encrypt plen p clen c st =
  [@inline_let]
  let IMS_Transport h recv_tpt_msg send_key send_nonce receive_key receive_nonce = st in
  if not (aead_check_size (isc_get_nc isc) plen clen) then Fail CInput_size
  else if UInt64.(send_nonce >=^ uint_to_t (with_onorm saturated_nonce_value))
  then Fail CSaturated_nonce
  else
    begin
    (**) let h0 = ST.get () in
    (**) assert(Seq.equal (B.as_seq h0 (null #MUT #uint8)) (Seq.empty #uint8));
    encrypt send_key send_nonce 0ul (null #MUT #uint8) plen p c;
    [@inline_let]
    let st = IMS_Transport h recv_tpt_msg send_key FStar.UInt64.(send_nonce +^ uint_to_t 1)
                           receive_key receive_nonce in
    Res st
    end

(**** Transport read *)

#push-options "--ifuel 1"
let mk_state_t_transport_read #isc decrypt plen p clen c st =
  [@inline_let]
  let IMS_Transport h recv_tpt_msg send_key send_nonce receive_key receive_nonce = st in
  if not (aead_check_size (isc_get_nc isc) plen clen) then Fail CInput_size
  else if UInt64.(receive_nonce >=^ uint_to_t (with_onorm saturated_nonce_value))
  then Fail CSaturated_nonce
  else
    begin
    (**) assert(size_v plen <= aead_max_input (isc_get_config isc) + aead_tag_size);
    (**) assert(size_v clen >= aead_tag_size);
    (**) assert(size_v clen <= aead_max_input (isc_get_config isc) + aead_tag_size);
    (**) let h0 = ST.get () in
    (**) assert(Seq.equal (B.as_seq h0 (null #MUT #uint8)) (Seq.empty #uint8));
    match decrypt receive_key receive_nonce 0ul (null #MUT #uint8) plen p c with
    | CDecrypt_error -> Fail CDecrypt_error
    | CSuccess ->
      (**) let h1 = ST.get () in
      [@inline_let]
      let st = IMS_Transport h (bool_to_bool_or_gbool true) send_key send_nonce
                             receive_key FStar.UInt64.(receive_nonce +^ uint_to_t 1) in
      Res st
    end
#pop-options
