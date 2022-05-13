module Impl.Noise.API.Session

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

module B = LowStar.Buffer
module BS = Lib.ByteSequence
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module G = FStar.Ghost

open Spec.Noise.API.Device.Definitions
open Spec.Noise.API.DState.Definitions

friend Spec.Noise.API.DState.Definitions
friend Spec.Noise.API.State.Definitions

open Spec.Noise.API.Session
friend Spec.Noise.API.Session
module Spec = Spec.Noise.API.Session

open Impl.Noise.Types
open Impl.Noise.API.Device
friend Impl.Noise.API.Device
open Impl.Noise.API.DState
friend Impl.Noise.API.DState
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate
open Spec.Noise
open Spec.Noise.PatternsSecurity
open Spec.Noise.API.MetaInfo

open Lib.RandomSequence
open Lib.RandomBuffer.System

open Lib.Memzero0
open FStar.UInt32
open Meta.Noise

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

// Align the .fst and the .fsti
let _align_fsti = ()

(*** Session *)
type session_t idc = dstate_t idc
type session_p_or_null idc = dstate_p_or_null idc

let session_p_g_is_null #idc sn = dstate_p_g_is_null sn

let session_p_v #idc h sn =
  let s = dstate_p_v h sn in
  assert(Some? (ac_levels (dstate_get_pattern s)));
  s

let session_p_invariant #idc h sn = dstate_p_invariant h sn
let session_p_is_gstuck #idc h sn = dstate_p_is_gstuck h sn
let session_p_is_stuck #idc st = dstate_p_is_stuck st

let session_p_live #idc h sn = dstate_p_live h sn
let session_p_is_null #idc sn = dstate_p_is_null sn

let session_p_g_get_device #idc h sn = dstate_p_g_get_device h sn
let session_p_rid_of #idc sn = dstate_p_rid_of sn

let session_p_g_has_static (#idc : valid_idc) (h : mem) (sn : session_p idc) : GTot bool =
  let initiator = session_p_g_is_initiator h sn in
  isc_get_s (idc_get_isc idc initiator)

let session_p_g_handshake_get_static :
     #idc:valid_idc
  -> h:mem
  -> sn:session_p idc{session_p_g_is_handshake h sn}
  -> GTot (
       let initiator = session_p_g_is_initiator h sn in
       sprivate_key_t idc initiator & spublic_key_t idc initiator) =
  fun #idc h sn ->
  dstate_p_g_handshake_get_static h sn

let device_p_owns_session_p #idc h dvp sn =
  session_p_g_get_device h sn == dvp /\
  begin
  if session_p_g_is_handshake h sn && session_p_g_has_static h sn then
    let spriv, spub = session_p_g_handshake_get_static h sn in
    let dv_spriv, dv_spub = device_p_g_get_static h dvp in
    lbuffer_or_unit_to_opt_lseq h spriv == lbuffer_or_unit_to_opt_lseq h dv_spriv /\
    lbuffer_or_unit_to_opt_lseq h spub == lbuffer_or_unit_to_opt_lseq h dv_spub
  else
    True
  end

let device_p_owns_session_p_lem #idc h dvp sn = ()

let session_p_invariant_live_lem #idc h sn = ()

let session_p_frame_invariant #idc l sn h0 h1 =
  dstate_p_frame_invariant l sn h0 h1

let session_p_frame_invariant_update_device #idc l sn dvp h0 h1 =
  dstate_p_frame_invariant_update_device #idc l sn dvp h0 h1

let session_p_or_null_frame_invariant #idc l sn dvp h0 h1 =
  dstate_p_or_null_frame_invariant #idc l sn dvp h0 h1

let session_p_or_null_frame_invariant_update_device #idc l sn dvp h0 h1 =
  dstate_p_or_null_frame_invariant_update_device #idc l sn dvp h0 h1

let session_p_g_get_device_disjoint_regions #idc sn h0 =
  dstate_p_g_get_device_disjoint_regions #idc sn h0

let session_p_recall_region #idc sn =
  dstate_p_recall_region sn

(**** Session utilities *)

let mk_session_p_get_status #idc sn =
  mk_dstate_p_get_status sn

let mk_session_p_compute_next_message_len #idc out sn payload_len =
  mk_dstate_p_compute_next_message_len #idc out sn payload_len

let mk_session_p_get_hash #idc out sn =
  mk_dstate_p_get_hash #idc out sn

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val valid_idc_handshake_pattern_no_empty_message
  (idc : valid_idc)
  (i : nat{i < List.Tot.length (idc_get_pattern idc).messages}) :
  Lemma (compute_message_length idc i > 0)

let valid_idc_handshake_pattern_no_empty_message idc i =
  Impl.Noise.API.State.StateMachine.check_pattern_messagei_lem (idc_get_pattern idc) i;
  compute_min_message_length_lem (idc_get_config idc) (idc_get_pattern idc) i

let mk_session_p_get_id #idc sn = mk_dstate_p_get_id sn
let mk_session_p_get_info #idc out sn = mk_dstate_p_get_info out sn
let mk_session_p_get_peer_id #idc sn = mk_dstate_p_get_peer_id sn
let mk_session_p_get_peer_info #idc out sn = mk_dstate_p_get_peer_info out sn

let mk_session_p_reached_max_security #idc snp =
  [@inline_let]
  let pattern = idc_get_pattern idc in
  [@inline_let]
  let num_msgs = with_onorm #nat (List.Tot.length pattern.messages) in
  let sn = B.index snp.stp 0ul in
  match sn with
  | DS_Initiator sn_state _ _ _ _ _ _ _ ->
    [@inline_let] let initiator = true in
    [@inline_let]
    let sends_last_handshake = with_onorm #bool (sends_last_handshake initiator pattern) in
    begin match sn_state with
    | IMS_Transport _ recv_tpt_msg _ _ _ _ ->
      if num_msgs > 1 then
        if sends_last_handshake then
          bool_or_gbool_to_bool recv_tpt_msg false
        else true
      else true
    | IMS_Handshake _ _ _ _ _ _ _ _ _ _ _ -> false
    end
  | DS_Responder sn_state _ _ _ _ _ _ _ ->
    [@inline_let] let initiator = false in
    [@inline_let]
    let sends_last_handshake = with_onorm #bool (sends_last_handshake initiator pattern) in
    begin match sn_state with
    | IMS_Transport _ recv_tpt_msg _ _ _ _ ->
      if num_msgs > 1 then
        if sends_last_handshake then
          bool_or_gbool_to_bool recv_tpt_msg false
        else true
      else true
    | IMS_Handshake _ _ _ _ _ _ _ _ _ _ _ -> false
    end


(**** Encapsulated messages *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let clevel_greater_than (l0 l1 : conf_level_t) :
  Pure bool (requires True)
  (ensures (fun b -> b = (Spec.clevel_greater_than (UInt8.v l0) (UInt8.v l1)))) =
  let open FStar.UInt8 in
  (l1 >=^ uint_to_t 2 && l0 >=^ l1) ||
  (l1 = uint_to_t 1 && (l0 = l1 || l0 >=^ uint_to_t 3)) ||
  (l1 = uint_to_t 0)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let alevel_greater_than (l0 l1 : auth_level_t) :
  Pure bool (requires True)
  (ensures (fun b -> b = (Spec.alevel_greater_than (UInt8.v l0) (UInt8.v l1)))) =
  FStar.UInt8.(l0 >=^ l1)

val encap_message_t : Type0
[@CAbstractStruct]
inline_for_extraction // inline the projectors
noeq type encap_message_t = {
  em_ac_level : ac_level_t;
  em_message_len : size_t;
  em_message : lbuffer uint8 em_message_len;
}

noeq type encap_message_p_or_null = {
  emp : B.pointer_or_null encap_message_t;
  emp_r : HS.rid;
}

let encap_message_p_g_is_null emp =
  B.g_is_null emp.emp

let encap_message_p_live h emp =
  B.live h emp.emp

let encap_message_p_null = { emp = B.null; emp_r = root; }
let encap_message_p_null_is_live h = ()

let encap_message_p_is_null emp =
  B.is_null emp.emp

let encap_message_p_rid_of emp =
  emp.emp_r

val encap_message_t_invariant (h : HS.mem) (em : encap_message_t) : GTot Type0
let encap_message_t_invariant h em =
  live h em.em_message /\
  (if B.g_is_null (em.em_message <: buffer uint8) then True
   else B.freeable (em.em_message <: buffer uint8))

let encap_message_p_invariant h emp =
  let em = B.deref h emp.emp in
  encap_message_t_invariant h em /\
  is_eternal_region emp.emp_r /\
  emp.emp_r <> root /\
  B.live h emp.emp /\
  B.freeable emp.emp /\
  begin
  let p_l = B.loc_addr_of_buffer emp.emp in
  let msg_l =
    if B.g_is_null (em.em_message <: buffer uint8)
    then B.loc_buffer (em.em_message <: buffer uint8) // Yes, we need that...
    else B.loc_addr_of_buffer (em.em_message <: buffer uint8)
  in
  B.(loc_disjoint p_l msg_l) /\
  region_includes emp.emp_r p_l /\
  region_includes emp.emp_r msg_l
  end

let encap_message_p_frame_invariant l emp h0 h1 = ()
let encap_message_p_or_null_frame_invariant l emp h0 h1 = ()
let encap_message_p_invariant_implies_live h emp = ()

val encap_message_t_v (h : HS.mem) (em : encap_message_t) : GTot encap_message
let encap_message_t_v h em =
  let lvl_v = ac_level_t_v em.em_ac_level in
  let msg_v = as_seq h em.em_message in
  Mkencap_message lvl_v msg_v

let encap_message_p_v h emp =
  let em = B.deref h emp.emp in
  encap_message_t_v h em

let encap_message_p_free emp =
  let em = B.index emp.emp 0ul in
  if not (B.is_null (em.em_message <: buffer uint8))
  then B.free (em.em_message <: buffer uint8);
  B.free emp.emp

/// Internal helper
[@@ noextract_to "Karamel"] inline_for_extraction noextract  
val pack_message_with_level :
     r:HS.rid
  -> level:ac_level_t
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  ST encap_message_p
  (requires (fun h0 ->
    is_eternal_region r /\
    live h0 msg))
  (ensures (fun h0 emp h1 ->
    B.(modifies loc_none h0 h1) /\
    region_includes r (encap_message_p_region_of emp) /\
    encap_message_p_invariant h1 emp /\
    encap_message_p_v h1 emp ==
      Mkencap_message (ac_level_t_v level) (as_seq h0 msg)))

let pack_message_with_level r0 level msg_len msg =
  let r = ST.new_region r0 in
  let msg' = lbuffer_malloc_copy_also_empty r (u8 0) msg in
  [@inline_let] let lvl = level in
  [@inline_let] let em =
  {
    em_ac_level = level;
    em_message_len = msg_len;
    em_message = msg';
  }
  in
  let emp_p = B.malloc r em 1ul in
  {
    emp = emp_p;
    emp_r = r;
  }

let pack_message_with_conf_level r0 requested_conf_level msg_len msg =
  pack_message_with_level r0 (Conf_level requested_conf_level) msg_len msg

let pack_message r0 msg_len msg =
  pack_message_with_conf_level r0 max_conf_level msg_len msg

let unpack_message_with_auth_level r out_msg_len out_msg requested_auth_level emp =
  let em = B.index emp.emp 0ul in
  let ok =
    if em.em_message_len = 0ul then true
    else
      match em.em_ac_level with
      | Auth_level l -> alevel_greater_than l requested_auth_level
      | _ -> false
  in
  if ok then
    begin
    let msg = lbuffer_malloc_copy_also_empty #uint8 #em.em_message_len r (u8 0) em.em_message in
    (**) let h1 = ST.get () in
    (**) begin
    (**) assert(Seq.equal (as_seq h1 msg) (as_seq h1 em.em_message))
    (**) end;
    B.upd out_msg_len 0ul em.em_message_len;
    B.upd out_msg 0ul msg;
    true
    end
  else
    begin
    B.upd out_msg 0ul null;
    false
    end

let unpack_message r out_msg_len out_msg emp =
  unpack_message_with_auth_level r out_msg_len out_msg max_auth_level emp

let unsafe_unpack_message r out_ac_level out_msg_len out_msg emp =
  let em = B.index emp.emp 0ul in
  let msg = lbuffer_malloc_copy_also_empty #uint8 #em.em_message_len r (u8 0) em.em_message in
  B.upd out_ac_level 0ul em.em_ac_level;
  B.upd out_msg_len 0ul em.em_message_len;
  B.upd out_msg 0ul msg

/// Helper for internal use only
[@@ noextract_to "Karamel"] inline_for_extraction noextract  
val pack_message_with_auth_level :
     r:HS.rid
  -> auth_level:auth_level_t
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  ST encap_message_p
  (requires (fun h0 ->
    is_eternal_region r /\
    live h0 msg))
  (ensures (fun h0 emp h1 ->
    B.(modifies loc_none h0 h1) /\
    region_includes r (encap_message_p_region_of emp) /\
    encap_message_p_invariant h1 emp /\
    encap_message_p_v h1 emp ==
      Spec.pack_message_with_auth_level (UInt8.v auth_level) (as_seq h0 msg)))

let pack_message_with_auth_level r auth_level msg_len msg =
  pack_message_with_level r (Auth_level auth_level) msg_len msg

(*** Session: create/free *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract  
let mk_session_p_create_uses_e_no_alloc_post :
     #idc:valid_idc
  -> initiator:bool // This parameter is meta
  -> r:HS.rid
  -> dvp:device_p idc // TODO: may be none in the future
  -> epriv:private_key_t (idc_get_nc idc)
  -> epub:public_key_t (idc_get_nc idc)
  -> pid:opt_pid_t idc initiator
  -> h0:mem
  -> sn:session_p_or_null idc
  -> h1:mem -> GTot Type0 =
  fun #idc initiator r dvp epriv epub pid h0 sn h1 ->
  let entr_loc = Lib.Buffer.loc entropy_p in
  let epriv_loc = B.loc_buffer (epriv <: buffer uint8) in
  let epub_loc = B.loc_buffer (epub <: buffer uint8) in
  let l = B.(loc_union (loc_union (device_p_region_of dvp) entr_loc) (loc_union epriv_loc epub_loc)) in
  B.(modifies l h0 h1) /\
  session_p_live h1 sn /\
  device_p_invariant h1 dvp /\
  device_p_get_cstate h1 dvp == device_p_get_cstate h0 dvp /\
  device_p_g_get_static h1 dvp == device_p_g_get_static h0 dvp /\
  device_p_no_removal dvp h0 h1 /\
  begin
  let dv_v = device_p_v h0 dvp in
  let pid_v = opt_pid_v pid in
  let entr0 = B.deref h0 (entropy_p <: B.buffer (G.erased entropy)) in
  let res_v = create_session dv_v initiator entr0 pid_v in
  if not (session_p_g_is_null sn) then
    Res? (fst res_v) /\
    begin
    let Res (st'_v, dv'_v), entr' = res_v in
    session_p_invariant h1 sn /\
    session_p_g_is_handshake h1 sn /\ // Not sure it is useful
    session_p_g_is_initiator h1 sn = initiator /\
    region_includes r (session_p_region_of sn) /\
    device_p_owns_session_p h1 dvp sn /\
    not (session_p_is_gstuck h1 sn) /\
    device_p_v h1 dvp == dv'_v /\
    session_p_v h1 sn == st'_v /\
    G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr'
    end
  else
    let _, entr' = res_v in
    device_p_v h1 dvp == device_p_v h0 dvp /\
    // Note that the device is left unchanged as a consequence of the modifies clause
    G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr'
  end

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type mk_session_p_create_uses_e_no_alloc_st (idc : valid_idc) =
     initiator:bool // This parameter is meta
  -> r:HS.rid
  -> dvp:device_p idc // TODO: may be none in the future
  -> epriv:private_key_t (idc_get_nc idc)
  -> epub:public_key_t (idc_get_nc idc)
  -> pid:opt_pid_t idc initiator ->
  ST (session_p_or_null idc)
  (requires (fun h0 ->
    let pattern = idc_get_pattern idc in

    device_p_invariant h0 dvp /\
    live h0 epriv /\
    live h0 epub /\
    live h0 entropy_p /\

    ST.is_eternal_region r /\

    isc_get_e (idc_get_isc idc initiator) = true /\

    begin
    let r_loc = region_to_loc r in
    let dv_loc = device_p_region_of dvp in
    let entr_loc = B.loc_buffer (entropy_p <: buffer (G.erased entropy)) in
    let epriv_loc = B.loc_addr_of_buffer (epriv <: buffer uint8) in
    let epub_loc = B.loc_addr_of_buffer (epub <: buffer uint8) in
    B.all_disjoint [dv_loc; r_loc; entr_loc; epriv_loc; epub_loc]
    end /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))

  (ensures (fun h0 sn h1 ->
   mk_session_p_create_uses_e_no_alloc_post initiator r dvp epriv epub pid h0 sn h1))

/// [mk_session_p_create] but with [uses_e = true] and no allocation (otherwise,
/// proofs explode).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_create_uses_e_no_alloc :
     #idc : valid_idc
  -> ssi:ss_impls (idc_get_nc idc)
  -> initialize:initialize_handshake_state_st (idc_get_nc idc) ->
  mk_session_p_create_uses_e_no_alloc_st idc

#restart-solver
#push-options "--z3rlimit 100"
let mk_session_p_create_uses_e_no_alloc #idc ssi initialize initiator r dvp epriv epub pid =
  [@inline_let] let nc = idc_get_nc idc in
  (**) let h0 = ST.get () in
  crypto_random epriv (private_key_vs nc);
  (**) let h1 = ST.get () in
  
  let res = idh_sp (ssi_get_prims ssi) epub epriv in
  (**) let h2 = ST.get () in
  begin
  (**) let entr_loc = Lib.Buffer.loc entropy_p in
  (**) let epriv_loc = B.loc_buffer (epriv <: buffer uint8) in
  (**) let epub_loc = B.loc_buffer (epub <: buffer uint8) in
  (**) let l = B.loc_union entr_loc (B.loc_union epriv_loc epub_loc) in
  (**) device_p_frame_invariant l dvp h0 h2
  end;

  match res with
  | CSuccess ->
    let res = mk_dstate_p_create ssi initialize initiator r dvp epriv epub pid in
    (**) let h3 = ST.get () in
    (**) assert(device_p_no_removal dvp h0 h2);
    (**) assert(device_p_no_removal dvp h2 h3);
    (**) device_p_no_removal_trans_lem dvp h0 h2 h3;
    (**) assert(device_p_no_removal dvp h0 h3);
    res
  | _ -> mk_dstate_p_null idc
#pop-options

/// This is really annoying. The above proof works fine, but a slight modification
/// makes Z3 go completely off tracks and fail, with no regards to the amount of
/// rlimit. Working with [mk_session_p_create_uses_e] is also very difficult,
/// because it needs a huge rlimit.
/// I have thus no better solution than introducing another helper.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_create_uses_e_no_alloc_memzero :
     #idc : valid_idc
  -> ssi:ss_impls (idc_get_nc idc)
  -> initialize:initialize_handshake_state_st (idc_get_nc idc) ->
  mk_session_p_create_uses_e_no_alloc_st idc

#restart-solver
#push-options "--z3rlimit 100"
let mk_session_p_create_uses_e_no_alloc_memzero =
  fun #idc ssi initialize initiator r dvp epriv epub pid ->

  B.recall (entropy_p <: buffer (G.erased entropy));

  [@inline_let] let nc = idc_get_nc idc in

  (**) let h0 = ST.get () in
  
  let res = mk_session_p_create_uses_e_no_alloc #idc ssi initialize initiator r dvp epriv epub pid in

  (**) let h1 = ST.get () in
  (**) assert(device_p_no_removal dvp h0 h1);
  B.recall (entropy_p <: buffer (G.erased entropy));

  begin
  let sn = res in
  let entr_loc = Lib.Buffer.loc entropy_p in
  let epriv_loc = B.loc_buffer (epriv <: buffer uint8) in
  let epub_loc = B.loc_buffer (epub <: buffer uint8) in
  let l = B.(loc_union (loc_union (device_p_region_of dvp) entr_loc) (loc_union epriv_loc epub_loc)) in
  assert(
    B.(modifies l h0 h1) /\
    session_p_live h1 sn /\
    device_p_invariant h1 dvp /\
    device_p_get_cstate h1 dvp == device_p_get_cstate h0 dvp /\
    device_p_g_get_static h1 dvp == device_p_g_get_static h0 dvp /\
    device_p_no_removal dvp h0 h1);
  let dv_v = device_p_v h0 dvp in
  let pid_v = opt_pid_v pid in
  let entr0 = B.deref h0 (entropy_p <: B.buffer (G.erased entropy)) in
  let res_v = create_session dv_v initiator entr0 pid_v in
  assert(
    if not (session_p_g_is_null sn) then
      Res? (fst res_v) /\
      begin
      let Res (st'_v, dv'_v), entr' = res_v in
      session_p_invariant h1 sn /\
      session_p_g_is_handshake h1 sn /\ // Not sure it is useful
      session_p_g_is_initiator h1 sn = initiator /\
      region_includes r (session_p_region_of sn) /\
      device_p_owns_session_p h1 dvp sn /\
      not (session_p_is_gstuck h1 sn) /\
      device_p_v h1 dvp == dv'_v /\
      session_p_v h1 sn == st'_v /\
      G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr'
      end
    else
      let _, entr' = res_v in
      device_p_v h1 dvp == device_p_v h0 dvp /\
      // Note that the device is left unchanged as a consequence of the modifies clause
      G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr')
  end;
  // Leave no sensitive information on the stack
  Lib.Memzero0.memzero #uint8 epriv (private_key_vs nc);
  Lib.Memzero0.memzero #uint8 epub (public_key_vs nc);

  (**) let h3 = ST.get () in

  begin
  (**) let epriv_loc = B.loc_buffer (epriv <: buffer uint8) in
  (**) let epub_loc = B.loc_buffer (epub <: buffer uint8) in
  (**) let l = B.(loc_union epriv_loc epub_loc) in
  (**) assert(B.(modifies l h1 h3));
  (**) device_p_frame_invariant l dvp h1 h3;
  (**) assert(device_p_no_removal dvp h1 h3);
  (**) device_p_no_removal_trans_lem dvp h0 h1 h3;
  (**) if not (session_p_g_is_null res) then
  (**)    session_p_frame_invariant l res h1 h3
  (**) else ();
  (**) assert(B.deref h3 (entropy_p <: B.buffer (G.erased entropy)) ==
  (**)   B.deref h1 (entropy_p <: B.buffer (G.erased entropy)))
  end;

  res
#pop-options


/// [mk_session_p_create] but with [uses_e = true] and allocation
/// of the ephemeral keys.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_create_uses_e :
     #idc:valid_idc
  -> ssi:ss_impls (idc_get_nc idc)
  -> initialize:initialize_handshake_state_st (idc_get_nc idc)
  -> initiator:bool // This parameter is meta
  -> r:HS.rid
  -> dvp:device_p idc
  -> pid:opt_pid_t idc initiator ->
  ST (session_p_or_null idc)
  (requires (fun h0 ->
    let pattern = idc_get_pattern idc in

    device_p_invariant h0 dvp /\
    ST.is_eternal_region r /\

    isc_get_e (idc_get_isc idc initiator) = true /\

    begin
    let r_loc = region_to_loc r in
    let dv_loc = device_p_region_of dvp in
    let entr_loc = Lib.Buffer.loc entropy_p in
    B.all_disjoint [dv_loc; r_loc; entr_loc]
    end /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))
  (ensures (fun h0 sn h1 ->
    session_p_create_post #idc initiator r dvp pid h0 sn h1))

#restart-solver
#push-options "--z3rlimit 200 --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"
let mk_session_p_create_uses_e #idc ssi initialize initiator r0 dvp pid =
  (**) let h0 = ST.get () in
  [@inline_let] let nc = idc_get_nc idc in

  (**) Lib.Buffer.recall entropy_p;
  (**) let r = new_region r0 in // We need r to be different from root
  (**) assert(B.loc_includes (region_to_loc r0) (region_to_loc r));
  (**) let h1 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h1;

  push_frame ();
  (**) let h2 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h2;

  // We need to recall the regions to show that they are disjoint from the stack
  (**) device_p_recall_region dvp;
  (**) recall_region r;
  (**) eternal_disjoint_from_tip h2 r;

  let epriv : lbuffer uint8 (private_key_vs nc) = create (private_key_vs nc) (u8 0) in

  (**) let h3 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h3;

  let epub : lbuffer uint8 (public_key_vs nc) = create (public_key_vs nc) (u8 0) in

  (**) let h4 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h4;

  let res = mk_session_p_create_uses_e_no_alloc_memzero ssi initialize initiator r dvp epriv epub pid in

  (**) Lib.Buffer.recall entropy_p;
  (**) let h5 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h5;

  pop_frame ();

  (**) let h6 = ST.get () in
  (**) Lib.Buffer.recall entropy_p;
  (**) B.loc_unused_in_not_unused_in_disjoint h6;
  (**) B.(modifies_only_not_unused_in (B.loc_union (device_p_region_of dvp) (Lib.Buffer.loc entropy_p)) h0 h4);
  (**) assert(B.(modifies loc_none h0 h4));
  (**) device_p_frame_invariant B.loc_none dvp h0 h4;
  (**) assert(B.(modifies (region_to_loc (get_tip h5)) h5 h6));
  (**) device_p_frame_invariant (region_to_loc (get_tip h5)) dvp h5 h6;
  (**) assert(device_p_no_removal dvp h0 h4);
  (**) assert(device_p_no_removal dvp h4 h5);
  (**) device_p_no_removal_trans_lem dvp h0 h4 h5;
  (**) assert(device_p_no_removal dvp h0 h5);
  (**) assert(device_p_no_removal dvp h5 h6);
  (**) device_p_no_removal_trans_lem dvp h0 h5 h6;
  (**) assert(device_p_no_removal dvp h0 h6);
  (**) assert(
  (**)   B.deref h5 (entropy_p <: B.buffer (G.erased entropy)) ==
  (**)    B.deref h6 (entropy_p <: B.buffer (G.erased entropy)));

  // Doesn't work with those assertions
  (**) begin
  (**) assert(
  (**)   B.(modifies (loc_union (device_p_region_of dvp) (Lib.Buffer.loc entropy_p)) h0 h6) /\
  (**)   session_p_or_null_invariant h6 res dvp /\
  (**)   device_p_invariant h6 dvp /\
  (**)   device_p_get_cstate h6 dvp == device_p_get_cstate h0 dvp /\
  (**)   device_p_g_get_static h6 dvp == device_p_g_get_static h0 dvp /\
  (**)   device_p_no_removal dvp h0 h6);
  (**) let dv_v = device_p_v h0 dvp in
  (**) let pid_v = opt_pid_v pid in
  (**) let entr0 = B.deref h0 (entropy_p <: B.buffer (G.erased entropy)) in
  (**) let res_v = create_session dv_v initiator entr0 pid_v in
  (**) assert(
  (**)   if not (session_p_g_is_null res) then
  (**)     Res? (fst res_v) /\
  (**)     begin
  (**)     let Res (sn'_v, dv'_v), entr' = res_v in
  (**)     session_p_g_is_handshake h6 res /\
  (**)     session_p_g_is_initiator h6 res = initiator /\
  (**)     region_includes r (session_p_region_of res) /\
  (**)     device_p_owns_session_p h6 dvp res /\
  (**)     not (session_p_is_gstuck h6 res) /\
  (**)     device_p_v h6 dvp == dv'_v /\
  (**)     session_p_v h6 res == sn'_v /\
  (**)     G.reveal (B.deref h6 (entropy_p <: B.buffer (G.erased entropy))) == entr'
  (**)     end
  (**)   else
  (**)     let _, entr' = res_v in
  (**)     device_p_v h6 dvp == device_p_v h0 dvp /\
  (**)     G.reveal (B.deref h6 (entropy_p <: B.buffer (G.erased entropy))) == entr')
  (**) end;

  res
#pop-options

let mk_session_p_create #idc #initiator ssi initialize r dvp pid =
  (**) let h0 = ST.get () in
  (**) Lib.Buffer.recall entropy_p;
  [@inline_let] let nc = idc_get_nc idc in
  [@inline_let] let uses_e = with_onorm(uses_e (idc_get_pattern idc) initiator) in
  (**) assert(isc_get_e (idc_get_isc idc initiator) = uses_e);

  if uses_e then
    mk_session_p_create_uses_e ssi initialize initiator r dvp pid
  else
    mk_dstate_p_create ssi initialize initiator r dvp () () pid

let mk_session_p_free #idc sn =
  mk_dstate_p_free sn

(*** Session: messages *)
(**** Session: messages: utilities *)

/// Reimplement in Low* some of the helpers used for the security levels checks
[@(strict_on_arguments [0; 1])]
noextract inline_for_extraction
val mk_compute_transport_conf_level
  (initiator : bool) (pattern : wfs_handshake_pattern)
  (received_transport_message :
    bool_or_gbool (save_received_transport initiator pattern)) :
  Pure conf_level_t
  (requires (
    Spec.Noise.API.State.Definitions.can_send initiator pattern))
  (ensures (fun cl ->
    match Spec.Noise.API.MetaInfo.compute_transport_conf_level
            initiator pattern (bool_or_gbool_to_gbool received_transport_message) with
    | Some cl_v -> UInt8.v cl = cl_v
    | None -> False))

#push-options "--fuel 1 --ifuel 1"
let mk_compute_transport_conf_level initiator pattern received_transport_message =
  [@inline_let]
  let levels = with_onorm #(list (auth_level & conf_level)) (Some?.v (ac_levels pattern)) in
  [@inline_let]
  let num_msgs = with_onorm #nat (List.Tot.length pattern.messages) in
  if num_msgs > 1 then // statically reduces
    [@inline_let]
    let sent_last_handshake = with_onorm #bool (sends_last_handshake initiator pattern) in
    if sent_last_handshake then // statically reduces
      if convert_type #_ #bool received_transport_message then
        UInt8.uint_to_t (with_onorm #nat (snd (List.Tot.index levels (num_msgs+1))))
      else
        UInt8.uint_to_t (with_onorm #nat (snd (List.Tot.index levels (num_msgs-1))))
    else
        UInt8.uint_to_t (with_onorm #nat (snd (List.Tot.index levels num_msgs)))
  else
    begin
    (**) assert(initiator);
    UInt8.uint_to_t (with_onorm #nat (snd (List.Tot.index levels (List.Tot.length pattern.messages - 1))))
    end
#pop-options

[@(strict_on_arguments [0; 1])]
noextract inline_for_extraction
val mk_compute_transport_auth_level
  (initiator : bool) (pattern : wfs_handshake_pattern) :
  Pure auth_level_t
  (requires (
    Spec.Noise.API.State.Definitions.can_receive initiator pattern))
  (ensures (fun al ->
    match Spec.Noise.API.MetaInfo.compute_transport_auth_level initiator pattern with
    | Some al_v -> UInt8.v al = al_v
    | None -> False))

#push-options "--fuel 1 --ifuel 1"
let mk_compute_transport_auth_level initiator pattern =
  [@inline_let]
  let levels = with_onorm #(list (auth_level & conf_level)) (Some?.v (ac_levels pattern)) in
  [@inline_let]
  let num_msgs = with_onorm #nat (List.Tot.length pattern.messages) in
  if num_msgs > 1 then // statically reduces
    [@inline_let]
    let sent_last_handshake = with_onorm #bool (sends_last_handshake initiator pattern) in
    if sent_last_handshake // statically reduces
    then UInt8.uint_to_t (with_onorm #nat (fst ((List.Tot.index levels num_msgs))))
    else UInt8.uint_to_t (with_onorm #nat (fst (List.Tot.index levels (num_msgs +1))))
  else
    begin
    (**) assert(not (initiator));
    UInt8.uint_to_t (with_onorm #nat (fst (List.Tot.index levels (List.Tot.length pattern.messages - 1))))
    end
#pop-options

[@(strict_on_arguments [0; 1])] // Won't reduce if i is strict
noextract inline_for_extraction
val mk_compute_handshake_conf_leveli
  (initiator : bool) (pattern : wfs_handshake_pattern)
  (i : nat) // meta
  (step : UInt32.t) :
  Pure conf_level_t
  (requires (
    i <= UInt32.v step /\ UInt32.v step < List.Tot.length pattern.messages /\
    Spec.Noise.API.State.Definitions.can_send initiator pattern))
  (ensures (fun cl ->
    let ac_levels = Some?.v (ac_levels pattern) in
    UInt8.v cl == snd (List.Tot.index ac_levels (UInt32.v step))))
  (decreases (List.Tot.length pattern.messages - i))

#push-options "--fuel 1 --ifuel 1"
let rec mk_compute_handshake_conf_leveli initiator pattern i step =
  [@inline_let]
  let levels = with_onorm #(list (auth_level & conf_level)) (Some?.v (ac_levels pattern)) in
  // Make sure there is no infinite unfolding at extraction time.
  // Also stop before we reach the end of the messages, because otherwise
  // it leads to invalid C code.
  if i = with_onorm #nat (List.Tot.length pattern.messages)-1 then
    UInt8.uint_to_t (with_onorm #nat (snd (List.Tot.index levels i)))
  // Actually, we could use initiator to skip some tests
  else if step = UInt32.uint_to_t i then
    UInt8.uint_to_t (with_onorm #nat (snd (List.Tot.index levels i)))
  else
    norm [zeta; iota; primops; delta_only[`%mk_compute_handshake_conf_leveli]]
    (mk_compute_handshake_conf_leveli initiator pattern (i+1) step)
#pop-options

[@(strict_on_arguments [0; 1])]
noextract inline_for_extraction
val mk_compute_handshake_conf_level
  (initiator : bool) (pattern : wfs_handshake_pattern)
  (step : UInt32.t) :
  Pure conf_level_t
  (requires (
    UInt32.v step < List.Tot.length pattern.messages /\
    Spec.Noise.API.State.Definitions.can_send initiator pattern))
  (ensures (fun cl ->
    let ac_levels = Some?.v (ac_levels pattern) in
    UInt8.v cl == snd (List.Tot.index ac_levels (UInt32.v step))))

let mk_compute_handshake_conf_level initiator pattern step =
  norm [zeta; iota; primops; delta_only[`%mk_compute_handshake_conf_leveli]]
  (mk_compute_handshake_conf_leveli initiator pattern 0 step)

[@(strict_on_arguments [0; 1])] // Won't reduce if i is strict
noextract inline_for_extraction
val mk_compute_handshake_auth_leveli
  (initiator : bool) (pattern : wfs_handshake_pattern)
  (i : nat) // meta
  (step : UInt32.t) :
  Pure auth_level_t
  (requires (
    i <= UInt32.v step /\ UInt32.v step < List.Tot.length pattern.messages /\
    Spec.Noise.API.State.Definitions.can_receive initiator pattern))
  (ensures (fun cl ->
    let ac_levels = Some?.v (ac_levels pattern) in
    UInt8.v cl == fst (List.Tot.index ac_levels (UInt32.v step))))
  (decreases (List.Tot.length pattern.messages - i))

#push-options "--fuel 1 --ifuel 1"
let rec mk_compute_handshake_auth_leveli initiator pattern i step =
  [@inline_let]
  let levels = with_onorm #(list (auth_level & conf_level)) (Some?.v (ac_levels pattern)) in
  // Make sure there is no infinite unfolding at extraction time.
  // Also stop before we reach the end of the messages, because otherwise
  // it leads to invalid C code.
  if i = with_onorm #nat (List.Tot.length pattern.messages)-1 then
    UInt8.uint_to_t (with_onorm #nat (fst (List.Tot.index levels i)))
  // Actually, we could use initiator to skip some tests
  else if step = UInt32.uint_to_t i then
    UInt8.uint_to_t (with_onorm #nat (fst (List.Tot.index levels i)))
  else
    norm [zeta; iota; primops; delta_only[`%mk_compute_handshake_auth_leveli]]
    (mk_compute_handshake_auth_leveli initiator pattern (i+1) step)
#pop-options

[@(strict_on_arguments [0; 1])]
noextract inline_for_extraction
val mk_compute_handshake_auth_level
  (initiator : bool) (pattern : wfs_handshake_pattern)
  (step : UInt32.t) :
  Pure auth_level_t
  (requires (
    UInt32.v step < List.Tot.length pattern.messages /\
    Spec.Noise.API.State.Definitions.can_receive initiator pattern))
  (ensures (fun cl ->
    let ac_levels = Some?.v (ac_levels pattern) in
    UInt8.v cl == fst (List.Tot.index ac_levels (UInt32.v step))))

let mk_compute_handshake_auth_level initiator pattern step =
  norm [zeta; iota; primops; delta_only[`%mk_compute_handshake_auth_leveli]]
  (mk_compute_handshake_auth_leveli initiator pattern 0 step)

(**** Session: messages: write *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val write_transport_check_security
  (initiator : bool) (pattern : wfs_handshake_pattern)
  (recv_tpt_msg : bool_or_gbool (save_received_transport initiator pattern))
  (h : mem)
  (payload : encap_message_t) :
  Pure bool
  (requires (Spec.Noise.API.State.Definitions.can_send initiator pattern))
  (ensures (fun b ->
    b = Spec.write_transport_check_security initiator pattern
                                            (bool_or_gbool_to_gbool recv_tpt_msg)
                                            (encap_message_t_v h payload)))

let write_transport_check_security initiator pattern recv_tpt_msg h payload =
  if payload.em_message_len = 0ul then true
  else
    let clevel = mk_compute_transport_conf_level initiator pattern recv_tpt_msg in
    match payload.em_ac_level with
    | Conf_level req_level -> clevel_greater_than clevel req_level
    | _ -> false

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val write_handshake_check_security
  (initiator : bool)
  (pattern : wfs_handshake_pattern)
  (step : UInt32.t{UInt32.v step < List.Tot.length pattern.messages})
  (h : mem)
  (payload : encap_message_t) :
  Pure bool
  (requires (Spec.Noise.API.State.Definitions.can_send initiator pattern))
  (ensures (fun b ->
    b = Spec.write_handshake_check_security pattern (UInt32.v step)
                                            (encap_message_t_v h payload)))

let write_handshake_check_security initiator pattern step h payload =
  if payload.em_message_len = 0ul then true
  else
    let clevel = mk_compute_handshake_conf_level initiator pattern step in
    match payload.em_ac_level with
    | Conf_level req_level -> clevel_greater_than clevel req_level
    | _ -> false

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_write_aux_transport :
     #idc : valid_idc
  -> transport_write_impl : dstate_p_transport_write_st idc
  -> initiator : bool // This is meta
  -> payload : encap_message_p
  -> sn_p : session_p idc
  -> sn : session_t idc
  -> r : HS.rid
  -> out_len : B.pointer size_t
  -> out : B.pointer (buffer uint8) ->
  ST rcode
  (requires (fun h0 ->
    session_p_write_pre idc payload sn_p r out_len out h0 /\
    sn == B.deref h0 sn_p.stp /\
    session_p_g_is_transport h0 sn_p /\
    dstate_t_is_initiator sn = initiator))
  (ensures (fun h0 res h1 ->
    session_p_write_post idc payload sn_p r out_len out h0 res h1))

/// TODO: we redo part of the dynamic tests performed in dstate_p_transport_write.
/// It would be good to have a switch, to either perform those tests dynamically,
/// or put them in the precondition, depending on the layer of the API we want
/// to extract.
#push-options "--z3rlimit 200"
let mk_session_p_write_aux_transport #idc transport_write_impl initiator =
  fun payload_p sn_p sn r outlenp outp ->  

  (**) let h0 = ST.get () in
  // This assert triggers patterns
  (**) assert(session_p_or_null_invariant h0 sn_p (session_p_g_get_device h0 sn_p));

  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let num_messages = with_onorm(List.Tot.length pattern.messages) in
    
  begin
  (**) let st = dstate_t_get_state #idc sn in
  (**) state_t_footprint_full_inclusion_lem st
  end;

  // We need the session to have been matched then reconstructed before
  [@inline_let]
  let Mkddstate_t id info spriv spub pid pinfo dvp dst_st = destruct_dstate_t initiator sn in

  [@inline_let]
  let can_send =
    with_onorm #bool (Spec.Noise.API.State.Definitions.can_send initiator pattern) in
  let encap_payload = B.index payload_p.emp 0ul in
  [@inline_let] let req_level = encap_payload.em_ac_level in
  [@inline_let] let payload_len = encap_payload.em_message_len in
  [@inline_let] let payload = encap_payload.em_message in

  if can_send then
    let next_length_ok =
      mk_state_t_compute_next_message_len #(idc_get_isc idc initiator) #initiator
        dst_st payload_len outlenp
    in
    if next_length_ok then
      begin
      [@inline_let]
      let IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none = dst_st in
      let sec_ok =
        write_transport_check_security initiator pattern recv_tpt_msg h0 encap_payload in
      if sec_ok then
        begin
        // Allocate the buffer for the output
        let outlen = B.index outlenp 0ul in
        (**) assert(size_v outlen > 0);
        let out : buffer uint8 = B.malloc r (u8 0) outlen in
        (**) assert(region_includes r (B.loc_addr_of_buffer (out <: buffer uint8)));
        (**) let h1 = ST.get () in
        (**) dstate_p_frame_invariant (B.loc_buffer outlenp) sn_p h0 h1;
        (**) encap_message_p_frame_invariant (B.loc_buffer outlenp) payload_p h0 h1;
        let res = transport_write_impl payload_len payload outlen out sn_p in
        (**) let h2 = ST.get () in
        // Triggers patterns
        (**) assert(session_p_or_null_invariant h2 sn_p (session_p_g_get_device h2 sn_p));
        begin match res with
        | CSuccess ->
          B.upd outp 0ul out;
          (**) let h3 = ST.get () in
          // For safety
          (**) dstate_p_frame_invariant (B.loc_buffer outp) sn_p h2 h3;
          begin
          (**) let l1 =
          (**)      B.(loc_union (session_p_region_of sn_p)
          (**)        (loc_union
          (**)         (loc_buffer (outlenp <: buffer size_t))
          (**)         (loc_buffer (outp <: buffer (buffer uint8))))) in
          (**) let l2 = B.(loc_union l1 (loc_addr_of_buffer out)) in
          (**) assert(B.(modifies l2 h0 h3));
          (**) B.(modifies_only_not_unused_in l1 h0 h3);
          (**) assert(B.(modifies l1 h0 h3))
          end;
          Success
        | e ->
          B.free (out <: buffer uint8);
          B.upd outlenp 0ul 0ul;
          B.upd outp 0ul null;
          (**) let h3 = ST.get () in
          (**) dstate_p_frame_invariant B.(loc_union (loc_addr_of_buffer out)
          (**)   (loc_union (loc_buffer outlenp) (loc_buffer outp))) sn_p h2 h3;
          begin
          (**) let l1 =
          (**)      B.(loc_union (session_p_region_of sn_p)
          (**)        (loc_union
          (**)         (loc_buffer (outlenp <: buffer size_t))
          (**)         (loc_buffer (outp <: buffer (buffer uint8))))) in
          (**) let l2 = B.(loc_union l1 (loc_addr_of_buffer out)) in
          (**) assert(B.(modifies l2 h0 h3));
          (**) B.(modifies_only_not_unused_in l1 h0 h3);
          (**) assert(B.(modifies l1 h0 h3))
          end;
          Error e
        end
        end
      else
        begin
        B.upd outlenp 0ul 0ul;
        B.upd outp 0ul null;
        Error CSecurity_level
        end
      end
    else
      begin
      B.upd outlenp 0ul 0ul;
      B.upd outp 0ul null;
      Error CInput_size
      end
  else
    begin
    B.upd outlenp 0ul 0ul;
    B.upd outp 0ul null;
    Error CIncorrect_transition
    end
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_write_aux_handshake :
     #idc : valid_idc
  -> handshake_write_impl : dstate_p_handshake_write_st idc
  -> initiator : bool // This is meta
  -> payload : encap_message_p
  -> sn_p : session_p idc
  -> sn : session_t idc
  -> r : HS.rid
  -> out_len : B.pointer size_t
  -> out : B.pointer (buffer uint8) ->
  ST rcode
  (requires (fun h0 ->
    session_p_write_pre idc payload sn_p r out_len out h0 /\
    sn == B.deref h0 sn_p.stp /\
    session_p_g_is_handshake h0 sn_p /\
    dstate_t_is_initiator sn = initiator))
  (ensures (fun h0 res h1 ->
    session_p_write_post idc payload sn_p r out_len out h0 res h1))

#restart-solver
#push-options "--z3rlimit 200"
let mk_session_p_write_aux_handshake #idc handshake_write_impl initiator =
  fun payload_p sn_p sn r outlenp outp ->  

  (**) let h0 = ST.get () in
  // This assert triggers patterns
  (**) assert(session_p_or_null_invariant h0 sn_p (session_p_g_get_device h0 sn_p));

  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let num_messages = with_onorm(List.Tot.length pattern.messages) in

  (**) let r_split = sn_p.stp_r_split in // the region in which to allocate
  (**) let r_pid = sn_p.stp_r_pid in // the region we keep for future allocations (actually useless: only needed for the invariant)
  (**) let h1 = ST.get () in
  (**) assert(region_includes_region sn_p.stp_r r_split);
  (**) assert(region_includes_region sn_p.stp_r r_pid);
    
  begin
  (**) let st = dstate_t_get_state #idc sn in
  (**) state_t_footprint_full_inclusion_lem st
  end;

  // We need the session to have been matched then reconstructed before
  [@inline_let]
  let Mkddstate_t id info spriv spub pid pinfo dvp dst_st = destruct_dstate_t initiator sn in

  [@inline_let]
  let IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk = dst_st in

  (* Check if the state is stuck *)
  if st_step >=^ size (num_messages + 1) then
    begin
    B.upd outlenp 0ul 0ul;
    B.upd outp 0ul null;
    Stuck CIncorrect_transition
    end
  else
  begin

  [@inline_let]
  let can_send =
    with_onorm #bool (Spec.Noise.API.State.Definitions.can_send initiator pattern) in
  let encap_payload = B.index payload_p.emp 0ul in
  [@inline_let] let req_level = encap_payload.em_ac_level in
  [@inline_let] let payload_len = encap_payload.em_message_len in
  [@inline_let] let payload = encap_payload.em_message in

  if can_send then
    let next_length_ok =
      mk_state_t_compute_next_message_len #(idc_get_isc idc initiator) #initiator
        dst_st payload_len outlenp
    in
    if next_length_ok then
      begin
      let sec_ok = write_handshake_check_security initiator pattern st_step h0 encap_payload in
      if sec_ok then
        begin
        // Allocate the buffer for the output
        let outlen = B.index outlenp 0ul in
        (**) valid_idc_handshake_pattern_no_empty_message idc (UInt32.v st_step);
        (**) assert(UInt32.v outlen > 0);
        let out : buffer uint8 = B.malloc r (u8 0) outlen in
        (**) assert(region_includes r (B.loc_addr_of_buffer (out <: buffer uint8)));
        (**) let h1 = ST.get () in
        (**) dstate_p_frame_invariant (B.loc_buffer outlenp) sn_p h0 h1;
        (**) encap_message_p_frame_invariant (B.loc_buffer outlenp) payload_p h0 h1;
        let res = handshake_write_impl payload_len payload sn_p outlen out in
        (**) let h2 = ST.get () in
        // Triggers patterns
        (**) assert(session_p_or_null_invariant h2 sn_p (session_p_g_get_device h2 sn_p));
        begin match res with
        | CSuccess ->
          B.upd outp 0ul out;
          (**) let h3 = ST.get () in
          // For safety
          (**) dstate_p_frame_invariant (B.loc_buffer outp) sn_p h2 h3;
          begin
          (**) let l1 =
          (**)      B.(loc_union (session_p_region_of sn_p)
          (**)        (loc_union
          (**)         (loc_buffer (outlenp <: buffer size_t))
          (**)         (loc_buffer (outp <: buffer (buffer uint8))))) in
          (**) let l2 = B.(loc_union l1 (loc_addr_of_buffer out)) in
          (**) assert(B.(modifies l2 h0 h3));
          (**) B.(modifies_only_not_unused_in l1 h0 h3);
          (**) assert(B.(modifies l1 h0 h3))
          end;
          begin
          (**) let sn_v0 = session_p_v h0 sn_p in
          (**) let payload_v = encap_message_p_v h0 payload_p in
          (**) let res_v = write payload_v sn_v0 in
          (**) assert(Res? res_v)
          end;
          Success
        | e ->
          B.free (out <: buffer uint8);
          B.upd outlenp 0ul 0ul;
          B.upd outp 0ul null;
          (**) let h3 = ST.get () in
          (**) dstate_p_frame_invariant B.(loc_union (loc_addr_of_buffer out)
          (**)   (loc_union (loc_buffer outlenp) (loc_buffer outp))) sn_p h2 h3;
          begin
          (**) let l1 =
          (**)      B.(loc_union (session_p_region_of sn_p)
          (**)        (loc_union
          (**)         (loc_buffer (outlenp <: buffer size_t))
          (**)         (loc_buffer (outp <: buffer (buffer uint8))))) in
          (**) let l2 = B.(loc_union l1 (loc_addr_of_buffer out)) in
          (**) assert(B.(modifies l2 h0 h3));
          (**) B.(modifies_only_not_unused_in l1 h0 h3);
          (**) assert(B.(modifies l1 h0 h3))
          end;
          Stuck e
        end
        end
      else
        begin
        B.upd outlenp 0ul 0ul;
        B.upd outp 0ul null;
        Error CSecurity_level
        end
      end
    else
      begin
      B.upd outlenp 0ul 0ul;
      B.upd outp 0ul null;
      Error CInput_size
      end
  else
    begin
    B.upd outlenp 0ul 0ul;
    B.upd outp 0ul null;
    Error CIncorrect_transition
    end
  end
#pop-options

#push-options "--z3rlimit 100"
let mk_session_p_write #idc handshake_write_impl transport_write_impl =
  fun payload sn_p r out_len out ->
    (**) let h0 = ST.get () in
  // This assert triggers patterns
  (**) assert(session_p_or_null_invariant h0 sn_p (session_p_g_get_device h0 sn_p));

  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let num_messages = with_onorm(List.Tot.length pattern.messages) in
  
  let sn_p: session_p idc = sn_p in
  let snp: B.pointer (dstate_t idc) = sn_p.stp in
  let sn: dstate_t idc = B.index snp 0ul in
  
  begin
  (**) let st = dstate_t_get_state #idc sn in
  (**) state_t_footprint_full_inclusion_lem st
  end;

  match sn with
  | DS_Initiator sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv ->
    [@inline_let] let initiator = true in
    begin match sn_state with
    | IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none ->
      [@inline_let]
      let sn_state = IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none in
      [@inline_let]
      let sn = DS_Initiator sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv in
      mk_session_p_write_aux_transport transport_write_impl initiator payload sn_p sn r out_len out
    | IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk ->
      [@inline_let]
      let sn_state = IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk in
      [@inline_let]
      let sn = DS_Initiator sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv in
      mk_session_p_write_aux_handshake handshake_write_impl initiator payload sn_p sn r out_len out
    end
  | DS_Responder sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv ->
    [@inline_let] let initiator = false in
    begin match sn_state with
    | IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none ->
      [@inline_let]
      let sn_state = IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none in
      [@inline_let]
      let sn = DS_Responder sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv in
      mk_session_p_write_aux_transport transport_write_impl initiator payload sn_p sn r out_len out
    | IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk ->
      [@inline_let]
      let sn_state = IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk in
      [@inline_let]
      let sn = DS_Responder sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv in
      mk_session_p_write_aux_handshake handshake_write_impl initiator payload sn_p sn r out_len out
    end
#pop-options

(**** Session: messages: read *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val pack_message_with_auth_level_to_pointer :
     r:HS.rid
  -> auth_level:auth_level_t
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> out:B.pointer encap_message_p_or_null ->
  ST unit
  (requires (fun h0 ->
    is_eternal_region r /\
    r <> root /\
    live h0 msg /\
    (if B.g_is_null (msg <: buffer uint8) then True
     else B.freeable (msg <: buffer uint8)) /\
    B.live h0 out /\
    begin
    let msg_l =
      if B.g_is_null (msg <: buffer uint8) then (B.loc_buffer (msg <: buffer uint8))
      else B.(loc_addr_of_buffer (msg <: buffer uint8))
    in
    B.(loc_disjoint (loc_buffer out) msg_l) /\
    region_includes r msg_l
    end))
  (ensures (fun h0 _ h1 ->
    let emp = B.deref h1 out in
    B.(modifies (loc_buffer out) h0 h1) /\
    not (encap_message_p_g_is_null emp) /\
    encap_message_p_invariant h1 emp /\
    region_includes r (encap_message_p_region_of emp) /\
    encap_message_p_v h1 emp ==
      Spec.pack_message_with_auth_level (UInt8.v auth_level) (as_seq h0 msg)))

let pack_message_with_auth_level_to_pointer r auth_level msg_len msg out =
  (**) let h0 = ST.get () in
  [@inline_let]
  let em = {
    em_ac_level = Auth_level auth_level;
    em_message_len = msg_len;
    em_message = msg;
  }
  in
  (**) assert(encap_message_t_invariant h0 em);
  let em_ptr = B.malloc r em 1ul in
  let emp = {
    emp = em_ptr;
    emp_r = r;
  }
  in
  B.upd out 0ul emp;
  (**) let h1 = ST.get () in
  (**) assert(encap_message_p_invariant h1 emp)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_read_aux_transport :
     #idc : valid_idc
  -> transport_read_impl : dstate_p_transport_read_st idc
  -> initiator : bool // This is meta
  -> r : HS.rid
  -> payload_out : B.pointer encap_message_p_or_null
  -> sn_p : session_p idc
  -> sn : session_t idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->
  ST rcode
  (requires (fun h0 ->
    session_p_read_pre idc r payload_out sn_p inlen input h0 /\
    r <> root /\
    sn == B.deref h0 sn_p.stp /\
    session_p_g_is_transport h0 sn_p /\
    dstate_t_is_initiator sn = initiator))
  (ensures (fun h0 res h1 ->
    session_p_read_post idc r payload_out sn_p inlen input h0 res h1))

/// TODO: we redo part of the dynamic tests performed in dstate_p_transport_read.
#push-options "--z3rlimit 200"
let mk_session_p_read_aux_transport #idc transport_read_impl initiator =
  fun r payload_out sn_p sn inlen input ->  

  (**) let h0 = ST.get () in
  // This assert triggers patterns
  (**) assert(session_p_or_null_invariant h0 sn_p (session_p_g_get_device h0 sn_p));

  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let num_messages = with_onorm(List.Tot.length pattern.messages) in
    
  begin
  (**) let st = dstate_t_get_state #idc sn in
  (**) state_t_footprint_full_inclusion_lem st
  end;

  // We need the session to have been matched then reconstructed before
  [@inline_let]
  let Mkddstate_t id info spriv spub pid pinfo dvp dst_st = destruct_dstate_t initiator sn in

  [@inline_let]
  let can_receive =
    with_onorm #bool (Spec.Noise.API.State.Definitions.can_receive initiator pattern) in

  if can_receive then
    [@inline_let]
    let next_length_option =
      mk_state_t_compute_next_decrypted_payload_length_option
        #(idc_get_isc idc initiator) #initiator dst_st inlen
    in
    match next_length_option with
    | Some outlen ->
      [@inline_let]
      let alevel = mk_compute_transport_auth_level initiator pattern in
      // Allocate the buffer for the output
      let out : lbuffer uint8 outlen =
        if FStar.UInt32.(outlen >^ 0ul) then (B.malloc r (u8 0) outlen <: buffer uint8)
        else null
      in
      (**) let out_l : G.erased B.loc =
      (**)   if B.g_is_null (out <: buffer uint8) then B.loc_none
      (**)   else B.loc_addr_of_buffer (out <: buffer uint8) in
      (**) assert(region_includes r out_l);
      let res = transport_read_impl outlen out inlen input sn_p in
      (**) let h2 = ST.get () in
      // Triggers patterns
      (**) assert(session_p_or_null_invariant h2 sn_p (session_p_g_get_device h2 sn_p));
      begin match res with
      | CSuccess ->
        pack_message_with_auth_level_to_pointer r alevel outlen out payload_out;
        (**) let h3 = ST.get () in
        (**) dstate_p_frame_invariant (B.loc_buffer payload_out) sn_p h2 h3;
        begin
        (**) let l1 =
        (**)      B.(loc_union (session_p_region_of sn_p)
        (**)         (loc_buffer payload_out)) in
        (**) let l2 = out_l in
        (**) let l3 = B.loc_union l1 l2 in
        (**) assert(B.(modifies l3 h0 h3));
        (**) B.(modifies_only_not_unused_in l1 h0 h3);
        (**) assert(B.(modifies l1 h0 h3))
        end;
        Success
      | e ->
        if not (B.is_null (out <: buffer uint8)) then
          B.free (out <: buffer uint8);
        B.upd payload_out 0ul encap_message_p_null;
        (**) let h3 = ST.get () in
        (**) dstate_p_frame_invariant B.(loc_union out_l
        (**)   (loc_buffer payload_out)) sn_p h2 h3;
        begin
        (**) let l1 =
        (**)      B.(loc_union (session_p_region_of sn_p)
        (**)         (loc_buffer payload_out)) in
        (**) let l2 = out_l in
        (**) let l3 = B.loc_union l1 l2 in
        (**) assert(B.(modifies l3 h0 h3));
        (**) B.(modifies_only_not_unused_in l1 h0 h3);
        (**) assert(B.(modifies l1 h0 h3))
        end;
        Error e
      end
    | _ ->
      begin
      B.upd payload_out 0ul encap_message_p_null;
      Error CInput_size
      end
  else
    begin
    B.upd payload_out 0ul encap_message_p_null;
    Error CIncorrect_transition
    end
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_session_p_read_aux_handshake :
     #idc : valid_idc
  -> handshake_read_impl : dstate_p_handshake_read_st idc
  -> initiator : bool // This is meta
  -> r : HS.rid
  -> payload_out : B.pointer encap_message_p_or_null
  -> sn_p : session_p idc
  -> sn : session_t idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen ->
  ST rcode
  (requires (fun h0 ->
    session_p_read_pre idc r payload_out sn_p inlen input h0 /\
    r <> root /\
    sn == B.deref h0 sn_p.stp /\
    session_p_g_is_handshake h0 sn_p /\
    dstate_t_is_initiator sn = initiator))
  (ensures (fun h0 res h1 ->
    session_p_read_post idc r payload_out sn_p inlen input h0 res h1))

/// TODO: we redo part of the dynamic tests performed in dstate_p_handshake_read.
#restart-solver
#push-options "--z3rlimit 400"
let mk_session_p_read_aux_handshake #idc handshake_read_impl initiator =
  fun r payload_out sn_p sn inlen input ->  

  (**) let h0 = ST.get () in
  // This assert triggers patterns
  (**) assert(session_p_or_null_invariant h0 sn_p (session_p_g_get_device h0 sn_p));

  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let num_messages = with_onorm(List.Tot.length pattern.messages) in

  (**) let r_split = sn_p.stp_r_split in // the region in which to allocate
  (**) let r_pid = sn_p.stp_r_pid in // the region we keep for future allocations (actually useless: only needed for the invariant)
  (**) let h1 = ST.get () in
  (**) assert(region_includes_region sn_p.stp_r r_split);
  (**) assert(region_includes_region sn_p.stp_r r_pid);

  begin
  (**) let st = dstate_t_get_state #idc sn in
  (**) state_t_footprint_full_inclusion_lem st
  end;

  // We need the session to have been matched then reconstructed before
  [@inline_let]
  let Mkddstate_t id info spriv spub pid pinfo dvp dst_st = destruct_dstate_t initiator sn in

  [@inline_let]
  let IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk = dst_st in

  (* Check if the state is stuck *)
  if st_step >=^ size (num_messages + 1) then
    begin
    B.upd payload_out 0ul encap_message_p_null;
    Stuck CIncorrect_transition
    end
  else
  
  begin
  // Can the session receive any message at all? (check that the pattern is two-ways)
  [@inline_let]
  let can_receive =
    with_onorm #bool (Spec.Noise.API.State.Definitions.can_receive initiator pattern) in
  // Can the session send a message now?
  [@inline_let]
  let step_can_receive =
    (if initiator then (st_step %^ 2ul) = 1ul else (st_step %^ 2ul) = 0ul)
    && (st_step <^ size num_messages)
  in

  if can_receive && step_can_receive then
    begin
    begin
    (**) let sn_v = session_p_v h0 sn_p in
    (**) assert(Spec.Noise.API.State.Handshake_receive? (session_get_status sn_v));
    (**) let Spec.Noise.API.State.Handshake_receive i = session_get_status sn_v in
    (**) assert(i < List.Tot.length pattern.messages)
    end;

    [@inline_let]
    let next_length_option =
      mk_state_t_compute_next_decrypted_payload_length_option
        #(idc_get_isc idc initiator) #initiator dst_st inlen
    in
    match next_length_option with
    | Some outlen ->
      let alevel = mk_compute_handshake_auth_level initiator pattern st_step in
      // Allocate the buffer for the output
      let out : lbuffer uint8 outlen =
        if FStar.UInt32.(outlen >^ 0ul) then (B.malloc r (u8 0) outlen <: buffer uint8)
        else null
      in
      (**) let h1 = ST.get () in
      (**) let out_l : G.erased B.loc =
      (**)   if B.g_is_null (out <: buffer uint8) then B.loc_none
      (**)   else B.loc_addr_of_buffer (out <: buffer uint8) in
      (**) assert(region_includes r out_l);
      begin
      (**) assert(B.(modifies loc_none h0 h1));
      (**) let cstate = device_p_get_cstate h0 dvp in
      (**) idc_get_cstate_frame_invariant #idc B.loc_none cstate h0 h1
      end;
      let res = handshake_read_impl outlen out sn_p inlen input in
      (**) let h2 = ST.get () in
      // Triggers patterns
      (**) assert(session_p_or_null_invariant h2 sn_p (session_p_g_get_device h2 sn_p));
      // Prove device_p_no_removal
      (**) assert(device_p_no_removal dvp h0 h1);
      (**) assert(device_p_no_removal dvp h1 h2);
      (**) device_p_no_removal_trans_lem dvp h0 h1 h2;
      begin match res with
      | CSuccess ->
        pack_message_with_auth_level_to_pointer r alevel outlen out payload_out;
        (**) let h3 = ST.get () in
        (**) dstate_p_frame_invariant (B.loc_buffer payload_out) sn_p h2 h3;
        begin
        (**) let l1 =
        (**)      B.(loc_union (session_p_region_of sn_p)
        (**)         (loc_union (device_p_region_of dvp)
        (**)         (loc_buffer payload_out))) in
        (**) let l2 = out_l in
        (**) let l3 = B.loc_union l1 l2 in
        (**) assert(B.(modifies l3 h0 h3));
        (**) B.(modifies_only_not_unused_in l1 h0 h3);
        (**) assert(B.(modifies l1 h0 h3));
        // No removal
        (**) assert(device_p_no_removal dvp h2 h3);
        (**) device_p_no_removal_trans_lem dvp h0 h2 h3
        end;
        Success
      | e ->
        if not (B.is_null (out <: buffer uint8)) then
          B.free (out <: buffer uint8);
        B.upd payload_out 0ul encap_message_p_null;
        (**) let h3 = ST.get () in
        (**) dstate_p_frame_invariant B.(loc_union out_l
        (**)   (loc_buffer payload_out)) sn_p h2 h3;
        begin
        (**) let l1 =
        (**)      B.(loc_union (session_p_region_of sn_p)
        (**)         (loc_union (device_p_region_of dvp)
        (**)         (loc_buffer payload_out))) in
        (**) let l2 = out_l in
        (**) let l3 = B.loc_union l1 l2 in
        (**) assert(B.(modifies l3 h0 h3));
        (**) B.(modifies_only_not_unused_in l1 h0 h3);
        (**) assert(B.(modifies l1 h0 h3));
        (**) let l4 = B.(loc_union (session_p_region_of sn_p) (loc_union (loc_buffer payload_out) out_l)) in
        (**) assert(B.modifies l4 h2 h3);
        (**) device_p_frame_invariant l4 dvp h2 h3;
        // No removal
        (**) assert(device_p_no_removal dvp h2 h3);
        (**) device_p_no_removal_trans_lem dvp h0 h2 h3
        end;
        Stuck e
      end
    | _ ->
      begin
      B.upd payload_out 0ul encap_message_p_null;
      Error CInput_size
      end
    end
  else
    begin
    B.upd payload_out 0ul encap_message_p_null;
    Error CIncorrect_transition
    end
  end
#pop-options

#push-options "--z3rlimit 100"
let mk_session_p_read #idc handshake_read_impl transport_read_impl =
  fun r0 payload_out sn_p inlen input ->
    (**) let h0 = ST.get () in
  // This assert triggers patterns
  (**) assert(session_p_or_null_invariant h0 sn_p (session_p_g_get_device h0 sn_p));

  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let num_messages = with_onorm(List.Tot.length pattern.messages) in
  
  let sn_p: session_p idc = sn_p in
  let snp: B.pointer (dstate_t idc) = sn_p.stp in
  let sn: dstate_t idc = B.index snp 0ul in
  
  begin
  (**) let st = dstate_t_get_state #idc sn in
  (**) state_t_footprint_full_inclusion_lem st
  end;

  // Make sure the region is <> root
  let r = new_region r0 in
  (**) assert(region_includes_region r0 r);
  (**) let h1 = ST.get () in
  begin
  (**) assert(B.(modifies loc_none h0 h1));
  (**) let dvp = dstate_p_g_get_device h0 sn_p in
  (**) let cstate = device_p_get_cstate h0 dvp in
  (**) idc_get_cstate_frame_invariant #idc B.loc_none cstate h0 h1
  end;

  let res =
    match sn with
    | DS_Initiator sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv ->
      [@inline_let] let initiator = true in
      begin match sn_state with
      | IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none ->
        [@inline_let]
        let sn_state = IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none in
        [@inline_let]
        let sn = DS_Initiator sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv in
        mk_session_p_read_aux_transport transport_read_impl initiator r payload_out sn_p sn inlen input
      | IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk ->
        [@inline_let]
        let sn_state = IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk in
        [@inline_let]
        let sn = DS_Initiator sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv in
        mk_session_p_read_aux_handshake handshake_read_impl initiator r payload_out sn_p sn inlen input
      end
    | DS_Responder sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv ->
      [@inline_let] let initiator = false in
      begin match sn_state with
      | IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none ->
        [@inline_let]
        let sn_state = IMS_Transport h recv_tpt_msg send_key send_none recv_key recv_none in
        [@inline_let]
        let sn = DS_Responder sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv in
        mk_session_p_read_aux_transport transport_read_impl initiator r payload_out sn_p sn inlen input
      | IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk ->
        [@inline_let]
        let sn_state = IMS_Handshake st_step k ck h spriv spub epriv epub rs re psk in
        [@inline_let]
        let sn = DS_Responder sn_state sn_id sn_info sn_spriv sn_spub sn_pid sn_pinfo sn_dv in
        mk_session_p_read_aux_handshake handshake_read_impl initiator r payload_out sn_p sn inlen input
      end
  in
  begin
  (**) let h2 = ST.get () in
  (**) let dvp = dstate_p_g_get_device h0 sn_p in
  (**) assert(device_p_no_removal dvp h0 h1);
  (**) assert(device_p_no_removal dvp h1 h2);
  (**) device_p_no_removal_trans_lem dvp h0 h1 h2
  end;
  res
#pop-options
