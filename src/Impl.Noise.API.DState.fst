module Impl.Noise.API.DState

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

open Spec.Noise.API.State.Definitions
friend Spec.Noise.API.State.Definitions
open Spec.Noise.API.State

module M = Spec.Noise.Map
module SSpec = Spec.Noise.API.State.Definitions

open Spec.Noise.API.Device.Definitions
friend Spec.Noise.API.Device.Definitions
open Spec.Noise.API.Device.Lemmas
friend Spec.Noise.API.Device.Lemmas
module DSpec = Spec.Noise.API.Device

open Spec.Noise.API.DState.Definitions
friend Spec.Noise.API.DState.Definitions
open Spec.Noise.API.DState.Lemmas
friend Spec.Noise.API.DState.Lemmas
module Spec = Spec.Noise.API.DState

open Impl.Noise.Types
open Impl.Noise.HandshakeState
open Impl.Noise.SendReceive
open Impl.Noise.RecursiveMessages
open Impl.Noise.API.State
module State = Impl.Noise.API.State
open Impl.Noise.API.Device
friend Impl.Noise.API.Device
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.BufferEquality
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate
open Spec.Noise

module LL = Impl.Noise.LinkedList
module St = Impl.Noise.Stateful

open Lib.Memzero0

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

let _align_fsti = ()

(*** Configuration, policy *)

#push-options "--ifuel 1"
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let apply_policy (idc : idconfig) :
  stateful_validation_state (idc_get_nc idc) (stateful_validation_info idc) =

Stateful_vstate

  (* vst *)
  (apply_policy_stateful idc)

  (* recv_psk *)
  (idc_is_psk idc)

  (* validate_spec *)
  // Don't do eta-expansion, because otherwise we need functional extensionality
  // later on to prove equalities with other functions.
  (apply_policy (idc_get_dc idc))

  // validate
  (fun dv rs pinfo psk ->
   (**) let h0 = ST.get () in
   [@inline_let]
   let Mkdevice_t_raw info sk spriv spub prlg scounter peers pcounter cert = dv in
   [@inline_let] let nc = idc_get_nc idc in
   [@inline_let] let id_cl = idc_get_pid idc in
   [@inline_let] let peer_info = idc_get_info idc in
   [@inline_let] let has_s = with_onorm(peers_have_s (idc_get_pattern idc)) in
   [@inline_let] let has_psk = with_onorm(idc_is_psk idc) in
   [@inline_let] let policy = idc_get_policy idc in
   [@inline_let] let vpinfo_st = stateful_validation_info idc in

   let b =
   (raw_apply_policy nc id_cl peer_info has_s has_psk policy).validate peers rs pinfo psk in
   (**) let h1 = ST.get () in
   begin
   (**) let dv_v0 = device_t_v h0 dv in
   (**) let dv_v1 = device_t_v h1 dv in
   (**) let peers_v0 = dv_v0.DSpec.dv_peers in
   (**) let peers_v1 = LL.v h1 peers in
   (**) let peers_v1' = dv_v1.DSpec.dv_peers in
   (**) let rs_v = as_seq h0 rs in
   (**) let res_v = (raw_apply_policy nc id_cl peer_info has_s has_psk policy).validate_spec peers_v0 rs_v in
   (**) let res_v' = apply_policy_on_peers_spec (idc_get_dc idc) peers_v0 rs_v in
   (**) assert(peers_v1 == peers_v1');
   (**) assert(forall p. raw_peer_has_s #(get_config nc) #(peer_info.St.smficc_stateful.St.t ()) rs_v p ==
   (**)        DSpec.peer_has_s #(idc_get_dc idc) rs_v p);
   (**) M.lookup_pred_eq_lem (raw_peer_has_s #(get_config nc) #(peer_info.St.smficc_stateful.St.t ()) rs_v)
   (**)                      (DSpec.peer_has_s #(idc_get_dc idc) rs_v) peers_v0;
   (**) assert(res_v == res_v');
   (**) assert(
   (**)   begin
   (**)   match res_v with
   (**)   | None  -> not b
   (**)   | Some (pinfo_v, psk_v) ->
   (**)     b /\
   (**)     pinfo_v ==
   (**)     (raw_stateful_validation_info id_cl peer_info.St.smficc_stateful).St.v () h1 pinfo /\
   (**)     psk_v == lbuffer_or_unit_to_opt_lseq h1 psk
   (**)   | _ -> False
   (**)   end)
   end;   
   b)
#pop-options


#push-options "--fuel 1"
let idc_pre_receives_rs_lem (idc : valid_idc) (initiator : bool) :
  Lemma (
    let hsk = idc_get_pattern idc in
    let pre = get_receive_pre hsk initiator in
    (pre_receives_rs hsk initiator <==> Some? pre)) = ()
#pop-options

let idc_get_isc idc initiator =
  match idc () with Mkidconfig_raw nc dc pat sid pid info policy cert srlz ->
  [@inline_let] let sc_info = stateful_validation_info idc in
  [@inline_let] let peers_have_s = with_onorm(peers_have_s pat) in
  [@inline_let] let is_psk = with_onorm(idc_is_psk idc) in
  [@inline_let] let ks = with_onorm(key_slots_from_pattern initiator pat) in
  [@inline_let] let info_st = info.St.smficc_stateful in
  [@inline_let] let sc = dconfig_to_sconfig dc in
  [@inline_let] let isc =
  {
    isc_nc = nc;
    isc_sc = sc;
    isc_pattern = pat;
    isc_ks = ks;
    isc_pinfo = sc_info;
    isc_lookups_psk = idc_is_psk idc;
  } in
  (**) assert(not (isc_lookups_psk isc) || is_psk);
  (**) assert(not (lookups_psk pat initiator) || isc_lookups_psk isc);
  (**) assert(handshake_pattern_is_valid (isc_get_pattern isc));
  (**) assert(check_pattern (isc_get_pattern isc));
  (**) assert(isc_is_valid initiator isc);
  isc

let idc_get_resp_isc_is_valid (idc : valid_idc) = ()

let idc_get_validate idc initiator =
  apply_policy idc


(*** DState *)
(**** Definitions *)

/// TODO: A state doesn't necessarily need to keep a device as parameter. However,
/// implemeting this makes it difficult to make it work with the spec. A possibility
/// would be to carry around an option device, rather than a device.

/// We have to create one constructor for the initiator and one constructor for
/// the responder, because the types extracted for [state_t] will not be the same.
[@CAbstractStruct]
noeq type dstate_t_raw
  (id_t info_t
   istate_t ispriv_t ispub_t ipid_t ipinfo_t idv_t
   rstate_t rspriv_t rspub_t rpid_t rpinfo_t rdv_t : Type0) =
| DS_Initiator :
     state:istate_t
  -> id:id_t
  -> info:info_t
  -> spriv:ispriv_t
  -> spub:ispub_t
  -> pid:ipid_t
  -> pinfo:ipinfo_t
  -> dv:idv_t
  -> dstate_t_raw id_t info_t istate_t ispriv_t ispub_t ipid_t ipinfo_t idv_t
                  rstate_t rspriv_t rspub_t rpid_t rpinfo_t rdv_t
| DS_Responder :
     state:rstate_t
  -> id:id_t
  -> info:info_t
  -> spriv:rspriv_t
  -> spub:rspub_t
  -> pid:rpid_t
  -> pinfo:rpinfo_t
  -> dv:rdv_t
  -> dstate_t_raw id_t info_t istate_t ispriv_t ispub_t ipid_t ipinfo_t idv_t
                  rstate_t rspriv_t rspub_t rpid_t rpinfo_t rdv_t

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_t (idc : valid_idc) =
  dstate_t_raw 
    (dstate_id_t idc)
    (info_t idc)
    (State.state_t (idc_get_init_isc idc) true)
    (sprivate_key_t idc true) // For now, we copy the keys inside the state. TODO: share them with the device
    (spublic_key_t idc true)
    (peer_id_opt_t idc) //(idc_get_pid idc).id_t // We don't use [peer_id_t]: [pid] might be the 'none' value
    (peer_info_t idc)
    (device_p idc)
    (State.state_t (idc_get_resp_isc idc) false)
    (sprivate_key_t idc false) // For now, we copy the keys inside the state. TODO: share them with the device
    (spublic_key_t idc false)
    (peer_id_opt_t idc) //(idc_get_pid idc).id_t // Might be the 'none' value
    (peer_info_t idc)
    (device_p idc)

[@@ noextract_to "Karamel"] noextract
let invert_dstate_t (idc : valid_idc) :
  Lemma
  (inversion (dstate_t idc))
  [SMTPat (dstate_t idc)] =
  allow_inversion (dstate_t idc)

noeq type dstate_p_or_null_raw (dstate_t : Type0) = {
  stp : B.pointer_or_null dstate_t;
  stp_r : HS.rid;
  // Region in which to perform the split allocations
  stp_r_split : HS.rid;
  // Region in which to allocate the pid pointers
  stp_r_pid : HS.rid;
}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_p_or_null (idc : valid_idc) =
  dstate_p_or_null_raw (dstate_t idc)

let dstate_p_g_is_null #idc stp = B.g_is_null stp.stp

/// A small utility to factorize the proofs and the helpers.
/// Note that we can't extract it because [isconfig] can't be extracted.
/// The first 'd' stands for 'destructed'.

inline_for_extraction noextract noeq
type gddstate_t (idc : valid_idc) = {
  gdds_initiator : bool;
  gdds_id:dstate_id_t idc;
  gdds_info:info_t idc;
  gdds_spriv:sprivate_key_t idc gdds_initiator;
  gdds_spub:spublic_key_t idc gdds_initiator;
  gdds_pid : (idc_get_pid idc).id_t;
  gdds_pinfo : peer_info_t idc;
  gdds_dv : device_p idc;
  gdds_st : state_t (idc_get_isc idc gdds_initiator) gdds_initiator;
}

inline_for_extraction noextract noeq
type ddstate_t (idc : valid_idc) (initiator : bool) = {
  dds_id:dstate_id_t idc;
  dds_info:info_t idc;
  dds_spriv:sprivate_key_t idc initiator;
  dds_spub:spublic_key_t idc initiator;
  dds_pid : (idc_get_pid idc).id_t;
  dds_pinfo : peer_info_t idc;
  dds_dv : device_p idc;
  dds_st : state_t (idc_get_isc idc initiator) initiator;
}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val gdestruct_dstate_t (#idc : valid_idc) (st : dstate_t idc) : GTot (gddstate_t idc)
let gdestruct_dstate_t #idc st =
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv ->
    { gdds_initiator = true; gdds_id = id; gdds_info = info;
      gdds_st = st; gdds_spriv = spriv; gdds_spub = spub;
      gdds_pid = pid; gdds_pinfo = pinfo; gdds_dv = dv }
  | DS_Responder st id info spriv spub pid pinfo dv ->
    { gdds_initiator = false; gdds_id = id; gdds_info = info;
      gdds_st = st; gdds_spriv = spriv; gdds_spub = spub;
      gdds_pid = pid; gdds_pinfo = pinfo; gdds_dv = dv }

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_is_initiator :
     #idc:valid_idc
  -> st:dstate_t idc
  -> bool
let dstate_t_is_initiator #idc st =
  DS_Initiator? st

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val destruct_dstate_t (#idc : valid_idc) (initiator : bool)
                      (st : dstate_t idc{initiator = dstate_t_is_initiator st}) :
    ddstate_t idc initiator
let destruct_dstate_t #idc initiator st =
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv ->
    { dds_st = st; dds_id = id; dds_info = info;
      dds_spriv = spriv; dds_spub = spub;
      dds_pid = pid; dds_pinfo = pinfo; dds_dv = dv }
  | DS_Responder st id info spriv spub pid pinfo dv ->
    { dds_st = st; dds_id = id; dds_info = info;
      dds_spriv = spriv; dds_spub = spub;
      dds_pid = pid; dds_pinfo = pinfo; dds_dv = dv }

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_is_handshake (#idc : valid_idc) (st : dstate_t idc) : bool
let dstate_t_is_handshake #idc st =
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv -> state_t_is_handshake st
  | DS_Responder st id info spriv spub pid pinfo dv -> state_t_is_handshake st

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let dstate_t_is_transport (#idc : valid_idc) (st : dstate_t idc) : GTot bool =
  not (dstate_t_is_handshake st)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_handshake_get_step :
     #idc:valid_idc
  -> st:dstate_t idc{dstate_t_is_handshake st}
  -> UInt32.t
let dstate_t_handshake_get_step #idc st =
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv -> state_t_handshake_get_step st
  | DS_Responder st id info spriv spub pid pinfo dv -> state_t_handshake_get_step st

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_handshake_get_step_v :
     #idc:valid_idc
  -> st:dstate_t idc{dstate_t_is_handshake st}
  -> nat
let dstate_t_handshake_get_step_v #idc st =
  UInt32.v (dstate_t_handshake_get_step st)

let mk_dstate_p_null (idc : valid_idc) : stp:dstate_p_or_null idc{dstate_p_g_is_null stp} =
  { stp = B.null; stp_r = root; stp_r_split = root; stp_r_pid = root; }

[@@ noextract_to "Karamel"] noextract
val dstate_t_g_handshake_get_static :
     #idc:valid_idc
  -> st:dstate_t idc{dstate_t_is_handshake st}
  -> GTot (
       let initiator = dstate_t_is_initiator st in
       sprivate_key_t idc initiator & spublic_key_t idc initiator)

let dstate_t_g_handshake_get_static #idc st =
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv -> (spriv, spub)
  | DS_Responder st id info spriv spub pid pinfo dv -> (spriv, spub)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_get_device (#idc : valid_idc) (dst : dstate_t idc) : GTot (device_p idc)
let dstate_t_get_device #idc dst =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dv st = gdestruct_dstate_t dst in
  dv

[@@ noextract_to "Karamel"] noextract
val dstate_t_get_state (#idc : valid_idc) (dst : dstate_t idc) :
  GTot (state_t (idc_get_isc idc (dstate_t_is_initiator dst)) (dstate_t_is_initiator dst))
let dstate_t_get_state #idc dst =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dv st = gdestruct_dstate_t dst in
  st

let dstate_p_g_get_device #idc h dst_p =
  let dst = B.deref h dst_p.stp in
  dstate_t_get_device #idc dst

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_get_pid (#idc : valid_idc) (dst : dstate_t idc) :
  Tot (idc_get_pid idc).id_t
let dstate_t_get_pid #idc dst =
  match dst with
  | DS_Initiator st id info spriv spub pid pinfo dv -> pid
  | DS_Responder st id info spriv spub pid pinfo dv -> pid

[@@ noextract_to "Karamel"] noextract
val dstate_t_core_footprint (#idc : valid_idc) (st : dstate_t idc) : GTot B.loc
let dstate_t_core_footprint #idc st =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dv st = gdestruct_dstate_t st in
  B.(loc_union (state_t_core_footprint st)
    (loc_union (idc_get_info_footprint info) (idc_get_info_footprint pinfo)))

[@@ noextract_to "Karamel"] noextract
val dstate_t_footprint (#idc : valid_idc) (st : dstate_t idc) : GTot B.loc
let dstate_t_footprint #idc st =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dv st = gdestruct_dstate_t st in
  // The static keys footprint is actually already included in [state_t_footprint],
  // but as it is abstract, counting them twice makes reasoning easier.
  B.(loc_union (loc_union (state_t_footprint st)
               (loc_union (idc_get_info_footprint info) (idc_get_info_footprint pinfo)))
               (loc_union (lbuffer_or_unit_to_loc spriv) (lbuffer_or_unit_to_loc spub)))

[@@ noextract_to "Karamel"] noextract
val dstate_t_footprint_with_device (#idc : valid_idc) (dst : dstate_t idc) : GTot B.loc
let dstate_t_footprint_with_device #idc dst =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dv st = gdestruct_dstate_t dst in
  B.(loc_union (dstate_t_footprint dst) (device_p_region_of dv))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_has_static (#idc : valid_idc) (st : dstate_t idc) : bool
let dstate_t_has_static #idc st =
  let initiator = dstate_t_is_initiator st in
  isc_get_s (idc_get_isc idc initiator)

[@@ noextract_to "Karamel"] noextract
val device_p_owns_dstate_t
  (#idc : valid_idc) (h : mem) (dvp : device_p idc) (st : dstate_t idc) : GTot Type0
let device_p_owns_dstate_t #idc h dvp dst =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dvp' st = gdestruct_dstate_t dst in
  let dv = B.deref h dvp.dvp in
  let Mkdevice_t_raw dv_info dv_sk dv_spriv dv_spub prologue dv_scounter peers pcounter cstate = dv in
  dvp == dvp' /\
  begin
  if dstate_t_is_handshake dst && dstate_t_has_static dst then
    lbuffer_or_unit_to_opt_lseq h spriv == lbuffer_or_unit_to_opt_lseq h dv_spriv /\
    lbuffer_or_unit_to_opt_lseq h spub == lbuffer_or_unit_to_opt_lseq h dv_spub
  else True
  end

/// Internally, any dstate_t will always satisfy this invariant when given to or
/// returned by a function. The invariant revealed to the user is (very) slightly more
/// precise.
[@@ noextract_to "Karamel"] noextract
val dstate_t_invariant_core (#idc : valid_idc) (h : mem) (dst : dstate_t idc) : GTot Type0
let dstate_t_invariant_core #idc h dst =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dvp st = gdestruct_dstate_t dst in
  let dv = B.deref h dvp.dvp in
  let Mkdevice_t_raw dv_info dv_sk dv_spriv dv_spub scounter prologue peers pcounter cstate = dv in
  device_p_invariant h dvp /\
  state_t_invariant h st /\
  lbuffer_or_unit_live h spriv /\
  lbuffer_or_unit_live h spub /\
  idc_get_info_invariant h info /\
  idc_get_info_invariant h pinfo /\

  lbuffer_or_unit_freeable spriv /\
  lbuffer_or_unit_freeable spub /\
  idc_get_info_freeable h info /\
  idc_get_info_freeable h pinfo /\

  begin
  let dvp_loc = device_p_region_of dvp in
  let st_loc = state_t_core_footprint st in
  let info_loc = info_footprint info in
  let pinfo_loc = peer_info_footprint pinfo in
  let spriv_loc = lbuffer_or_unit_to_loc spriv in
  let spub_loc = lbuffer_or_unit_to_loc spub in
  B.all_disjoint [dvp_loc; st_loc; info_loc; pinfo_loc; spriv_loc; spub_loc]
  end /\

  begin
  let pattern = idc_get_pattern idc in
  let n = List.Tot.length pattern.messages in
  if state_t_is_handshake st then
    let step = UInt32.v (state_t_handshake_get_step st) in
    let st_spriv, st_spub = state_t_handshake_get_static st in
    st_spriv == spriv /\ st_spub == spub
  else
    peer_id_is_some pid = knows_remote pattern initiator n
  end /\

  device_p_owns_dstate_t h dvp dst

[@@ noextract_to "Karamel"] noextract
val dstate_t_invariant (#idc : valid_idc) (h : mem) (dst : dstate_t idc) : GTot Type0
let dstate_t_invariant #idc h dst =
  dstate_t_invariant_core h dst /\

  begin
  let Mkgddstate_t initiator id info spriv spub pid pinfo dvp st = gdestruct_dstate_t dst in
  let pattern = idc_get_pattern idc in
  let n = List.Tot.length pattern.messages in
  if state_t_is_handshake st then
    let step = UInt32.v (state_t_handshake_get_step st) in
    (step <= n ==> (
      peer_id_is_some pid = knows_remote pattern initiator step))
  else
    peer_id_is_some pid = knows_remote pattern initiator n
  end

/// When we need to manipulate a state's step index, but there is no invariant to
/// assert it is bounded by the number of messages, we use min(step, number of messages).
/// This allows us to call functions which take a precondition on the step, without
/// carrying cumbersome preconditions everywhere (and in the end all this is hidden
/// from the user).
[@@ noextract_to "Karamel"] noextract
let get_bounded_step (#isc : isconfig) (#initiator : bool)
                     (st:State.state_t isc initiator{state_t_is_handshake st}) : nat =
  let pattern =  isc_get_pattern isc in
  let i = state_t_handshake_get_step st in
  let i = UInt32.v i in
  let n = List.Tot.length pattern.messages in
  if i > n then n else i  

[@@ noextract_to "Karamel"] noextract
val dstate_t_v_aux (#idc : valid_idc) (h : mem)
                   (initiator : bool)
                   (st:State.state_t (idc_get_isc idc initiator) initiator)
                   (id:dstate_id_t idc)
                   (info:info_t idc)
                   (pid:(idc_get_pid idc).id_t)
                   (pinfo:peer_info_t idc) :
  GTot (dstate_s idc)

let dstate_t_v_aux #idc h initiator st id info pid pinfo =
  let pattern = idc_get_pattern idc in
  let isc = idc_get_isc idc initiator in
  let id_v = dstate_id_v id in
  let info_v = idc_get_info_v h info in
  let pid_v = peer_id_opt_v pid in
  let pinfo_v = if Some? pid_v then Some (idc_get_info_v #idc h pinfo) else None in
  if state_t_is_handshake st then
    begin
    let i = get_bounded_step #isc #initiator st in
    let smi = isc_step_to_smi #initiator isc i in
    let st_v = handshake_state_t_v_with_smi h st smi in
    {
      dst_state = st_v;
      dst_id = id_v;
      dst_info = info_v;
      dst_pid = pid_v;
      dst_pinfo = pinfo_v;
    }
    end
  else
    let st_v = transport_state_t_v h st in
    {
      dst_state = st_v;
      dst_id = id_v;
      dst_info = info_v;
      dst_pid = pid_v;
      dst_pinfo = pinfo_v;
    }

[@@ noextract_to "Karamel"] noextract
val dstate_t_v (#idc : valid_idc) (h : mem) (st : dstate_t idc) : GTot (dstate_s idc)
let dstate_t_v #idc h st =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dv st = gdestruct_dstate_t st in
  dstate_t_v_aux #idc h initiator st id info pid pinfo

// Sanity check
[@@ noextract_to "Karamel"] noextract
val dstate_t_is_handshake_lem (#idc : valid_idc) (st : dstate_t idc) (h : mem) :
  Lemma
  (requires (dstate_t_invariant h st))
  (ensures (
    let st_v = dstate_t_v h st in
    dstate_t_is_handshake st = dstate_is_handshake st_v))

let dstate_t_is_handshake_lem #idc st h = ()

[@@ noextract_to "Karamel"] noextract
val dstate_t_frame_invariant :
     #idc:valid_idc
  -> l:B.loc
  -> st:dstate_t idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    dstate_t_invariant h0 st /\
    B.loc_disjoint l (dstate_t_footprint_with_device st) /\
    B.modifies l h0 h1))
  (ensures (
    dstate_t_invariant h1 st /\
    dstate_t_v h0 st == dstate_t_v h1 st))
  [SMTPat (dstate_t_invariant h1 st);
   SMTPat (B.modifies l h0 h1)]

let dstate_t_frame_invariant #idc l dst h0 h1 =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dvp st = gdestruct_dstate_t dst in
  let pattern = idc_get_pattern idc in
  let isc = idc_get_isc idc initiator in
  info_frame_invariant l info h0 h1;
  info_frame_invariant l pinfo h0 h1;
  info_frame_freeable l info h0 h1;
  info_frame_freeable l pinfo h0 h1;
  device_p_frame_invariant l dvp h0 h1;
  if state_t_is_handshake st then
    begin
    let i = get_bounded_step #isc #initiator st in
    let smi = isc_step_to_smi isc i in
    handshake_state_t_frame_invariant #isc l #initiator st smi h0 h1
    end
  else
    begin
    state_t_footprint_inclusion_lem #isc #initiator st;
    transport_state_t_frame_invariant #isc l #initiator st h0 h1
    end

/// The finer frame invariant
[@@ noextract_to "Karamel"] noextract
val dstate_t_frame_invariant_update_device
  (#idc : valid_idc) (l : B.loc) (st : dstate_t idc) (dvp : device_p idc) (h0 h1 : mem) :
  Lemma
  (requires (
    B.loc_disjoint (dstate_t_footprint st) l /\
    B.modifies l h0 h1 /\
    device_p_only_changed_peers_or_counters dvp h0 h1 /\
    device_p_invariant h1 dvp /\
    dstate_t_invariant h0 st /\
    device_p_owns_dstate_t h0 dvp st))
  (ensures (
    dstate_t_invariant h1 st /\
    dstate_t_v h1 st == dstate_t_v h0 st /\
    device_p_owns_dstate_t h1 dvp st))
    [SMTPat (dstate_t_invariant h1 st);
     SMTPat (device_p_owns_dstate_t h0 dvp st);
     SMTPat (B.modifies l h0 h1)]

let dstate_t_frame_invariant_update_device #idc l dst dvp0 h0 h1 =
  let Mkgddstate_t initiator id info spriv spub pid pinfo dvp st = gdestruct_dstate_t dst in
  let pattern = idc_get_pattern idc in
  let isc = idc_get_isc idc initiator in
  info_frame_invariant l info h0 h1;
  info_frame_invariant l pinfo h0 h1;
  info_frame_freeable l info h0 h1;
  info_frame_freeable l pinfo h0 h1;
  if state_t_is_handshake st then
    begin
    let i = get_bounded_step #isc #initiator st in
    let smi = isc_step_to_smi isc i in
    handshake_state_t_frame_invariant #isc l #initiator st smi h0 h1
    end
  else
    begin
    state_t_footprint_inclusion_lem #isc #initiator st;
    transport_state_t_frame_invariant #isc l #initiator st h0 h1
    end

[@@ noextract_to "Karamel"] noextract
val dstate_p_core_footprint (#idc : valid_idc) (h : mem) (stp : dstate_p idc) : GTot B.loc
let dstate_p_core_footprint #idc h stp =
  let st = B.deref h stp.stp in
  B.(loc_union (loc_addr_of_buffer stp.stp) (dstate_t_core_footprint st))

[@@ noextract_to "Karamel"] noextract
val dstate_p_footprint (#idc : valid_idc) (h : mem) (stp : dstate_p idc) : GTot B.loc
let dstate_p_footprint #idc h stp =
  let st = B.deref h stp.stp in
  B.(loc_union (loc_addr_of_buffer stp.stp) (dstate_t_footprint st))

[@@ noextract_to "Karamel"] noextract
val dstate_p_footprint_with_device (#idc : valid_idc) (h : mem) (stp : dstate_p idc) : GTot B.loc
let dstate_p_footprint_with_device #idc h stp =
  let st = B.deref h stp.stp in
  B.(loc_union (loc_addr_of_buffer stp.stp) (dstate_t_footprint_with_device st))

let dstate_p_rid_of (#idc : valid_idc) (stp : dstate_p idc) :
  GTot HS.rid =
  stp.stp_r

let dstate_p_v #idc h stp =
  let st = B.deref h stp.stp in
  dstate_t_v h st

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val dstate_t_is_stuck (#idc : valid_idc) (st : dstate_t idc) : bool
let dstate_t_is_stuck #idc st =
  [@inline_let] let n = with_onorm(List.Tot.length (idc_get_pattern idc).messages) in
  [@inline_let] let is_handshake_state = dstate_t_is_handshake st in
  is_handshake_state && UInt32.gte (dstate_t_handshake_get_step st) (size (n + 1))

[@@ noextract_to "Karamel"] noextract
val dstate_t_is_stuck_lem (#idc : valid_idc) (st : dstate_t idc) (h : mem) :
  Lemma
  (requires (dstate_t_invariant h st))
  (ensures (
    let st_v = dstate_t_v h st in
    dstate_t_is_stuck st = dstate_is_stuck st_v))

let dstate_t_is_stuck_lem #idc st h = ()

let dstate_p_g_handshake_get_static #idc h stp =
  let st = B.deref h stp.stp in
  dstate_t_g_handshake_get_static st

// Sanity check
[@@ noextract_to "Karamel"] noextract
let dstate_p_g_is_initiator_lem (#idc : valid_idc) (stp : dstate_p idc) (h : mem) :
  Lemma (
    let st = B.deref h stp.stp in
    dstate_p_g_is_initiator h stp = dstate_t_is_initiator st) = ()

// Sanity check
[@@ noextract_to "Karamel"] noextract
let dstate_p_g_is_handshake_lem (#idc : valid_idc) (stp : dstate_p idc) (h : mem) :
  Lemma (
    let st = B.deref h stp.stp in
    dstate_p_g_is_handshake h stp = dstate_t_is_handshake st) = ()

let dstate_p_invariant #idc h stp =
  let st = B.deref h stp.stp in

  // Parent region: used to make the footprint independent from the memory snapshot
  // If dvp.dvp_r <> FStar.Monotonic.HyperHeap.root, we can use:
  // * [ST.recall_region]
  // * [FStar.Monotonic.HyperStack.eternal_disjoint_from_tip]
  // to show that the region is disjoint from the stack.
  // This won't appear on the user side: at allocation time, we use the trick
  // of allocating a new region inside the region the user provides for heap
  // allocation, and allocate the new state in this new region.
  ST.is_eternal_region stp.stp_r /\
  ST.is_eternal_region stp.stp_r_split /\
  ST.is_eternal_region stp.stp_r_pid /\
  stp.stp_r <> root /\
  stp.stp_r_split <> root /\
  stp.stp_r_pid <> root /\

  // We don't need (and can't have) precise relations between regions
  region_includes_region stp.stp_r stp.stp_r_split /\
  region_includes_region stp.stp_r stp.stp_r_pid /\

  B.live h stp.stp /\
  B.freeable stp.stp /\

  region_includes stp.stp_r (dstate_t_footprint st) /\
  region_includes stp.stp_r (B.loc_addr_of_buffer stp.stp) /\

  begin
  let ptr_loc = B.loc_addr_of_buffer stp.stp in
  let st_loc = dstate_t_footprint_with_device st in
  let r_split =
    if dstate_p_g_is_handshake h stp then region_to_loc stp.stp_r_split else B.loc_none in
  let r_pid = region_to_loc stp.stp_r_pid in
  B.all_disjoint [ptr_loc; st_loc; r_split; r_pid]
  end /\

  B.loc_disjoint (device_p_region_of (dstate_p_g_get_device h stp)) (dstate_p_region_of stp) /\

  dstate_t_invariant h st

let dstate_p_live #idc h stp =
  B.live h stp.stp /\
  begin
  if dstate_p_g_is_null stp then True
  else dstate_p_invariant h stp
  end

let dstate_p_is_null #idc stp =
  is_null #MUT #_ stp.stp

let dstate_p_recall_region #idc stp =
  (**) let h0 = ST.get () in
  recall_region stp.stp_r;
  // We could use a pattern instead, but it would be cumbersome
  if IndefiniteDescription.strong_excluded_middle (is_stack_region (get_tip h0)) then
    eternal_disjoint_from_tip h0 stp.stp_r
  else ()

let dstate_p_is_stuck #idc st =
  let st = B.index st.stp 0ul in
  dstate_t_is_stuck st

// Sanity check
[@@ noextract_to "Karamel"] noextract
let dstate_t_p_owns_dstate_p_lem
  (#idc : valid_idc) (h : mem) (stp : dstate_p idc) :
  Lemma (
    let st = B.deref h stp.stp in
    dstate_p_g_has_static h stp = dstate_t_has_static st) = ()

let device_p_owns_dstate_p
  (#idc : valid_idc) (h : mem) (dvp : device_p idc) (stp : dstate_p idc) : GTot Type0 =
  dstate_p_g_get_device h stp == dvp /\
  begin
  if dstate_p_g_is_handshake h stp && dstate_p_g_has_static h stp then
    let spriv, spub = dstate_p_g_handshake_get_static h stp in
    let dv_spriv, dv_spub = device_p_g_get_static h dvp in
    lbuffer_or_unit_to_opt_lseq h spriv == lbuffer_or_unit_to_opt_lseq h dv_spriv /\
    lbuffer_or_unit_to_opt_lseq h spub == lbuffer_or_unit_to_opt_lseq h dv_spub
  else
    True
  end

// Sanity check
[@@ noextract_to "Karamel"] noextract
let device_p_owns_dstate_p_lem
  (#idc : valid_idc) (h : mem) (dvp : device_p idc) (dstp : dstate_p idc) :
  Lemma (
    let dst = B.deref h dstp.stp in
    device_p_owns_dstate_p h dvp dstp <==> device_p_owns_dstate_t h dvp dst) = ()

let dstate_p_invariant_get_device #idc h stp = ()

let dstate_p_invariant_live_lem #idc h stp = ()

let dstate_p_frame_invariant #idc l stp h0 h1 =
  let st = B.deref h0 stp.stp in
  dstate_t_frame_invariant l st h0 h1

let dstate_p_frame_invariant_update_device #idc l stp dvp h0 h1 =
  let st = B.deref h0 stp.stp in
  dstate_t_frame_invariant_update_device l st dvp h0 h1

let dstate_p_or_null_frame_invariant #idc l stp dvp h0 h1 =
  if dstate_p_g_is_null stp then ()
  else
    let st = B.deref h0 stp.stp in
    dstate_t_frame_invariant l st h0 h1

let dstate_p_or_null_frame_invariant_update_device #idc l stp dvp h0 h1 =
  if dstate_p_g_is_null stp then ()
  else
    let st = B.deref h0 stp.stp in
    dstate_t_frame_invariant_update_device l st dvp h0 h1

#push-options "--fuel 1"
let idc_pattern_length_not_zero (idc : valid_idc) :
  Lemma(List.Tot.length (idc_get_pattern idc).messages > 0) = ()
#push-options

[@@ noextract_to "Karamel"] noextract
let dstate_t_handshake_shared_props_base
  (#idc : valid_idc)
  (h1 h2 : mem)
  (dst1 : dstate_t idc{dstate_t_is_handshake dst1})
  (dst2 : dstate_t idc) :
  GTot Type0 =
  let initiator = dstate_t_is_initiator dst1 in
  let isc = idc_get_isc idc initiator in
  let Mkgddstate_t initiator1 id1 info1 spriv1 spub1 pid1 pinfo1 dv1 st1 = gdestruct_dstate_t dst1 in
  let Mkgddstate_t initiator2 id2 info2 spriv2 spub2 pid2 pinfo2 dv2 st2 = gdestruct_dstate_t dst2 in
  initiator1 = initiator2 /\
  dv1 == dv2 /\
  device_p_get_cstate h1 dv1 == device_p_get_cstate h2 dv2 /\
  id1 == id2 /\
  info1 == info2 /\
  // TODO: Is the peer info footprint equality really necessary?
//  peer_info_footprint pinfo1 == peer_info_footprint pinfo2 /\
  pinfo1 == pinfo2
  // The core footprint and the keys will be taken care of by the additional requirements

[@@ noextract_to "Karamel"] noextract
let dstate_t_handshake_no_split_shared_props
  (#idc : valid_idc)
  (h1 h2 : mem)
  (dst1 : dstate_t idc{dstate_t_is_handshake dst1})
  (dst2 : dstate_t idc{dstate_t_is_handshake dst2}) :
  GTot Type0 =
  let initiator = dstate_t_is_initiator dst1 in
  let isc = idc_get_isc idc initiator in
  dstate_t_handshake_shared_props_base h1 h2 dst1 dst2 /\
  state_t_handshake_shared_props #isc #initiator (dstate_t_get_state dst1) (dstate_t_get_state dst2)

[@@ noextract_to "Karamel"] noextract
let dstate_t_handshake_shared_props
  (#idc : valid_idc)
  (r : rid) // some dynamic allocations might have happened because of split
  (h1 h2 : mem)
  (dst1 : dstate_t idc{dstate_t_is_handshake dst1})
  (dst2 : dstate_t idc) :
  GTot Type0 =
  let initiator = dstate_t_is_initiator dst1 in
  let isc = idc_get_isc idc initiator in
  dstate_t_handshake_shared_props_base h1 h2 dst1 dst2 /\
   begin
   if dstate_t_is_handshake dst2 then
     state_t_handshake_shared_props #isc #initiator (dstate_t_get_state dst1) (dstate_t_get_state dst2)
   else
     B.(loc_includes (loc_union (region_to_loc r) (dstate_t_footprint dst1))
                     (dstate_t_footprint dst2))
   end

[@@ noextract_to "Karamel"] noextract
let dstate_p_handshake_shared_props
  (#idc : valid_idc)
  (h1 h2 : mem)
  (dstp1 : dstate_p idc{dstate_p_g_is_handshake h1 dstp1})
  (dstp2 : dstate_p idc) :
  GTot Type0 =
  let dst1 = B.deref h1 dstp1.stp in
  let dst2 = B.deref h2 dstp2.stp in
  dstp1.stp_r == dstp2.stp_r /\
  dstate_t_handshake_shared_props dstp1.stp_r h1 h2 dst1 dst2

let dstate_p_g_get_device_disjoint_regions #idc stp h0 = ()

(**** Utilities *)
let mk_dstate_p_get_status #idc dst_p =
  let dst = B.index dst_p.stp 0ul in
  match dst with
  | DS_Initiator st _ _ _ _ _ _ _ ->
    begin match st with
    | IMS_Handshake step _ _ _ _ _ _ _ _ _ _ ->
      if FStar.UInt32.(step %^ 2ul) = 0ul then Handshake_write
      else Handshake_read
    | IMS_Transport _ _ _ _ _ _ -> Transport
    end
  | DS_Responder st _ _ _ _ _ _ _ ->
    begin match st with
    | IMS_Handshake step _ _ _ _ _ _ _ _ _ _ ->
      if FStar.UInt32.(step %^ 2ul) = 0ul then Handshake_read
      else Handshake_write
    | IMS_Transport _ _ _ _ _ _ -> Transport
    end

// Given a payload length, return the length of the next message to receive/send.
// If we are in the handshake phase, it depends on the current step.
// In transport phase, it is always payload_len + aead_tag (note that the state
// can't necessarily send/receive a message).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_compute_next_message_len
  (#idc:valid_idc) (out : B.pointer size_t)
  (dst : dstate_t idc) (payload_len : size_t) :
  Stack bool
  (requires (fun h0 ->
    B.live h0 out /\
    dstate_t_invariant h0 dst))
  (ensures (fun h0 b h1 ->
    B.(modifies (loc_buffer out) h0 h1) /\
    begin
    let nc = idc_get_config idc in
    let pat = idc_get_pattern idc in
    let dst_v = dstate_t_v h0 dst in
    (**) normalize_term_spec(List.Tot.length pat.messages);
    if b then
      match dstate_get_status dst_v with
      | Spec.Noise.API.State.Handshake_receive step
      | Spec.Noise.API.State.Handshake_send step ->
        step < List.Tot.length pat.messages /\
        size_v (B.deref h1 out) =
          size_v payload_len + compute_message_length nc pat step
      | Spec.Noise.API.State.Transport ->
        size_v (B.deref h1 out) = size_v payload_len + aead_tag_vsv
    else True
    end))

let mk_dstate_t_compute_next_message_len #idc out dst payload_len =
  (**) normalize_term_spec(List.Tot.length (idc_get_pattern idc).messages);
  match dst with
  | DS_Initiator st _ _ _ _ _ _ _ ->
    mk_state_t_compute_next_message_len st payload_len out
  | DS_Responder st _ _ _ _ _ _ _ ->
    mk_state_t_compute_next_message_len st payload_len out

let mk_dstate_p_compute_next_message_len #idc out dst_p payload_len =
  let dst = B.index dst_p.stp 0ul in
  mk_dstate_t_compute_next_message_len #idc out dst payload_len

let mk_dstate_p_get_hash #idc out dst_p =
  (**) let h0 = ST.get () in
  let dst = B.index dst_p.stp 0ul in
  let h =
    match dst with
    | DS_Initiator st _ _ _ _ _ _ _ ->
      (**) state_t_get_hash_lem st h0;
      (**) state_t_footprint_full_inclusion_lem st;
      state_t_get_hash st
    | DS_Responder st _ _ _ _ _ _ _ ->
      (**) state_t_get_hash_lem st h0;
      (**) state_t_footprint_full_inclusion_lem st;
      state_t_get_hash st
  in
  copy out h

let mk_dstate_p_get_id #idc stp =
  let st = B.index stp.stp 0ul in
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv -> id
  | DS_Responder st id info spriv spub pid pinfo dv -> id

let mk_dstate_p_get_info #idc out stp =
  let st = B.index stp.stp 0ul in
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv ->
    (idc_get_info idc).St.smficc_copy () out info
  | DS_Responder st id info spriv spub pid pinfo dv ->
    (idc_get_info idc).St.smficc_copy () out info

let mk_dstate_p_get_peer_id #idc stp =
  let st = B.index stp.stp 0ul in
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv -> pid
  | DS_Responder st id info spriv spub pid pinfo dv -> pid

let mk_dstate_p_get_peer_info #idc out stp =
  let st = B.index stp.stp 0ul in
  match st with
  | DS_Initiator st id info spriv spub pid pinfo dv ->
    if pid <> peer_id_none idc then
      begin
      (idc_get_info idc).St.smficc_copy () out pinfo;
      true
      end
    else false
  | DS_Responder st id info spriv spub pid pinfo dv ->
    if pid <> peer_id_none idc then
      begin
      (idc_get_info idc).St.smficc_copy () out pinfo;
      true
      end
    else false

(**** Create, free *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let dstate_t_create_st_pre :
     #idc:valid_idc
  -> r:HS.rid
  -> dvp:device_p idc // TODO: may be none in the future
  -> initiator:bool
  -> epriv:eprivate_key_t idc initiator
  -> epub:epublic_key_t idc initiator
  -> pid:opt_pid_t idc initiator
  -> h0:mem ->
  GTot Type0 =
  fun #idc r dvp initiator epriv epub pid h0 ->
  let pattern = idc_get_pattern idc in
  device_p_invariant h0 dvp /\
  ST.is_eternal_region r /\
  lbuffer_or_unit_live h0 epriv /\
  lbuffer_or_unit_live h0 epub /\
  begin
  let r_loc = region_to_loc r in
  let dv_loc = device_p_region_of dvp in
  let epriv_loc = lbuffer_or_unit_to_loc epriv in
  let epub_loc = lbuffer_or_unit_to_loc epub in
  B.all_disjoint [dv_loc; r_loc; epriv_loc; epub_loc]
  end /\
  get_hash_pre (idc_get_nc idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let dstate_t_create_st_post :
     #idc:valid_idc
  -> r:HS.rid
  -> dvp:device_p idc // TODO: may be none in the future
  -> initiator:bool
  -> epriv:eprivate_key_t idc initiator
  -> epub:epublic_key_t idc initiator
  -> pid:opt_pid_t idc initiator
  -> h0:mem
  -> res:ds_result_code (dstate_t idc)
  -> h1:mem ->
  GTot Type0 =
  fun #idc r dvp initiator epriv epub pid h0 res h1 ->
  B.(modifies (device_p_region_of dvp) h0 h1) /\
  device_p_invariant h1 dvp /\
  device_p_get_cstate h1 dvp == device_p_get_cstate h0 dvp /\
  device_p_g_get_static h1 dvp == device_p_g_get_static h0 dvp /\
  device_p_no_removal dvp h0 h1 /\
  begin
  let dv_v = device_p_v h0 dvp in
  let e_v =
    mk_keypair_from_keys_or_unit #(idc_get_isc idc initiator)
                                 #(isc_get_e (idc_get_isc idc initiator)) h0 epriv epub
  in
  let pid_v = opt_pid_v pid in
  match res, create_dstate dv_v initiator e_v pid_v with
  | Res st, Res (st'_v, dv'_v) ->
    dstate_t_invariant h1 st /\
    dstate_t_is_handshake st /\ // Not sure it is useful
    dstate_t_is_initiator st = initiator /\
    region_includes r (dstate_t_footprint st) /\
    dstate_t_get_device st == dvp /\
    device_p_v h1 dvp == dv'_v /\
    dstate_t_v h1 st == st'_v
  | Fail _, _ ->
    device_p_v h1 dvp == device_p_v h0 dvp
  | _ -> False
  end

/// The proof is too long if the lookup is performed in the create function:
/// we thus split it.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_create_no_lookup :
     #idc:valid_idc
  -> ssi:ss_impls (idc_get_nc idc)
  -> initialize:initialize_handshake_state_st (idc_get_nc idc)
  -> r:HS.rid
  -> dvp:device_p idc // TODO: may be none in the future
  -> dv:device_t idc // dvp should have been dereferenced in the caller function
  -> initiator:bool
  -> epriv:eprivate_key_t idc initiator
  -> epub:epublic_key_t idc initiator
  -> pid:opt_pid_t idc initiator
  -> peer_ptr:peer_p_or_null idc ->
  ST (ds_result_code (dstate_t idc))
  (requires (fun h0 ->
    dstate_t_create_st_pre r dvp initiator epriv epub pid h0 /\
    dv == B.deref h0 dvp.dvp /\
    // We should have checked that the state counter is not saturated
    dv.dv_states_counter <> state_id_max idc /\
    // Additional conditions on the peer pointer
    peer_p_or_null_invariant h0 peer_ptr dvp /\
    (knows_remote_at_init idc initiator ==> Some? (opt_pid_v pid)) /\
    begin
    match opt_pid_v pid with
    | None -> peer_p_g_is_null peer_ptr
    | Some pid_v ->
      let dv_v = device_p_v h0 dvp in
      match lookup_peer_by_id dv_v pid_v with
      | None -> False
      | Some p_v ->
        not (peer_p_g_is_null peer_ptr) /\
        peer_p_v h0 peer_ptr == p_v
    end))
  (ensures (fun h0 res h1 ->
    dstate_t_create_st_post r dvp initiator epriv epub pid h0 res h1))

/// Conditional copy with a weak postcondition (no freshness assertion).
/// Having a weaker postcondition can make the proofs faster.
inline_for_extraction noextract
val lbuffer_or_unit_conditional_malloc_copy_relaxed
  (#a : Type0) (#len : size_t{size_v len > 0}) (#b1 : bool)
  (b2 : bool{b2 ==> b1})
  (r : HS.rid) (init : a)
  (i : type_or_unit (lbuffer a len) b1) :
  ST (type_or_unit (lbuffer a len) b2)
  (requires (fun h0 ->
    B.live h0 (lbuffer_or_unit_to_buffer i) /\
    ST.is_eternal_region r))
  (ensures (fun h0 o h1 ->
    B.(modifies loc_none h0 h1) /\
    B.(loc_includes (loc_region_only true r) (lbuffer_or_unit_to_loc o)) /\
    lbuffer_or_unit_freeable o /\
    B.live h1 (lbuffer_or_unit_to_buffer o) /\
    (if b2 then lbuffer_or_unit_to_seq h1 o == lbuffer_or_unit_to_seq h0 i else True)))

let lbuffer_or_unit_conditional_malloc_copy_relaxed #a #len #b1 b2 r init i =
  if b2 then lbuffer_or_unit_malloc_copy #a #len #b1 r init i
  else (() <: type_or_unit (lbuffer a len) b2)

/// Another helper to remove as many stateful [if ... then ... else ...] as
/// possible (cause proof explosions).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val allocate_peer_info
  (#idc : valid_idc)
  (r_pinfo : HS.rid)
  (initiator : bool)
  (peer_ptr : peer_p_or_null idc) :
  ST (
    [@inline_let] let nc = idc_get_nc idc in
    [@inline_let] let knows_rs = with_onorm (knows_rs_at_init idc initiator) in
    [@inline_let] let knows_psk = with_onorm (knows_psk_at_init idc initiator) in
    [@inline_let] let isc = idc_get_isc idc initiator in
    [@inline_let] let is_psk = with_onorm (idc_is_psk idc) in
    [@inline_let] let has_remote_s = with_onorm (isc_get_rs isc) in
    peer_info_t idc &
    public_key_t_or_unit nc (knows_rs && has_remote_s) &
    preshared_key_t_or_unit (knows_psk && is_psk))
  (requires (fun h0 ->
    ST.is_eternal_region r_pinfo /\
    peer_p_live h0 peer_ptr /\
    begin
    let knows_remote = knows_remote_at_init idc initiator in
    knows_remote ==> (not (peer_p_g_is_null peer_ptr) /\ peer_p_invariant h0 peer_ptr)
    end
    ))
  (ensures (fun h0 (st_pinfo, rs, psk) h1 ->
    let nc = idc_get_nc idc in
    let knows_rs = knows_rs_at_init idc initiator in
    let knows_psk = knows_psk_at_init idc initiator in
    let isc = idc_get_isc idc initiator in
    let is_psk = idc_is_psk idc in
    let has_remote_s = isc_get_rs isc in
    let knows_remote = knows_remote_at_init idc initiator in

    B.(modifies loc_none h0 h1) /\
    region_includes r_pinfo (peer_info_footprint st_pinfo) /\
    peer_info_invariant h1 st_pinfo /\
    peer_info_freeable h1 st_pinfo /\
    begin
    if knows_remote then
      let peer = B.deref h0 peer_ptr.pp in
      peer_info_v h1 st_pinfo == (peer_p_v h0 peer_ptr).DSpec.p_info /\
      (if knows_rs && has_remote_s then rs == peer.p_s else True) /\
      (if knows_psk then psk == peer.p_psk else True)
    else True
    end))

let allocate_peer_info #idc r_pinfo initiator peer_ptr =
  (**) let h0 = ST.get () in
  [@inline_let] let nc = idc_get_nc idc in
  [@inline_let] let knows_rs = with_onorm (knows_rs_at_init idc initiator) in
  [@inline_let] let knows_psk = with_onorm (knows_psk_at_init idc initiator) in
  [@inline_let] let isc = idc_get_isc idc initiator in
  [@inline_let] let is_psk = with_onorm (idc_is_psk idc) in
  [@inline_let] let has_remote_s = with_onorm (isc_get_rs isc) in
  [@inline_let] let knows_remote = with_onorm (knows_remote_at_init idc initiator) in
  // Copy the looked up peer if there is, otherwise just allocate
  if knows_remote then
    begin
    let peer = B.index peer_ptr.pp 0ul in
    [@inline_let]
    let psk : preshared_key_t_or_unit (knows_psk && is_psk) =
      if knows_psk then peer.p_psk else () in
    [@inline_let]
    let rs : public_key_t_or_unit nc (knows_rs && has_remote_s) =
      if knows_rs && has_remote_s then peer.p_s else ()
    in
    (idc_get_info idc).St.smficc_clone r_pinfo peer.p_info, rs, psk
    end
  else (idc_get_info idc).St.smficc_malloc () r_pinfo, (), ()

#restart-solver
#push-options "--z3rlimit 1000 --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"
let mk_dstate_t_create_no_lookup #idc ssi initialize r dvp dv initiator epriv epub pid peer_ptr =
  [@inline_let] let nc = idc_get_nc idc in
  [@inline_let] let isc = idc_get_isc idc initiator in
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let knows_rs = with_onorm (knows_rs_at_init idc initiator) in
  [@inline_let] let knows_psk = with_onorm (knows_psk_at_init idc initiator) in
  [@inline_let] let knows_remote = with_onorm (knows_remote_at_init idc initiator) in
  [@inline_let] let is_psk = with_onorm (idc_is_psk idc) in
  [@inline_let] let has_remote_s = with_onorm (isc_get_rs isc) in

  (**) create_state_smi_pre_lem isc initiator knows_rs knows_psk;
  (**) let h0 = ST.get () in

  [@inline_let] let has_s = with_onorm (isc_get_s (idc_get_isc idc initiator)) in
  (**) let (r_state, r_info, r_pinfo, r_bufs) = create_regions4 r in
  (**) let h1 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) let (r_bufs_spriv, r_bufs_spub) = create_regions2 r_bufs in
  (**) assert(region_includes_region r r_bufs_spriv);
  (**) assert(region_includes_region r r_bufs_spub);
  (**) let h2 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  (* Static keys *)
  let st_spriv : sprivate_key_t idc initiator =
    // Devices are designed so that they can generate both initiators and responders:
    // it is thus not because a device has static keys that the dstate has some too
    lbuffer_or_unit_conditional_malloc_copy_relaxed has_s r_bufs_spriv (u8 0) dv.dv_spriv
  in
  (**) let h3 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h3;
  // This assertion is needed
  (**) assert(region_includes r_bufs_spriv (lbuffer_or_unit_to_loc st_spriv));
  (**) assert(region_includes r_bufs (lbuffer_or_unit_to_loc st_spriv));
  let st_spub : spublic_key_t idc initiator =
    lbuffer_or_unit_conditional_malloc_copy_relaxed has_s r_bufs_spub (u8 0) dv.dv_spub
  in
  (**) let h4 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h4;
  // This assertion is needed
  (**) assert(region_includes r_bufs_spub (lbuffer_or_unit_to_loc st_spub));
  (**) assert(region_includes r_bufs (lbuffer_or_unit_to_loc st_spub));

  (* Info *)
  let st_info = (idc_get_info idc).St.smficc_clone #() r_info dv.dv_info in
  (**) let h5 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h5;

  (* Peer information *)
  (**) peer_p_or_null_frame_invariant B.loc_none peer_ptr dvp h0 h5;
  let st_pinfo, rs, psk = allocate_peer_info #idc r_pinfo initiator peer_ptr in
  (* State *)
  (**) let h6 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h6;
  begin
  (**) let r_state_loc = region_to_loc r_state in
  (**) let spriv_loc = lbuffer_or_unit_to_loc st_spriv in
  (**) let spub_loc = lbuffer_or_unit_to_loc st_spub in
  (**) let epriv_loc = lbuffer_or_unit_to_loc epriv in
  (**) let epub_loc = lbuffer_or_unit_to_loc epub in
  (**) let rs_loc = lbuffer_or_unit_to_loc rs in
  (**) let psk_loc = lbuffer_or_unit_to_loc psk in
  (**) let prlg_loc = B.loc_buffer (dv.dv_prologue.buffer <: buffer uint8) in

  (**) assert(region_includes r_bufs spriv_loc);
  (**) assert(region_includes r_bufs spub_loc);
  // Those ones are not necessary here, but useful for later
  (**) assert(region_includes r_pinfo (peer_info_footprint st_pinfo));
  (**) assert(region_includes r_info (info_footprint st_info));

  (**) assert(
  (**)   LowStar.Monotonic.Buffer.all_disjoint [
  (**)     r_state_loc; spriv_loc; spub_loc; epriv_loc; epub_loc; rs_loc; psk_loc; prlg_loc
  (**)   ])
  end;

  (* Update the device's states counter *)
  [@inline_let] let st_id = dv.dv_states_counter in
  [@inline_let]
  let dv' = { dv with dv_states_counter = (idc_get_sid idc).id_increment st_id } in
  B.upd dvp.dvp 0ul dv';
  (**) let h7 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h7;

  (* Initialize the state *)
  let st =
    mk_state_t_create_state #isc (convert_type ssi) initialize r_state
      initiator dv.dv_prologue.size dv.dv_prologue.buffer
      st_spriv st_spub epriv epub #knows_rs rs #knows_psk psk
  in

  (**) let h8 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h8;
  (**) assert(B.loc_includes (region_to_loc r) (region_to_loc r_state));
  (**) assert(B.loc_includes (region_to_loc r) (region_to_loc r_info));
  (**) assert(B.loc_includes (region_to_loc r) (region_to_loc r_pinfo));
  (**) assert(B.loc_includes (region_to_loc r) (region_to_loc r_bufs));
  (**) assert(B.loc_includes (region_to_loc r) (state_t_core_footprint st));
  (**) assert(B.loc_includes (region_to_loc r) (info_footprint st_info));
  (**) assert(B.loc_includes (region_to_loc r) (peer_info_footprint st_pinfo));
  (**) assert(B.loc_includes (region_to_loc r) (lbuffer_or_unit_to_loc st_spriv));
  (**) assert(B.loc_includes (region_to_loc r) (lbuffer_or_unit_to_loc st_spub));
  (**) assert(B.(modifies loc_none h0 h6));
  (**) device_p_frame_invariant B.loc_none dvp h0 h6;
  begin
  (**) let l = device_p_region_of dvp in
  (**) assert(B.(modifies l h6 h8)); 
  (**) info_frame_invariant l st_info h5 h7;
  (**) info_frame_freeable l st_info h5 h7;
  (**) info_frame_invariant l st_pinfo h6 h7;
  (**) info_frame_freeable l st_pinfo h6 h7;

  (**) info_frame_invariant B.loc_none st_info h7 h8;
  (**) info_frame_freeable B.loc_none st_info h7 h8;
  (**) info_frame_invariant B.loc_none st_pinfo h7 h8;
  (**) info_frame_freeable B.loc_none st_pinfo h7 h8
  end;
  (**) assert(device_p_invariant h8 dvp);

  // device_p_no_removal
  begin
  (**) let peers_l = device_p_g_get_peers h6 dvp in
  (**) M.list_in_listP_refl peers_l;
  (**) LL.frame_invariant dv.dv_peers B.loc_none h0 h6;
  (**) assert(device_p_no_removal dvp h6 h7);
  (**) device_p_no_removal_trans_lem dvp h0 h6 h7;
  (**) assert(device_p_no_removal dvp h0 h7);
  (**) device_p_no_removal_trans_lem dvp h0 h7 h8;
  (**) assert(device_p_no_removal dvp h0 h8)
  end;

  begin
  (**) let sc = dconfig_to_sconfig (idc_get_dc idc) in
  (**) let isc = idc_get_isc idc initiator in
  (**) let dv_v = device_p_v h0 dvp in
  (**) let prlg_v = as_seq h8 (Mksized_buffer?.buffer (Mkdevice_t_raw?.dv_prologue dv)) in
  (**) let s_v = mk_keypair_from_keys_or_unit #isc #(isc_get_s isc) h8 st_spriv st_spub in
  (**) let e_v = mk_keypair_from_keys_or_unit #isc #(isc_get_e isc) h0 epriv epub in
  (**) let rs_v = lbuffer_or_unit_to_opt_lseq h8 rs in
  (**) let psk_v = lbuffer_or_unit_to_opt_lseq h8 psk in
  (**) let si_v = if isc_get_s isc then dv_v.DSpec.dv_static_identity else None in
  (**) assert(dv_v.DSpec.dv_prologue == prlg_v);
  (**) assert(si_v == s_v);
  (**) assert(dv_v == device_p_v h6 dvp);
  (**) begin
  (**) if knows_remote then
  (**)   begin
  (**)   let peer_v = peer_p_v h0 peer_ptr in
  (**)   let pinfo_v = idc_get_info_v h7 st_pinfo in
  (**)   let opt_pid_v = opt_pid_v pid in
  (**)   assert(Res (Some peer_v) == lookup_opt_peer dv_v opt_pid_v);
  (**)   assert(pinfo_v == peer_v.DSpec.p_info);
  // Note that the equality with the remote s is a bit complex
  (**)   assert(psk_v == peer_v.DSpec.p_psk)
  (**)   end
  (**) else
  (**)   begin
  (**)   assert(rs_v == None);
  (**)   assert(psk_v == None)
  (**)   end
  (**) end;
  (**) 
  (**) assert(
  (**)   match create_state (isc_get_pattern isc) prlg_v
  (**)                      initiator s_v e_v rs_v psk_v with
  (**)   | Res st'_v ->
  (**)     let smi = create_state_smi isc knows_rs knows_psk in
  (**)     handshake_state_t_v_with_smi h8 st smi == st'_v /\
  (**)     UInt32.v (state_t_handshake_get_step st) = 0 /\
  (**)     (st_spriv, st_spub) == state_t_handshake_get_static st
  (**)   | _ -> False)
  end;

  (* Return *)
  [@inline_let]
  let st_pid = if knows_remote then pid else (idc_get_pid idc).id_none in
  [@inline_let]
  let dst =
    if initiator then DS_Initiator st st_id st_info st_spriv st_spub st_pid st_pinfo dvp
    else DS_Responder st st_id st_info st_spriv st_spub st_pid st_pinfo dvp
  in

  begin
  (**) state_t_handshake_footprint_inclusion_lem #isc st;
  (**) assert(dstate_t_invariant h8 dst);
  (**) assert(dstate_t_is_handshake dst);
  (**) assert(region_includes r (dstate_t_footprint dst));
  (**) let dv_v = device_p_v h0 dvp in
  (**) let e_v = mk_keypair_from_keys_or_unit #(idc_get_isc idc initiator) #(isc_get_e (idc_get_isc idc initiator)) h0 epriv epub in
  (**) let pid_v = opt_pid_v pid in
  (**) let dst_v = dstate_t_v h8 dst in
  (**) let res_v = create_dstate dv_v initiator e_v pid_v in
  (**) assert(Res? res_v);
  (**) let st'_v, dv'_v = Res?.v res_v in
  (**) let sc = dconfig_to_sconfig (idc_get_dc idc) in
  (**) let opt_info_v = if not (peer_p_g_is_null peer_ptr) then Some (peer_p_v h0 peer_ptr) else None in
  (**) let s_v = mk_keypair_from_keys_or_unit #isc #(isc_get_s isc) h8 st_spriv st_spub in
  (**) let rs_v = lbuffer_or_unit_to_opt_lseq h8 rs in
  (**) let psk_v = lbuffer_or_unit_to_opt_lseq h8 psk in
  (**) let smi = create_state_smi isc knows_rs knows_psk in
  (**) assert(isc_step_to_smi #initiator isc 0 == smi);
  (**) assert(
  (**)   st'_v.Spec.dst_state ==
  (**)   (Res?.v (create_state #sc pattern dv_v.DSpec.dv_prologue initiator s_v e_v rs_v psk_v)));
  (**) assert(
  (**)   match res_v with
  (**)   | Res (dst'_v, dv'_v) ->
  (**)     dst_v.Spec.dst_state == dst'_v.Spec.dst_state /\
  (**)     dst_v.Spec.dst_pid == dst'_v.Spec.dst_pid /\
  (**)     dst_v.Spec.dst_pinfo == dst'_v.Spec.dst_pinfo /\
  (**)     dv'_v == device_p_v h8 dvp /\
  (**)     dstate_t_v h8 dst == dst'_v
  (**)   | _ -> False)
  end;
  Res dst
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_create :
     #idc:valid_idc
  -> ssi:ss_impls (idc_get_nc idc)
  -> initialize:initialize_handshake_state_st (idc_get_nc idc)
  -> r:HS.rid
  -> dvp:device_p idc // TODO: may be none in the future
  -> initiator:bool
  -> epriv:eprivate_key_t idc initiator
  -> epub:epublic_key_t idc initiator
  -> pid:opt_pid_t idc initiator ->
  ST (ds_result_code (dstate_t idc))
  (requires (fun h0 ->
    dstate_t_create_st_pre r dvp initiator epriv epub pid h0))
  (ensures (fun h0 res h1 ->
    dstate_t_create_st_post r dvp initiator epriv epub pid h0 res h1))

#restart-solver
#push-options "--z3rlimit 200 --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"
let mk_dstate_t_create #idc ssi initialize r dvp initiator epriv epub pid =
  [@inline_let] let nc = idc_get_nc idc in
  [@inline_let] let isc = idc_get_isc idc initiator in
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let knows_rs = with_onorm (knows_rs_at_init idc initiator) in
  [@inline_let] let knows_psk = with_onorm (knows_psk_at_init idc initiator) in
  [@inline_let] let knows_remote = with_onorm (knows_remote_at_init idc initiator) in
  [@inline_let] let is_psk = with_onorm (idc_is_psk idc) in
  [@inline_let] let has_remote_s = with_onorm (isc_get_rs isc) in
  (**) idc_pre_receives_rs_lem idc initiator;
  (**) let h0 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  let dv = B.index dvp.dvp 0ul in
  (**) let h1 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) device_p_frame_invariant B.loc_none dvp h0 h1;
  if dv.dv_states_counter = state_id_max idc then
    // TODO: we need a more specific error code - note that it is only internal,
    // so it is ok for now.
    Fail CIncorrect_transition
  else
    begin
    let peer_ptr : peer_p_or_null idc =
      if knows_remote then
        mk_device_p_lookup_peer_by_id dvp pid
      else peer_p_null idc
    in
    (**) let h2 = ST.get () in
    (**) B.loc_unused_in_not_unused_in_disjoint h2;
    (**) device_p_frame_invariant B.loc_none dvp h1 h2;
    (* Check the peer *)
    (**) assert(isc_get_psk isc == is_psk);
    (**) create_state_smi_pre_lem isc initiator knows_rs knows_psk;
    (**) assert(create_state_smi_pre isc initiator knows_rs knows_psk);
    let p_is_null = if knows_remote then peer_p_is_null peer_ptr else true in
    if knows_remote && p_is_null then
      Fail CUnknown_peer_id
    else
      begin
      (**) let h3 = ST.get () in
      (**) assert(B.(modifies loc_none h0 h3));
      (**) assert(device_p_no_removal dvp h0 h3);
      let res = mk_dstate_t_create_no_lookup ssi initialize r dvp dv initiator epriv epub pid peer_ptr in
      (**) let h4 = ST.get () in
      (**) device_p_no_removal_trans_lem dvp h0 h3 h4;
      res
      end
    end
#pop-options

[@@ noextract_to "Karamel"] noextract
val dstate_create_not_stuck_lem
  (#idc : valid_idc)
  (h : mem) (stp : dstate_p idc)
  (dv : device (idc_get_dc idc))
  (initiator : bool)
  (e : option (keypair (idc_get_config idc)))
  (opt_pid:option peer_id) :
  Lemma
  (requires (
    dstate_p_invariant h stp /\
    Res? (create_dstate dv initiator e opt_pid) /\
    dstate_p_v h stp == fst (Res?.v (create_dstate dv initiator e opt_pid))))
  (ensures (
    not (dstate_p_is_gstuck h stp)))

let dstate_create_not_stuck_lem #idc h stp dv initiator e opt_pid = ()

#push-options "--z3rlimit 100 --ifuel 0 --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"
let mk_dstate_p_create #idc ssi initialize initiator r0 dvp epriv epub pid =
  (**) let h0 = ST.get () in
  // We don't allocate directly in the region provided by the user.
  // This allows us to prove that the state footprint is always disjoint
  // from the stack later on. See [dstate_p_invariant] more more information.
  (**) let (r, r_state, r_ptr, r_split, r_pid) = create_regions_non_root_4 r0 in
  (**) let h0_1 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h0_1;

  let res = mk_dstate_t_create #idc ssi initialize r_state dvp initiator epriv epub pid in

  (**) let h1 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) assert(device_p_no_removal dvp h0 h0_1);
  (**) assert(device_p_no_removal dvp h0_1 h1);
  (**) device_p_no_removal_trans_lem dvp h0 h0_1 h1;
  
  match res with
  | Fail e -> { stp = B.null; stp_r = r; stp_r_split = r; stp_r_pid = r; } // we don't care about the regions
  | Res st ->
    let ptr = B.malloc r_ptr st 1ul in
    (**) let h2 = ST.get () in
    (**) B.loc_unused_in_not_unused_in_disjoint h2;
    (**) dstate_t_frame_invariant B.loc_none st h1 h2;

    (**) assert(device_p_no_removal dvp h1 h2);
    (**) device_p_no_removal_trans_lem dvp h0 h1 h2;
    (**) assert(device_p_no_removal dvp h0 h2);

    [@inline_let]
    let dst_p = { stp = ptr; stp_r = r; stp_r_split = r_split; stp_r_pid = r_pid } in

    begin
    (**) let dst = B.deref h2 dst_p.stp in
    (**) let isc = idc_get_isc idc initiator in
    (**) let Mkgddstate_t initiator id info spriv spub pid pinfo dv st = gdestruct_dstate_t dst in
    (**) state_t_handshake_footprint_inclusion_lem #isc #initiator st;
    (**) let ptr_loc = B.loc_addr_of_buffer dst_p.stp in
    (**) let st_loc = dstate_t_footprint dst in
    (**) let r_split = region_to_loc dst_p.stp_r_split in
    (**) let dv_loc = device_p_region_of dv in
    // Unfortunately, doesn't work without those region inclusion assertions
    (**) assert(region_includes r_ptr ptr_loc);
    (**) assert(region_includes r_state st_loc);
    (**) assert(region_includes r ptr_loc);
    (**) assert(region_includes r st_loc)
   end;

   begin
   // Checking the post-condition
   (**) let dst_p = dst_p in
   (**) let dv_v = device_p_v h0 dvp in
   (**) let e_v = mk_keypair_from_keys_or_unit #(idc_get_isc idc initiator)
   (**)                                        #(isc_get_e (idc_get_isc idc initiator))
   (**)                                        h0 epriv epub in
   (**) let pid_v = opt_pid_v pid in
//   (**) assert(B.(modifies loc_none h0 h2));
   (**) assert(dstate_p_live h2 dst_p);
   (**) assert(dstate_p_invariant h2 dst_p);
   (**) assert(dstate_p_g_is_handshake h2 dst_p);
   (**) assert(dstate_p_g_is_initiator h2 dst_p = initiator);
   (**) assert(region_includes r (dstate_p_region_of dst_p));
   (**) assert(device_p_owns_dstate_p h2 dvp dst_p);
   (**) assert(
   (**)   match create_dstate dv_v initiator e_v pid_v with
   (**)   | Res (st'_v, dv'_v) ->
   (**)     device_p_v h2 dvp == dv'_v /\
   (**)     dstate_p_v h2 dst_p == st'_v
   (**)   | _ -> False);
   (**) dstate_create_not_stuck_lem h2 dst_p dv_v initiator e_v pid_v;
   (**) assert(not (dstate_p_is_gstuck h2 dst_p))
   end;
   
   dst_p
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_free :
     #idc:valid_idc
  -> st:dstate_t idc ->
  ST unit
  (requires (fun h0 ->
    dstate_t_invariant h0 st))
  (ensures (fun h0 res h1 ->
    B.(modifies (dstate_t_footprint st) h0 h1)))

#push-options "--z3rlimit 100"
let mk_dstate_t_free #idc st =
  (**) let h0 = ST.get () in
  match st with
  | DS_Initiator state id info spriv spub pid pinfo dv ->
    mk_state_t_free state;
    (**) let h1 = ST.get () in
    begin
    (**) let initiator = true in
    (**) let isc = idc_get_isc idc initiator in
    (**) state_t_footprint_inclusion_lem #isc #initiator state
    end;
    (idc_get_info idc).St.smficc_free () info;
    (idc_get_info idc).St.smficc_free () pinfo;
    lbuffer_or_unit_free spriv;
    lbuffer_or_unit_free spub
  | DS_Responder state id info spriv spub pid pinfo dv ->
    mk_state_t_free state;
    (**) let h1 = ST.get () in
    begin
    (**) let initiator = false in
    (**) let isc = idc_get_isc idc initiator in
    (**) state_t_footprint_inclusion_lem #isc #initiator state
    end;
    (idc_get_info idc).St.smficc_free () info;
    (idc_get_info idc).St.smficc_free () pinfo;
    lbuffer_or_unit_free spriv;
    lbuffer_or_unit_free spub
#pop-options

let mk_dstate_p_free #idc stp =
  (**) let h0 = ST.get () in
  let st = B.index stp.stp 0ul in
  (**) let h1 = ST.get () in
  (**) dstate_p_frame_invariant B.loc_none stp h0 h1;
  mk_dstate_t_free st;
  B.free stp.stp

(**** Handshake split *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_try_split :
     #idc : valid_idc
  -> split_impl:split_st (idc_get_nc idc)
  -> r : rid
  -> initiator : bool
  -> prev_step:UInt32.t
  -> dst : dstate_t idc{
      dstate_t_is_initiator dst = initiator /\
      dstate_t_is_handshake dst /\
      begin
      let step = UInt32.v (dstate_t_handshake_get_step dst) in
      step <= List.Tot.length (idc_get_pattern idc).messages /\
      step = UInt32.v prev_step + 1
      end} ->
  ST (dstate_t idc)
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    dstate_t_invariant h0 dst /\
    begin
    let r_loc = region_to_loc r in
    let state_loc = dstate_t_footprint_with_device dst in
    B.all_disjoint [r_loc; state_loc]
    end /\
    get_hash_pre (idc_get_nc idc)))
  (ensures (fun h0 dst1 h1 ->
    B.(modifies (dstate_t_core_footprint dst) h0 h1) /\
    begin
    let pattern = idc_get_pattern idc in
    let n = List.Tot.length pattern.messages in
    let st_v0 = dstate_t_v h0 dst in
    let st_v1 = dstate_t_v h1 dst1 in
    st_v1 == Spec.try_split st_v0
    end /\
    dstate_t_invariant h1 dst1 /\
    dstate_t_handshake_shared_props r h0 h1 dst dst1))

#push-options "--z3rlimit 100"
let mk_dstate_t_try_split #idc split_impl r initiator prev_step dst =
  (**) let h0 = ST.get () in
  [@inline_let] let isc = idc_get_isc idc initiator in
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let]
  let num_messages = with_onorm(List.Tot.length pattern.messages) in
  [@inline_let]
  let Mkddstate_t id info spriv spub pid pinfo dv st = destruct_dstate_t initiator dst in

  if FStar.UInt32.(prev_step =^ size (num_messages -1)) then
    begin
    [@inline_let]
    let smi = with_onorm(step_to_smi pattern initiator num_messages) in
    (**) check_pattern_valid_meta_info_lem initiator isc (UInt32.v prev_step);
    (**) state_t_handshake_footprint_inclusion_lem #isc #initiator st;
    (**) assert(B.loc_disjoint (region_to_loc r) (state_t_core_footprint st));
    (**) assert(isc_valid_meta_info isc smi);

    let st1 = mk_state_t_split #isc #initiator smi split_impl r st in

    (**) let h1 = ST.get () in
    begin
    (**) let l = state_t_core_footprint st in
//    (**) idc_get_pinfo_frame_invariant #idc l pinfo h0 h1;
//    (**) idc_get_pinfo_frame_freeable #idc l pinfo h0 h1;
    (**) device_p_frame_invariant l dv h0 h1;
    (**) state_t_footprint_inclusion_lem #isc st1
    end;

    [@inline_let]
    let dst1 =
      if initiator then DS_Initiator st1 id info spriv spub pid pinfo dv
      else DS_Responder st1 id info spriv spub pid pinfo dv
    in
    (**) assert(dstate_t_invariant h1 dst1);
    (**) assert(dstate_t_handshake_shared_props r h0 h1 dst dst1);
    dst1
    end
  else dst
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_p_set_stuck :
     #idc : valid_idc
  -> st : dstate_p idc ->
  ST unit
  (requires (fun h0 ->
    dstate_p_invariant h0 st))
  (ensures (fun h0 () h1 ->
    B.(modifies (dstate_p_core_footprint h0 st) h0 h1) /\
    dstate_p_invariant h1 st /\
    dstate_p_same_device st h0 h1 /\
    begin
    if dstate_p_g_is_handshake h0 st then dstate_p_is_gstuck h1 st
    else dstate_p_v h1 st == dstate_p_v h0 st
    end))

#push-options "--z3rlimit 100"
let mk_dstate_p_set_stuck #idc dst_p =
  (**) let h0 = ST.get () in
  let dst = B.index dst_p.stp 0ul in
  (**) let h1 = ST.get () in
  (**) dstate_p_frame_invariant B.loc_none dst_p h0 h1;
  begin match dst with
  | DS_Initiator st id info spriv spub pid pinfo dv ->
    [@inline_let] let st1 = state_t_set_stuck_with_invariant h1 st in
    [@inline_let] let dst1 : dstate_t idc = DS_Initiator st1 id info spriv spub pid pinfo dv in
    (**) assert(dstate_t_invariant h1 dst1);
    B.upd dst_p.stp 0ul dst1
  | DS_Responder st id info spriv spub pid pinfo dv ->
    [@inline_let] let st1 = state_t_set_stuck_with_invariant h1 st in
    [@inline_let] let dst1 : dstate_t idc = DS_Responder st1 id info spriv spub pid pinfo dv in
    B.upd dst_p.stp 0ul dst1
  end;
  (**) let h2 = ST.get () in
  (**) dstate_t_frame_invariant (B.loc_buffer dst_p.stp) dst h1 h2;
  (**) assert(dstate_p_invariant h2 dst_p)
#pop-options

(**** Handshake send message *)

/// To factorize the proofs, we fix the [initiator] value.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_handshake_write_aux :
     #idc : valid_idc
  -> initiator : bool
  -> impl : state_t_handshake_write_rec_impl initiator idc
  -> split_impl: split_st (idc_get_nc idc)
  -> r : rid
  -> payload_len : size_t
  -> payload : lbuffer uint8 payload_len
  -> st : dstate_t idc{
       dstate_t_is_initiator st = initiator /\
       dstate_t_is_handshake st /\
       begin
       let step = UInt32.v (dstate_t_handshake_get_step st) in
       step < List.Tot.length (idc_get_pattern idc).messages /\
       initiator = ((step%2)=0)
       end}
  -> outlen : size_t
  -> out : lbuffer uint8 outlen ->
  ST (ds_result_code (dstate_t idc))
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    dstate_t_invariant h0 st /\
    live h0 payload /\
    live h0 out /\
    begin
    let r_loc = region_to_loc r in
    let payload_loc = B.loc_buffer (payload <: buffer uint8) in
    let out_loc = B.loc_buffer (out <: buffer uint8) in
    let state_loc = dstate_t_footprint_with_device st in
    B.all_disjoint [r_loc; payload_loc; out_loc; state_loc]
    end /\
    get_aead_pre (idc_get_nc idc) /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))
  (ensures (fun h0 res h1 ->
    B.(modifies (loc_union (dstate_t_core_footprint st)
                (loc_buffer (out <: buffer uint8))) h0 h1) /\
    // Adding those for security
    live h1 payload /\ live h1 out /\
    begin
    let st_v0 = dstate_t_v h0 st in
    let payload_v = as_seq h0 payload in
    let res_v = handshake_write payload_v st_v0 in

    match res with
    | Res st1 ->
      Res? res_v /\
      begin
      let Res (out'_v, st1'_v) = res_v in
      dstate_t_v h1 st1 == st1'_v /\
      as_seq h1 out == out'_v /\
      dstate_t_is_handshake st /\
      dstate_t_invariant h1 st1 /\
      dstate_t_handshake_shared_props r h0 h1 st st1
      end
    | Fail _ ->
      dstate_t_invariant h1 st
    | _ -> False
    end))

#push-options "--z3rlimit 500"
let mk_dstate_t_handshake_write_aux
  #idc initiator impl split_impl r payload_len payload dst outlen out =
  (**) let h0 = ST.get () in
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let init_isc = idc_get_isc idc true in
  [@inline_let] let resp_isc = idc_get_isc idc false in
  [@inline_let] let isc = idc_get_isc idc initiator in
  [@inline_let]
  let Mkddstate_t id info spriv spub pid pinfo dv st = destruct_dstate_t initiator dst in
  [@inline_let] let step = state_t_handshake_get_step st in
  
  begin
  (**) let st_v0 = dstate_t_v h0 dst in
  (**) let status = dstate_get_status st_v0 in
  (**) assert(status = Handshake_send (UInt32.v step))
  end;

  let res = impl step payload_len payload st outlen out in
//    mk_state_t_handshake_write_rec init_isc resp_isc step impls payload_len payload st
//                                   outlen out
//  in
  (**) let h1 = ST.get () in
  begin
  (**) let l = B.(loc_union (state_t_core_footprint st) (loc_buffer (out <: buffer uint8))) in
  (**) assert(B.modifies l h0 h1);
//  (**) idc_get_pinfo_frame_invariant #idc l pinfo h0 h1;
//  (**) idc_get_pinfo_frame_freeable #idc l pinfo h0 h1;
  (**) assert(info_invariant h1 info);
  (**) assert(info_freeable h1 info);
  (**) assert(info_invariant h1 pinfo);
  (**) assert(info_freeable h1 pinfo);
  (**) device_p_frame_invariant l dv h0 h1
  end;
  
  match res with
  | Fail e ->
    (**) assert(state_t_invariant h1 st);
    (**) assert(dstate_t_invariant h1 dst);
    Fail e
  | Res st1 ->
    // The type inferencer loops if we don't insert [convert_type]
    // See: https://github.com/FStarLang/FStar/issues/2184
    [@inline_let]
    let dst1 : dstate_t idc = 
      if initiator then DS_Initiator (convert_type #(state_t (idc_get_isc idc true) true) #(state_t (idc_get_isc idc true) true) st1) id info spriv spub pid pinfo dv
      else DS_Responder (convert_type #(state_t (idc_get_isc idc false) false) #(state_t (idc_get_isc idc false) false) st1) id info spriv spub pid pinfo dv
    in

    begin
    (**) let step0 = UInt32.v step in
    (**) let st_v0 = dstate_t_v h0 dst in
    (**) let st_v1 = dstate_t_v h1 dst1 in
    (**) assert(dstate_t_handshake_get_step_v dst1 = step0 + 1);
    (**) let status1 = dstate_get_status st_v1 in
    (**) assert(status1 = Handshake_receive (step0 + 1))
    end;

    (**) state_t_handshake_footprint_inclusion_lem #isc #initiator st;
    (**) state_t_handshake_footprint_inclusion_lem #isc #initiator st1;
    begin
    (**) let num_messages = List.Tot.length pattern.messages in
    (**) check_pattern_messagei_lem pattern (UInt32.v step);
    (**) assert(dstate_t_is_handshake dst1);
    (**) let step = UInt32.v step in
    (**) let smi0 = step_to_smi pattern initiator step in
    (**) let smi1 = step_to_smi pattern initiator (step + 1) in
    (**) let knows_at_init = knows_remote_at_init idc initiator in
    (**) assert(knows_remote pattern initiator step = knows_at_init || smi0.hsf.rs);
    (**) assert(knows_remote pattern initiator (step + 1) = knows_at_init || smi1.hsf.rs);
    (**) assert(smi1.hsf.rs = smi0.hsf.rs);
    (**) assert(knows_remote pattern initiator step = knows_remote pattern initiator (step +1));
    (**) assert(peer_id_is_some pid = knows_remote pattern initiator (step +1))
    end;
    (**) assert(dstate_t_invariant h1 dst1);
    Res (mk_dstate_t_try_split #idc split_impl r initiator step dst1)
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type dstate_t_handshake_write_st (idc : valid_idc) =
     r : rid
  -> payload_len : size_t
  -> payload : lbuffer uint8 payload_len
  -> st : dstate_t idc
  -> outlen : size_t
  -> out : lbuffer uint8 outlen ->
  ST (ds_result_code (dstate_t idc))
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    dstate_t_invariant h0 st /\
    live h0 payload /\
    live h0 out /\
    begin
    let r_loc = if dstate_t_is_handshake st then region_to_loc r else B.loc_none in
    let payload_loc = B.loc_buffer (payload <: buffer uint8) in
    let out_loc = B.loc_buffer (out <: buffer uint8) in
    let state_loc = dstate_t_footprint_with_device st in
    B.all_disjoint [r_loc; payload_loc; out_loc; state_loc]
    end /\
    get_aead_pre (idc_get_nc idc) /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))
  (ensures (fun h0 res h1 ->
    B.(modifies (loc_union (dstate_t_core_footprint st)
                (loc_buffer (out <: buffer uint8))) h0 h1) /\
    // Adding those for security
    live h1 payload /\ live h1 out /\
    begin
    let st_v0 = dstate_t_v h0 st in
    let payload_v = as_seq h0 payload in
    let res_v = handshake_write payload_v st_v0 in
    match res with
    | Res st1 ->
      Res? res_v /\
      begin
      let Res (out'_v, st1'_v) = res_v in
      dstate_t_v h1 st1 == st1'_v /\
      as_seq h1 out == out'_v /\
      dstate_t_is_handshake st /\
      dstate_t_invariant h1 st1 /\
      dstate_t_handshake_shared_props r h0 h1 st st1
      end
    | Fail _ ->
      dstate_t_invariant h1 st
    | _ -> False
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_handshake_write (#idc : valid_idc) :
     impl_init : state_t_handshake_write_rec_impl true idc
  -> impl_resp : state_t_handshake_write_rec_impl false idc
  -> split_impl : split_st (idc_get_nc idc) ->
  dstate_t_handshake_write_st idc

#push-options "--z3rlimit 200"
let mk_dstate_t_handshake_write
  #idc impl_init impl_resp split_impl r payload_len payload dst outlen out =
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let num_messages = with_onorm(List.Tot.length pattern.messages) in
  // Match on the state and reconstruct it. This may seem to be a no-op, but it
  // allows to statically know whether the state is initiator or responder in
  // the subsequent function calls, which is necessary to successfully extract the code.
  match dst with
  | DS_Initiator dst_st dst_id dst_info dst_spriv dst_spub dst_pid dst_pinfo dst_dv ->
    [@inline_let] let initiator = true in
    // Note that we reconstruct the match we perform below.
    // The reason is that it allows the code to reduce nicely later on, leadign
    // to more beautiful extracted code.
    begin match dst_st with
    | IMS_Handshake st_step st_cipher st_ck st_h st_spriv st_spub st_epriv st_epub st_rs st_re st_psk ->
      [@inline_let]
      let dst_st =
        IMS_Handshake st_step st_cipher st_ck st_h
                      st_spriv st_spub st_epriv st_epub st_rs st_re st_psk in
      [@inline_let]
      let dst = DS_Initiator dst_st dst_id dst_info dst_spriv dst_spub dst_pid dst_pinfo dst_dv in
      [@inline_let]
      let step = state_t_handshake_get_step dst_st in
      if FStar.UInt32.(step >=^ size num_messages)
      then Fail CIncorrect_transition
      else if not (initiator = (FStar.UInt32.rem step (size 2) = size 0))
      then Fail CIncorrect_transition
      else mk_dstate_t_handshake_write_aux
           #idc initiator impl_init split_impl r payload_len payload dst outlen out
    | IMS_Transport _ _ _ _ _ _ ->
      Fail CIncorrect_transition
    end
  | DS_Responder dst_st dst_id dst_info dst_spriv dst_spub dst_pid dst_pinfo dst_dv ->
    [@inline_let] let initiator = false in
    // We need to statically check that it is possible to send a message.
    // Otherwise, part of the code may not type check in ML (it would actually be unreachable)
    if with_onorm (can_send false pattern) then
      begin match dst_st with
      | IMS_Handshake st_step st_cipher st_ck st_h st_spriv st_spub st_epriv st_epub st_rs st_re st_psk ->
        [@inline_let]
        let dst_st =
          IMS_Handshake st_step st_cipher st_ck st_h
                        st_spriv st_spub st_epriv st_epub st_rs st_re st_psk in
        [@inline_let]
        let dst = DS_Responder dst_st dst_id dst_info dst_spriv dst_spub dst_pid dst_pinfo dst_dv in
        [@inline_let]
        let step = state_t_handshake_get_step dst_st in
        if FStar.UInt32.(step >=^ size num_messages)
        then Fail CIncorrect_transition
        else if not (initiator = (FStar.UInt32.rem step (size 2) = size 0))
        then Fail CIncorrect_transition
        else mk_dstate_t_handshake_write_aux
             #idc initiator impl_resp split_impl r payload_len payload dst outlen out
      | IMS_Transport _ _ _ _ _ _ ->
        Fail CIncorrect_transition
      end
    else
      Fail CIncorrect_transition
#pop-options

#restart-solver
#push-options "--z3rlimit 200"
let mk_dstate_p_handshake_write #idc impl_init impl_resp split_impl payload_len payload dst_p outlen out =
  (**) let h0 = ST.get () in
  let dst_p: dstate_p idc = dst_p in
  let stp: B.pointer (dstate_t idc) = dst_p.stp in
  let dst: dstate_t idc = B.index stp 0ul in
  (**) let r_split = dst_p.stp_r_split in // the region in which to allocate
  (**) let r_pid = dst_p.stp_r_pid in // the region we keep for future allocations (actually useless: only needed for the invariant)
  (**) let h1 = ST.get () in
  (**) dstate_p_frame_invariant B.loc_none dst_p h0 h1;
  (**) assert(region_includes_region dst_p.stp_r r_split);
  (**) assert(region_includes_region dst_p.stp_r r_pid);
  
  begin
  (**) let st = dstate_t_get_state #idc dst in
  (**) state_t_footprint_full_inclusion_lem st
  end;

  let res = 
    mk_dstate_t_handshake_write
      #idc impl_init impl_resp split_impl r_split payload_len payload dst outlen out
  in

  (**) let h2 = ST.get () in
  match res with
  | Fail e ->
    (* Update the state status so that it becomes unusable *)
    mk_dstate_p_set_stuck #idc dst_p;
    e
  | Res dst1 ->
    B.upd dst_p.stp 0ul dst1;
    (**) let h3 = ST.get () in
    begin
    (**) let st = dstate_t_get_state dst1 in
    (**) state_t_footprint_full_inclusion_lem st;
    (**) let l = B.loc_buffer dst_p.stp in
    (**) let dv = dstate_t_get_device dst1 in
    (**) dstate_t_frame_invariant l dst1 h2 h3;
    (**) assert(dstate_t_invariant h3 dst1);
    (**) assert(dstate_p_invariant h3 dst_p)
    end;

    CSuccess
#pop-options

(**** Handshake receive message *)

/// Not used: purely a sanity check for the proof of handshake receive message
[@@ noextract_to "Karamel"] noextract
val dstate_t_handshake_read_update_pinfo_lem
  (#idc : valid_idc) (dst : dstate_t idc{dstate_t_is_handshake dst})
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h0 : mem) :
  Lemma
  (requires (
    let step = UInt32.v (dstate_t_handshake_get_step dst) in
    let initiator = dstate_t_is_initiator dst in
    step < List.Tot.length (idc_get_pattern idc).messages /\
    initiator = ((step%2)=1) /\
    dstate_t_invariant h0 dst))
  (ensures (
    let input_v = as_seq h0 input in
    let Mkgddstate_t initiator id info spriv spub pid pinfo dvp st = gdestruct_dstate_t dst in
    let dv_v0 = device_p_v h0 dvp in
    let dc = idc_get_dc idc in
    let st_v0 = dstate_t_v h0 dst in
    let res_v = SSpec.handshake_read input_v st_v0.Spec.dst_state dv_v0 in
    match res_v with
    | Fail _ -> True
    | Res (opt_vpinfo_v, payload_v, st_v1) ->
      match st_v0.Spec.dst_pid, opt_vpinfo_v with
      | Some _, Some _ -> False
      | _ -> True))

let dstate_t_handshake_read_update_pinfo_lem
  (#idc : valid_idc) (dst : dstate_t idc{dstate_t_is_handshake dst})
  (inlen : size_t) (input : lbuffer uint8 inlen)
  (h0 : mem) =
  let pattern = idc_get_pattern idc in
  let step = UInt32.v (dstate_t_handshake_get_step dst) in
  let initiator = dstate_t_is_initiator dst in
  check_pattern_messagei_lem pattern step


/// Small helpers used to check if the current message contains a S token or not
/// SH: the extraction initially used [with_onorm (check_messagei_has_S ...)],
/// however this failed to extract because the normalizer was too agressive and the
/// equality test [step = uint_to_t i] got reduced to [UInt32.v step = i].
/// I tried wrapping this equality in a call to [norm] to protect it, but it didn't
/// work, so I finally resorted to more precise calls to the normalizer.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val check_messagei_has_S_aux
  (idc : valid_idc)
  (i : nat{i < List.Tot.length (idc_get_pattern idc).messages})
  (step : UInt32.t{UInt32.v step < List.Tot.length (idc_get_pattern idc).messages}) :
  Pure bool
  (requires True)
  (ensures (fun b ->
    let pattern = idc_get_pattern idc in
    let msg = List.Tot.index pattern.messages (UInt32.v step) in
    b = (List.Tot.mem S msg && i >= UInt32.v step)))
  (decreases i)

let rec check_messagei_has_S_aux idc i step =
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let msg = with_onorm (List.Tot.index pattern.messages i) in
  [@inline_let] let b1 = if i > 0 then check_messagei_has_S_aux idc (i-1) step else false in
  // This shouldn't introduce any unnecessary equality test in the extracted code.
  // i.e.: this should result in at most one equality test (because at most one
  // message contains S)
  if with_onorm (List.Tot.mem S msg)
  then b1 || step = UInt32.uint_to_t i else b1

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val check_messagei_has_S
  (idc : valid_idc)
  (step : UInt32.t{UInt32.v step < List.Tot.length (idc_get_pattern idc).messages}) :
  Pure bool
  (requires True)
  (ensures (fun b ->
    let pattern = idc_get_pattern idc in
    let msg = List.Tot.index pattern.messages (UInt32.v step) in
    b = List.Tot.mem S msg))

#push-options "--fuel 1"
let check_messagei_has_S idc step =
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let n = with_onorm (List.Tot.length pattern.messages) in
  // We need some fuel to prove that n > 0
  with_norm_steps [zeta; delta_only [`%check_messagei_has_S_aux ]; primops; iota]
  (check_messagei_has_S_aux idc (n-1) step)
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let mk_dstate_t_handshake_read_aux_no_split_st_gen_pre :
     #idc : valid_idc
  -> initiator : bool
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st : dstate_t idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  // Actually we don't always need this pointer
  -> pid_ptr : B.pointer_or_null (idc_get_pid idc).id_t
  -> h0 : mem -> GTot Type0 =
  fun #idc initiator payload_outlen payload_out st inlen input pid_ptr h0 ->
  let dvp = dstate_t_get_device st in
  let cstate = device_p_get_cstate h0 dvp in

  // Note: there is no dstate_t_invariant.
  // We put this requirement directly in the definition of mk_dstate_t_handshake_read_aux_no_split,
  // so that it allows us to share this pre with the certify_static helper.
  live h0 payload_out /\
  live h0 input /\
  idc_get_cstate_invariant h0 cstate /\
  B.live h0 pid_ptr /\
  begin
  let cstate_loc = idc_get_cstate_footprint cstate in
  let payload_loc = B.loc_buffer (payload_out <: buffer uint8) in
  let input_loc = B.loc_buffer (input <: buffer uint8) in
  let state_loc = dstate_t_footprint_with_device st in
  let pid_loc = if B.g_is_null pid_ptr then B.loc_none else B.loc_addr_of_buffer pid_ptr in
  B.all_disjoint [cstate_loc; payload_loc; input_loc; state_loc; pid_loc]
  end /\
  get_aead_pre (idc_get_nc idc) /\
  get_dh_pre (idc_get_nc idc) /\
  get_hash_pre (idc_get_nc idc)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
let mk_dstate_t_handshake_read_aux_no_split_st_post :
     #idc : valid_idc
  -> initiator : bool
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  // The original dstate
  -> st : dstate_t idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> pid_ptr : B.pointer (idc_get_pid idc).id_t
  -> h0 : mem
  -> res : ds_result_code (dstate_t idc)
  -> h1 : mem -> GTot Type0 =

  fun #idc initiator payload_outlen payload_out st inlen input pid_ptr h0 res h1 ->
  let dvp = dstate_t_get_device st in
  let cstate = device_p_get_cstate h0 dvp in
  let l =
    B.(loc_union (loc_union (dstate_t_core_footprint st)
                            (loc_buffer (payload_out <: buffer uint8)))
                 (loc_union (device_p_region_of dvp)
                            (B.loc_buffer pid_ptr)))
  in
  B.(modifies l h0 h1) /\
  device_p_no_removal dvp h0 h1 /\
  dstate_t_invariant h1 st /\
  // I don't understand why we need those liveness assertions
  live h1 payload_out /\ live h1 input /\ B.live h1 pid_ptr /\
  begin
  let st_v0 = dstate_t_v h0 st in
  let input_v = as_seq h0 input in
  let cst_v0 = idc_get_cstate_v h0 cstate in
  let dv_v0 = device_p_v h0 dvp in
  let res_v = handshake_read_no_split cst_v0 dv_v0 input_v st_v0 in
  begin match res with
  | Res st1 ->
    Res? res_v /\
    begin
    let Res (dv_v1, payload'_v, st1'_v) = res_v in
    let st1_v = dstate_t_v h1 st1 in
    st1_v == st1'_v /\
    as_seq h1 payload_out == payload'_v /\
    dstate_t_is_handshake st1 /\
    dstate_t_invariant h1 st1 /\
    dstate_t_handshake_no_split_shared_props h0 h1 st st1 /\
    device_p_v h1 dvp == dv_v1
    end
  | Fail _ ->
    device_p_v h1 dvp == device_p_v h0 dvp
  | _ -> False
  end
  end

/// To factorize the proofs, we fix the [initiator] value.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_handshake_read_aux_no_split_certify_static :
     #idc : valid_idc
  -> initiator : bool
  -> add_peer : device_p_add_peer_get_st idc
  -> payload_len : size_t
  -> payload:lbuffer uint8 payload_len
  // The device should have been dereferenced in the caller function
  -> dv:device_t idc
  -> dst : dstate_t idc{
       dstate_t_is_initiator dst = initiator /\
       dstate_t_is_handshake dst
    } ->
  ST (ds_result_code (dstate_t idc))
  (requires (fun h0 ->
    let inlen = 0ul in
    let input = B.null #uint8 in
    mk_dstate_t_handshake_read_aux_no_split_st_gen_pre
      initiator payload_len payload dst inlen input B.null h0 /\

    dstate_t_invariant_core h0 dst /\

    // The device was retrieve from the state, and dereferenced.
    // Note that the device invariant is already given by the state
    // invariant.
    dv == B.deref h0 (dstate_t_get_device dst).dvp /\

    is_hashable_size (idc_get_config idc) (size_v payload_len) /\

    // There can't be any psk, but we know it only from some checks that
    // happened before
    (idc_get_ks idc initiator).ks_psk = false /\

    begin
    let pattern = idc_get_pattern idc in
    let Mkgddstate_t initiator id info spriv spub pid pinfo dv st = gdestruct_dstate_t dst in
    let step = UInt32.v (state_t_handshake_get_step st) in
    let st_spriv, st_spub = state_t_handshake_get_static st in
    step > 0 /\ step <= List.Tot.length pattern.messages /\
    begin
    let smi = step_to_smi pattern initiator step in
    let has_s = check_messagei_has_S idc (size (step-1)) in
    smi.hsf.rs /\ has_s
    end
    end))

  (ensures (fun h0 res h1 ->
    let Mkgddstate_t initiator id info spriv spub pid pinfo dvp _ = gdestruct_dstate_t dst in
    let cstate = device_t_get_cstate dv in
    B.(modifies (loc_union (info_footprint pinfo) (device_p_region_of dvp)) h0 h1) /\
    device_p_no_removal dvp h0 h1 /\
    // In case of failure in handshake_read, we return the original state
    // (which may have been modified), and must still satisfy its invariant.
    // We need some precise conditions to show that it satisfies its invariant.
    dstate_t_invariant_core h1 dst /\
    // I don't understand why we need those liveness assertions
    live h1 payload /\
    begin
    let dst_v0 = dstate_t_v h0 dst in
    let st_v0 = dst_v0.Spec.dst_state in
    let id_v0 = dst_v0.Spec.dst_id in
    let info_v0 = dst_v0.Spec.dst_info in
    let payload_v = as_seq h0 payload in
    let cst_v0 = idc_get_cstate_v h0 cstate in
    let dv_v0 = device_p_v h0 dvp in
    let res_v = handshake_read_no_split_certify_static cst_v0 dv_v0 st_v0 id_v0 info_v0 payload_v in
    begin match res with
    | Res st1 ->
      Res? res_v /\
      begin
      let Res (dv_v1, payload'_v, st1'_v) = res_v in
      let st1_v = dstate_t_v h1 st1 in
      st1_v == st1'_v /\
      dstate_t_is_handshake st1 /\
      dstate_t_invariant h1 st1 /\
      dstate_t_handshake_no_split_shared_props h0 h1 dst st1 /\
      device_p_v h1 dvp == dv_v1
      end
    | Fail _ ->
      device_p_v h1 dvp == device_p_v h0 dvp
    | _ -> False
    end
    end))

#push-options "--z3rlimit 200"
let mk_dstate_t_handshake_read_aux_no_split_certify_static
  #idc initiator add_peer_impl payload_len payload dv dst =

  (**) let h0 = ST.get () in
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let init_isc = idc_get_isc idc true in
  [@inline_let] let resp_isc = idc_get_isc idc false in
  [@inline_let] let isc = idc_get_isc idc initiator in
  [@inline_let] let nc = idc_get_nc idc in
  [@inline_let]
  let Mkddstate_t id info spriv spub pid pinfo dvp st1 = destruct_dstate_t initiator dst in
  [@inline_let]
  let Mkdevice_t_raw dv_info dv_sk dv_spriv dv_spub prologue scounter peers pcounter cstate = dv in
  [@inline_let] let step = state_t_handshake_get_step st1 in

  (**) [@inline_let] let smi1 = step_to_smi pattern initiator (UInt32.v step) in

  begin
  (**) assert(smi1.hsf.rs);
  (**) let dst_v = dstate_t_v h0 dst in
  (**) assert(Some? (dstate_get_remote_static dst_v))
  end;

  [@inline_let]
  let rs = state_t_handshake_get_rs st1 in
  [@inline_let]
  let cert_state_st = idc_get_cstate idc in

  (**) state_t_footprint_full_inclusion_lem #isc #initiator st1;
  (**) state_t_handshake_invariant_stateful_live_rs #isc #initiator h0 st1;
  (**) assert(B.(loc_includes (state_t_core_footprint st1) (loc_addr_of_buffer (rs <: B.buffer uint8))));
  (**) assert(B.live h0 (rs <: buffer uint8));
  // We need the following for the call to [add_per]
  begin
  (**) state_t_handshake_footprint_inclusion_lem #isc #initiator st1;
  (**) let dv_loc = device_p_region_of dvp in
  (**) let pinfo_loc = info_footprint pinfo in
  (**) let rs_loc = lbuffer_or_unit_to_loc rs in
  (**) let st_loc = state_t_core_footprint st1 in
  (**) assert(B.loc_includes st_loc rs_loc);
  (**) assert(B.loc_disjoint dv_loc st_loc);
  (**) assert(B.loc_disjoint pinfo_loc st_loc);
  (**) assert(B.loc_disjoint dv_loc pinfo_loc);
  (**) assert(B.loc_disjoint dv_loc rs_loc);
  (**) assert(B.loc_disjoint pinfo_loc rs_loc)
  end;

  let cert_res = cert_state_st.certify cstate rs payload_len payload pinfo in

  (**) let h1 = ST.get () in
  begin
  (**) let l = info_footprint pinfo in
  (**) assert(B.loc_disjoint l (state_t_footprint st1));
  (**) handshake_state_t_frame_invariant l st1 smi1 h0 h1;
  (**) device_p_frame_invariant l dvp h0 h1;
  (**) assert(device_p_v h1 dvp == device_p_v h0 dvp);
  (**) assert(device_p_no_removal dvp h0 h1)
  end;

  [@inline_let]
  let certified =
    if with_onorm(cert_state_st.cst_always_success) then true
    else cert_state_st.cst_is_success cert_res
  in
  if certified then
    begin

    let pinfo_input = (idc_get_info idc).St.smficc_input_from_output () pinfo in
    (**) let h2 = ST.get () in

    let opt_npeer = add_peer_impl dvp pinfo_input rs () in

    (**) let h3 = ST.get () in
    begin
    (**) let l = device_p_region_of dvp in
    (**) assert(device_p_invariant h3 dvp);
    (**) assert(B.loc_disjoint l (state_t_footprint st1));
    (**) handshake_state_t_frame_invariant l st1 smi1 h1 h3;
    (**) info_frame_invariant l pinfo h1 h3;
    (**) info_frame_freeable l pinfo h1 h3;
    (**) info_frame_invariant l info h1 h3;
    (**) info_frame_freeable l info h1 h3;
    (**) device_p_frame_invariant (info_footprint pinfo) dvp h0 h2;
    (**) assert(device_p_no_removal dvp h0 h2);
    (**) assert(device_p_no_removal dvp h2 h3);
    (**) device_p_no_removal_trans_lem dvp h0 h2 h3
    end;
    if B.is_null opt_npeer.pp then
      Fail CPeer_conflict
    else
      begin
      let pid2 = (B.index opt_npeer.pp 0ul).p_id in

      begin
      (**) let dc = idc_get_dc idc in
      (**) let dvp_v0 = device_p_v h1 dvp in
      (**) let dvp_v1 = device_p_v h3 dvp in
      (**) let pinfo_v = idc_get_info_v h1 pinfo in
      (**) let rs_v = lbuffer_or_unit_to_opt_lseq h1 rs in
      (**) assert(Some? rs_v);
      (**) let st_v = handshake_state_t_v_with_smi h1 st1 smi1 in
      (**) let hs_st_v = IS_Handshake?.st st_v.st_hs_state in
      (**) let psk_v = hs_st_v.preshared in
      (**) assert(None? psk_v);
      (**) let r_v = add_peer #dc dvp_v0 pinfo_v rs_v psk_v in
      (**) assert(Some? r_v);
      (**) assert(dvp_v1 == snd(Some?.v r_v))
      end;

      [@inline_let]
      let dst2 =
        // If we don't insert [convert_type], the type inferencer loops
        if initiator then DS_Initiator (convert_type #(state_t (idc_get_isc idc true) true) #(state_t (idc_get_isc idc true) true) st1) id info spriv spub pid2 pinfo dvp
        else DS_Responder (convert_type #(state_t (idc_get_isc idc false) false) #(state_t (idc_get_isc idc false) false) st1) id info spriv spub pid2 pinfo dvp
      in

      (**) assert(dstate_t_invariant h3 dst2);

      Res dst2
      end
    end
  else
    begin
    Fail CRs_not_certified
    end
#pop-options

/// To factorize the proofs, we fix the [initiator] value.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_handshake_read_aux_no_split :
     #idc : valid_idc
  -> initiator : bool
  -> impl : state_t_handshake_read_rec_impl initiator idc
  -> add_peer : device_p_add_peer_get_st idc
  -> payload_outlen : size_t
  -> payload_out:lbuffer uint8 payload_outlen
  -> st : dstate_t idc{
       dstate_t_is_initiator st = initiator /\
       dstate_t_is_handshake st /\
       begin
       let step = UInt32.v (dstate_t_handshake_get_step st) in
       step < List.Tot.length (idc_get_pattern idc).messages /\
       initiator = ((step%2)=1)
       end}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> pid_ptr : B.pointer (idc_get_pid idc).id_t ->
  ST (ds_result_code (dstate_t idc))
  (requires (fun h0 ->
    mk_dstate_t_handshake_read_aux_no_split_st_gen_pre
      initiator payload_outlen payload_out st inlen input pid_ptr h0 /\
    // This condition is missing from the above predicate, because
    // we share it with the ...certify_state helper
    dstate_t_invariant h0 st /\
    // We need the following condition for the functional proof: another way
    // to do it would be to add a modifies clause, which states that the peer info
    // is left unchanged, in the post-condition of [mk_state_t_handshake_read_rec]
    B.deref h0 pid_ptr = dstate_t_get_pid st))
  (ensures (fun h0 res h1 ->
    mk_dstate_t_handshake_read_aux_no_split_st_post
      initiator payload_outlen payload_out st inlen input pid_ptr h0 res h1))

#restart-solver
#push-options "--z3rlimit 800 --ifuel 2"
let mk_dstate_t_handshake_read_aux_no_split
  #idc initiator impl add_peer_impl payload_outlen payload_out
  dst inlen input pid_ptr =
  (**) let h0 = ST.get () in
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let init_isc = idc_get_isc idc true in
  [@inline_let] let resp_isc = idc_get_isc idc false in
  [@inline_let] let isc = idc_get_isc idc initiator in
  [@inline_let] let nc = idc_get_nc idc in
  [@inline_let]
  let Mkddstate_t id info spriv spub pid pinfo dvp st = destruct_dstate_t initiator dst in
  [@inline_let] let step = state_t_handshake_get_step st in

  [@inline_let]
  let has_s = check_messagei_has_S idc step in

  // The following lines won't reduce correctly, but will be inlined anyway
  (**) [@inline_let] let msg = List.Tot.index pattern.messages (UInt32.v step) in
  (**) [@inline_let] let smi0 = step_to_smi pattern initiator (UInt32.v step) in
  (**) [@inline_let] let smi1 = step_to_smi pattern initiator (UInt32.v step + 1) in
  
  begin
  (**) let st_v0 = dstate_t_v h0 dst in
  (**) let status = dstate_get_status st_v0 in
  (**) assert(status = Handshake_receive (UInt32.v step))
  end;

  let dv = B.index dvp.dvp 0ul in
  [@inline_let]
  let Mkdevice_t_raw dv_info dv_sk dv_spriv dv_spub prologue scounter peers pcounter cstate = dv in
  (**) let h1 = ST.get () in
  (**) dstate_t_frame_invariant B.loc_none dst h0 h1;
  (**) assert(dstate_t_invariant h1 dst);
  (**) idc_get_cstate_frame_invariant B.loc_none cstate h0 h1;

  [@inline_let]
  let validation_st = apply_policy idc in
  [@inline_let]
  let vpinfo_st = stateful_validation_info idc in
  [@inline_let]
  let vst = dv in // validation state
  [@inline_let]
  let vpinfo = (pid_ptr, pinfo) in // validation peer information: (pid pointer, peer info)
  (**) assert(info_invariant h1 info);
  (**) assert(info_invariant h1 pinfo);
  (**) state_t_footprint_full_inclusion_lem #isc #initiator st;

  let res = impl step validation_st vst vpinfo payload_outlen payload_out st inlen input in
//  let res =
//    mk_state_t_handshake_read_rec init_isc resp_isc step impls validation_st vst vpinfo
//                                  payload_outlen payload_out
//                                  st inlen input
//  in

  (**) let h2 = ST.get () in
  begin
  (**) let l =
  (**)   B.(loc_union (state_t_core_footprint st)
  (**)     (loc_union (validation_st.vst.St.footprint vst)
  (**)     (loc_union (loc_buffer (payload_out <: buffer uint8))
  (**)     (vpinfo_st.St.footprint vpinfo)))) in
  (**) assert(B.modifies l h1 h2);
  (**) assert(info_invariant h2 info);
  (**) assert(info_freeable h2 info);
  (**) assert(info_invariant h2 pinfo);
  (**) assert(info_freeable h2 pinfo);
  (**) assert(device_p_invariant h2 dvp);
  (**) (idc_get_cstate idc).cstate.St.frame_invariant l cstate h1 h2;
  (**) assert((idc_get_cstate idc).cstate.St.invariant h2 cstate);
  (**) assert(lbuffer_or_unit_to_opt_lseq h2 dv_spriv == lbuffer_or_unit_to_opt_lseq h1 dv_spriv);
  (**) assert(lbuffer_or_unit_to_opt_lseq h2 dv_spub == lbuffer_or_unit_to_opt_lseq h1 dv_spub);
  (**) assert(device_p_owns_dstate_t h2 dvp dst);
  // No removal
  (**) assert(device_p_no_removal dvp h0 h1);
  (**) assert(device_p_no_removal dvp h1 h2);
  (**) device_p_no_removal_trans_lem dvp h0 h1 h2
  end;

  (* Check success *)
  match res with
  | Fail e -> Fail e
  | Res st1 ->

  begin
  (**) check_pattern_messagei_lem pattern (UInt32.v step);
  (**) let input_v = as_seq h0 input in
  (**) let dv_v0 = device_t_v h0 dv in
  (**) let dc = idc_get_dc idc in
  (**) let st_v0 = dstate_t_v h0 dst in
  (**) let res_v = SSpec.handshake_read input_v st_v0.Spec.dst_state dv_v0 in
  (**) assert(Res? res_v);
  (**) let opt_vpinfo_v, payload_v, st_v1 = Res?.v res_v in
  (**) assert(st_v1 == handshake_state_t_v_with_smi h2 st1 smi1);
  (**) let vpinfo_v0 = vpinfo_st.St.v () h0 vpinfo in
  (**) let vpinfo_v1 = vpinfo_st.St.v () h2 vpinfo in
  (**) assert(Some? opt_vpinfo_v = has_s);
  (**) assert(Some? opt_vpinfo_v ==> Some?.v opt_vpinfo_v == vpinfo_v1);
  (**) assert(None? opt_vpinfo_v ==> vpinfo_v1 == vpinfo_v0);
  (**) let pid1 = B.deref h2 pid_ptr in
  (**) let opt_pid_v1 = peer_id_opt_v pid1 in
  (**) assert(match st_v0.Spec.dst_pid, opt_vpinfo_v with
  (**)   | Some _, Some _ -> False
  (**)   | _, None -> not has_s /\ vpinfo_v1 == vpinfo_v0
  (**)   | None, Some (Some (pid_v1, pinfo_v1)) ->
  (**)     has_s /\ Some? opt_pid_v1 /\ Some?.v opt_pid_v1 = pid_v1 /\
  (**)     pinfo_v1 == idc_get_info_v h2 pinfo /\
  (**)     Some? opt_pid_v1
  (**)   | None, Some None ->
  (**)     has_s /\ None? opt_pid_v1 /\ None? opt_pid_v1
  (**)   | _ -> False)
  end;

  (**) assert(dstate_t_invariant h2 dst);

  (* Case 1: no S *)
  if not (has_s) then
    begin
    [@inline_let]
    let dst1 =
      // If we don't insert [convert_type], the type inferencer loops
      if initiator then DS_Initiator (convert_type #(state_t (idc_get_isc idc true) true) #(state_t (idc_get_isc idc true) true) st1) id info spriv spub pid pinfo dvp
      else DS_Responder (convert_type #(state_t (idc_get_isc idc false) false) #(state_t (idc_get_isc idc false) false) st1) id info spriv spub pid pinfo dvp
    in
    (**) assert(dstate_t_invariant h2 dst1);
    begin
    (**) let st_v0 = dstate_t_v h0 dst in
    (**) let st_v1 = dstate_t_v h2 dst in
    (**) assert(Some? st_v0.Spec.dst_pid = Some? st_v0.Spec.dst_pinfo);
    (**) assert(Some? st_v1.Spec.dst_pid = Some? st_v1.Spec.dst_pinfo);
    // The following assertion needs the hypothesis that the original value
    // of the peer id in the pointer is equal to the original state peer id
    (**) assert(
    (**)   match st_v0.Spec.dst_pinfo, st_v1.Spec.dst_pinfo with
    (**)   | None, None -> True
    (**)   | Some pinfo0, Some pinfo1 -> pinfo0 == pinfo1)
    end;

    Res dst1
    end
  else
    begin
    (* Case 2: S *)
    let pid1 = B.index pid_ptr 0ul in

    // Small manipulation to remove the if-then-else if it is not necessary
    [@inline_let]
    let always_false = with_onorm((idc_get_policy idc).always_false) in
    // This assertion needs ifuel 2
    (**) assert((idc_get_policy idc).always_false ==> not (pid1 = peer_id_none idc));
    [@inline_let]
    let has_pid = if always_false then true else not (pid1 = peer_id_none idc) in
    (**) assert(has_pid = not (pid1 = peer_id_none idc));

    [@inline_let]
    let dst1 =
    // If we don't insert [convert_type], the type inferencer loops
      if initiator then DS_Initiator (convert_type #(state_t (idc_get_isc idc true) true) #(state_t (idc_get_isc idc true) true) st1) id info spriv spub pid1 pinfo dvp
      else DS_Responder (convert_type #(state_t (idc_get_isc idc false) false) #(state_t (idc_get_isc idc false) false) st1) id info spriv spub pid1 pinfo dvp
    in
    (**) assert(dstate_t_invariant_core h2 dst1);

    (* Case 2.1: found a peer id *)
    if has_pid then
      begin
      begin
      (**) let pid_v1 = peer_id_opt_v pid1 in
      (**) assert(Some? pid_v1)
      end;
      (**) assert(dstate_t_invariant h2 dst1);
      Res dst1
      end
    (* Case 2.2: no peer id *)
    else
      begin
      (**) state_t_handshake_footprint_inclusion_lem st1;
      let res = mk_dstate_t_handshake_read_aux_no_split_certify_static
        initiator add_peer_impl payload_outlen payload_out dv dst1
      in

      (**) let h4 = ST.get () in
      (**) state_t_handshake_footprint_inclusion_lem st; // TODO: maybe useless
      (**) assert(device_p_no_removal dvp h2 h4);
      (**) device_p_no_removal_trans_lem dvp h0 h2 h4;

      begin
      (**) let l = B.(loc_union (info_footprint pinfo) (device_p_region_of dvp)) in
      (**) handshake_state_t_frame_invariant l st smi0 h2 h4
      end;

      res
      end
    end
#pop-options

/// To factorize the proofs, we fix the [initiator] value.
#restart-solver
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_handshake_read_aux :
     #idc : valid_idc
  -> initiator : bool
  -> impl : state_t_handshake_read_rec_impl initiator idc
  -> split_impl : split_st (idc_get_nc idc)
  -> add_peer : device_p_add_peer_get_st idc
  -> r : rid
  -> payload_outlen : size_t
  -> payload_out : lbuffer uint8 payload_outlen
  -> st : dstate_t idc{
       dstate_t_is_initiator st = initiator /\
       dstate_t_is_handshake st /\
       begin
       let step = UInt32.v (dstate_t_handshake_get_step st) in
       step < List.Tot.length (idc_get_pattern idc).messages /\
       initiator = ((step%2)=1)
       end}
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> pid_ptr : B.pointer (idc_get_pid idc).id_t ->

  ST (ds_result_code (dstate_t idc))
  (requires (fun h0 ->
    let dvp = dstate_t_get_device st in
    let cstate = device_p_get_cstate h0 dvp in  
    ST.is_eternal_region r /\
    dstate_t_invariant h0 st /\
    live h0 payload_out /\
    live h0 input /\
    idc_get_cstate_invariant h0 cstate /\
    B.live h0 pid_ptr /\
    B.deref h0 pid_ptr = dstate_t_get_pid st /\
    begin
    let r_loc = region_to_loc r in
    let cstate_loc = idc_get_cstate_footprint cstate in
    let payload_loc = B.loc_buffer (payload_out <: buffer uint8) in
    let input_loc = B.loc_buffer (input <: buffer uint8) in
    let state_loc = dstate_t_footprint_with_device st in
    let pid_loc = B.loc_addr_of_buffer pid_ptr in
    B.all_disjoint [r_loc; cstate_loc; payload_loc; input_loc; state_loc; pid_loc]
    end /\
    get_aead_pre (idc_get_nc idc) /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))

  (ensures (fun h0 res h1 ->
    let dvp = dstate_t_get_device st in
    let cstate = device_p_get_cstate h0 dvp in
    let l =
      B.(loc_union (loc_union (dstate_t_core_footprint st)
                              (loc_buffer (payload_out <: buffer uint8)))
                   (loc_union (device_p_region_of dvp)
                              (B.loc_buffer pid_ptr)))
    in
    B.(modifies l h0 h1) /\
    device_p_no_removal dvp h0 h1 /\
    // Note that if we split, the invariant of st is not satisfied anymore
    // Adding those for security
    live h1 payload_out /\ live h1 input /\ B.live h1 pid_ptr /\
    begin
    let st_v0 = dstate_t_v h0 st in
    let input_v = as_seq h0 input in
    let cst_v0 = idc_get_cstate_v h0 cstate in
    let dv_v0 = device_p_v h0 dvp in
    let res_v = handshake_read cst_v0 dv_v0 input_v st_v0 in
    begin match res with
    | Res st1 ->
      Res? res_v /\
      begin
      let Res (dv_v1, payload'_v, st1'_v) = res_v in
      let st1_v = dstate_t_v h1 st1 in
      dstate_t_v h1 st1 == st1'_v /\
      as_seq h1 payload_out == payload'_v /\
      dstate_t_invariant h1 st1 /\
      dstate_t_handshake_shared_props r h0 h1 st st1 /\
      device_p_v h1 dvp == dv_v1
      end
    | Fail _ ->
      dstate_t_invariant h1 st /\
      device_p_v h1 dvp == device_p_v h0 dvp
    | _ -> False
    end
    end))

#restart-solver
#push-options "--z3rlimit 200"
let mk_dstate_t_handshake_read_aux
  #idc initiator impl split_impl add_peer_impl r payload_outlen payload_out dst inlen input pid_ptr =
  (**) let h0 = ST.get () in
  [@inline_let] let prev_step = dstate_t_handshake_get_step dst in
  let res =
    mk_dstate_t_handshake_read_aux_no_split initiator impl add_peer_impl payload_outlen payload_out
                                            dst inlen input pid_ptr
  in
  (**) let h1 = ST.get () in
  begin
  (**) let dvp = dstate_t_get_device dst in
  (**) assert(device_p_no_removal dvp h0 h1)
  end;
  match res with
  | Fail e ->
    (**) assert(dstate_t_invariant h1 dst);
    Fail e
  | Res dst1 ->    
    begin
    (**) let payload_loc = B.loc_buffer (payload_out <: buffer uint8) in
    (**) let Mkgddstate_t id info initiator spriv spub pid pinfo dv st = gdestruct_dstate_t dst in
    (**) let Mkgddstate_t id1 info1 initiator1 spriv1 spub1 pid1 pinfo1 dv1 st1 = gdestruct_dstate_t dst1 in
    (**) state_t_footprint_full_inclusion_lem st;
    (**) state_t_footprint_full_inclusion_lem st1;
    (**) assert(B.loc_includes (dstate_t_footprint_with_device dst)
    (**)                       (dstate_t_footprint_with_device dst1));
    (**) assert(B.loc_disjoint (dstate_t_core_footprint dst1) payload_loc)
    end;
    // We have to perform this match here, otherwise [mk_dstate_t_try_split] doesn't
    // reduce correctly.
    let dst2 =
      if initiator then // Will statically reduce
        match dst1 with
        | DS_Initiator st id info spriv spub pid pinfo dv ->
          [@inline_let]
          let dst1 = DS_Initiator st id info spriv spub pid pinfo dv in
          mk_dstate_t_try_split split_impl r initiator prev_step dst1
      else
        match dst1 with // Will statically reduce
        | DS_Responder st id info spriv spub pid pinfo dv ->
          [@inline_let]
          let dst1 = DS_Responder st id info spriv spub pid pinfo dv in
          mk_dstate_t_try_split split_impl r initiator prev_step dst1
    in
    (**) let h2 = ST.get () in
    (**) assert(B.modifies (dstate_t_core_footprint dst1) h1 h2);
    // The following liveness assertion doesn't succeed if we don't add the
    // assertion in the postcondition of [mk_dstate_t_handshake_read_aux_no_split]
    (**) assert(B.live h1 (payload_out <: buffer uint8));
    (**) assert(B.live h2 (payload_out <: buffer uint8));
    (**) assert(as_seq h2 payload_out == as_seq h1 payload_out);
    (**) assert(dstate_t_invariant h2 dst2);
    begin
    (**) let dvp = dstate_t_get_device dst in
    (**) assert(device_p_no_removal dvp h1 h2);
    (**) device_p_no_removal_trans_lem dvp h0 h1 h2
    end;
    Res dst2
#pop-options

/// To factorize the proofs, we fix the [initiator] value.
#restart-solver
[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_t_handshake_read_st (idc : valid_idc) =
     r : rid
  -> payload_outlen : size_t
  -> payload_out : lbuffer uint8 payload_outlen
  -> st : dstate_t idc
  -> inlen : size_t
  -> input : lbuffer uint8 inlen
  -> pid_ptr : B.pointer (idc_get_pid idc).id_t ->

  ST (ds_result_code (dstate_t idc))
  (requires (fun h0 ->
    let dvp = dstate_t_get_device st in
    let cstate = device_p_get_cstate h0 dvp in  
    ST.is_eternal_region r /\
    dstate_t_invariant h0 st /\
    live h0 payload_out /\
    live h0 input /\
    idc_get_cstate_invariant h0 cstate /\
    B.live h0 pid_ptr /\
    B.deref h0 pid_ptr = dstate_t_get_pid st /\
    begin
    let r_loc = if dstate_t_is_handshake st then region_to_loc r else B.loc_none in
    let cstate_loc = idc_get_cstate_footprint cstate in
    let payload_loc = B.loc_buffer (payload_out <: buffer uint8) in
    let input_loc = B.loc_buffer (input <: buffer uint8) in
    let state_loc = dstate_t_footprint_with_device st in
    let pid_loc = if dstate_t_is_handshake st then B.loc_addr_of_buffer pid_ptr else B.loc_none in
    B.all_disjoint [r_loc; cstate_loc; payload_loc; input_loc; state_loc; pid_loc]
    end /\
    get_aead_pre (idc_get_nc idc) /\
    get_dh_pre (idc_get_nc idc) /\
    get_hash_pre (idc_get_nc idc)))

  (ensures (fun h0 res h1 ->
    let dvp = dstate_t_get_device st in
    let cstate = device_p_get_cstate h0 dvp in
    let l =
      B.(loc_union (loc_union (dstate_t_core_footprint st)
                              (loc_buffer (payload_out <: buffer uint8)))
                   (loc_union (device_p_region_of dvp)
                              (B.loc_buffer pid_ptr)))
    in
    B.(modifies l h0 h1) /\
    device_p_no_removal dvp h0 h1 /\
    // Adding those for security
    live h1 payload_out /\ live h1 input /\ B.live h1 pid_ptr /\
    begin
    let dvp = dstate_t_get_device st in
    let st_v0 = dstate_t_v h0 st in
    let input_v = as_seq h0 input in
    let cst_v0 = idc_get_cstate_v h0 cstate in
    let dv_v0 = device_p_v h0 dvp in
    let res_v = handshake_read cst_v0 dv_v0 input_v st_v0 in
    match res with
    | Res st1 ->
      Res? res_v /\
      begin
      let Res (dv_v1, payload'_v, st1'_v) = res_v in
      let st1_v = dstate_t_v h1 st1 in
      dstate_t_v h1 st1 == st1'_v /\
      as_seq h1 payload_out == payload'_v /\
      dstate_t_invariant h1 st1 /\
      dstate_t_handshake_shared_props r h0 h1 st st1 /\
      device_p_v h1 dvp == dv_v1
      end
    | Fail _ ->
      dstate_t_invariant h1 st /\
      device_p_v h1 dvp == device_p_v h0 dvp
    | _ -> False
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_handshake_read :
     #idc : valid_idc
  -> impl_init : state_t_handshake_read_rec_impl true idc
  -> impl_resp : state_t_handshake_read_rec_impl false idc
  -> split_impl : split_st (idc_get_nc idc)
  -> add_peer : device_p_add_peer_get_st idc ->
  dstate_t_handshake_read_st idc

#restart-solver
#push-options "--z3rlimit 100"
let mk_dstate_t_handshake_read
  #idc impl_init impl_resp split_impl add_peer_impl r payload_outlen payload_out dst inlen input pid_ptr =
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let num_messages = with_onorm(List.Tot.length pattern.messages) in
  (**) let h0 = ST.get () in
  begin
  // This is a bit ugly: gives us no_removal in case we perform no stateful operations later
  (**) let dvp = dstate_t_get_device dst in
  (**) device_p_frame_invariant B.loc_none dvp h0 h0
  end;
  // Match on the state and reconstruct it. This may seem to be a no-op, but it
  // allows to statically know whether the state is initiator or responder in
  // the subsequent function calls, which is necessary to successfully extract the code.
  match dst with
  | DS_Initiator dst_st dst_id dst_info dst_spriv dst_spub dst_pid dst_pinfo dst_dv ->
    // We need to statically check that it is possible to send a message.
    // Otherwise, the code may not type check in ML (it would actually be unreachable)
    if with_onorm (can_receive true pattern) then
      [@inline_let] let initiator = true in
      // We perform a match (that we reconstruct in the case of IMS_Handshake)
      // because it leads to better code at extraction time
      begin match dst_st with
      | IMS_Handshake st_step st_cipher st_ck st_h st_spriv st_spub st_epriv st_epub st_rs st_re st_psk ->
        [@inline_let]
        let dst_st =
          IMS_Handshake st_step st_cipher st_ck st_h
                        st_spriv st_spub st_epriv st_epub st_rs st_re st_psk in
        [@inline_let]
        let dst = DS_Initiator dst_st dst_id dst_info dst_spriv dst_spub dst_pid dst_pinfo dst_dv in
        [@inline_let]
        let step = state_t_handshake_get_step dst_st in
        if FStar.UInt32.(step >=^ size num_messages)
        then Fail CIncorrect_transition
        else if not (initiator = (FStar.UInt32.rem step (size 2) = size 1))
        then Fail CIncorrect_transition
        else mk_dstate_t_handshake_read_aux
             #idc initiator impl_init split_impl add_peer_impl r payload_outlen payload_out dst inlen input pid_ptr
      | IMS_Transport _ _ _ _ _ _ ->
        Fail CIncorrect_transition
      end
    else
      Fail CIncorrect_transition
  | DS_Responder dst_st dst_id dst_info dst_spriv dst_spub dst_pid dst_pinfo dst_dv ->
    [@inline_let] let initiator = false in
    begin match dst_st with
    | IMS_Handshake st_step st_cipher st_ck st_h st_spriv st_spub st_epriv st_epub st_rs st_re st_psk ->
      [@inline_let]
      let dst_st =
        IMS_Handshake st_step st_cipher st_ck st_h
                      st_spriv st_spub st_epriv st_epub st_rs st_re st_psk in
      [@inline_let]
      let dst = DS_Responder dst_st dst_id dst_info dst_spriv dst_spub dst_pid dst_pinfo dst_dv in
      [@inline_let]
      let step = state_t_handshake_get_step dst_st in
      if FStar.UInt32.(step >=^ size num_messages)
      then Fail CIncorrect_transition
      else if not (initiator = (FStar.UInt32.rem step (size 2) = size 1))
      then Fail CIncorrect_transition
      else mk_dstate_t_handshake_read_aux
           #idc initiator impl_resp split_impl add_peer_impl r payload_outlen payload_out dst inlen input pid_ptr
    | IMS_Transport _ _ _ _ _ _ ->
      Fail CIncorrect_transition
    end
#pop-options

#restart-solver
#push-options "--z3rlimit 400 --ifuel 1"
let mk_dstate_p_handshake_read
  #idc impl_init impl_resp split_impl add_peer_impl payload_outlen payload_out dst_p inlen input =
  (**) let h0 = ST.get () in
  let dst = B.index dst_p.stp 0ul in
  (**) let r_split = dst_p.stp_r_split in // the region in which to allocate for the split
  (**) let r_pid = dst_p.stp_r_pid in // the region in which to allocate for the pid pointer
  let pid = dstate_t_get_pid dst in
  let pid_ptr = B.malloc r_pid pid 1ul in
  (**) let h1 = ST.get () in
  (**) assert(B.(modifies loc_none h0 h1));
  begin
  (**) let Mkgddstate_t initiator id info spriv spub pid pinfo dvp st = gdestruct_dstate_t dst in
  (**) let dv = B.deref h0 dvp.dvp in
  (**) let Mkdevice_t_raw dv_info dv_sk dv_spriv dv_spub prologue scounter peers pcounter cstate = dv in
  (**) dstate_p_frame_invariant B.loc_none dst_p h0 h1;
  (**) idc_get_cstate_frame_invariant B.loc_none cstate h0 h1;
  (**) assert(region_includes_region dst_p.stp_r r_split);
  (**) assert(region_includes_region dst_p.stp_r r_pid);
  (**) assert(region_includes r_pid (B.loc_addr_of_buffer pid_ptr));
  (**) let st = dstate_t_get_state dst in
  (**) state_t_footprint_full_inclusion_lem st
  end;

  let res =
    mk_dstate_t_handshake_read
      #idc impl_init impl_resp split_impl add_peer_impl r_split payload_outlen payload_out dst inlen input pid_ptr
  in

  (**) let h2 = ST.get () in
  B.free pid_ptr;
  (**) let h3 = ST.get () in
  begin
  (**) let Mkgddstate_t initiator id info spriv spub pid pinfo dvp st = gdestruct_dstate_t dst in
  (**) let dv = B.deref h0 dvp.dvp in
  (**) let Mkdevice_t_raw dv_info dv_sk dv_spriv dv_spub scounter prologue peers pcounter cstate = dv in
  (**) let l =
       B.(loc_union (loc_union (dstate_t_core_footprint dst)
                               (loc_buffer (payload_out <: buffer uint8)))
                    (loc_union (device_p_region_of dvp)
                               (idc_get_cstate_footprint cstate)))
       in
  (**) let ptr_l = B.loc_addr_of_buffer pid_ptr in
  (**) assert(B.modifies (B.loc_union l ptr_l) h0 h3);
  (**) B.(modifies_only_not_unused_in l h0 h3);
  (**) let l' =
      B.(loc_union (loc_union (dstate_p_core_footprint h0 dst_p)
                              (loc_buffer (payload_out <: buffer uint8)))
                    (loc_union (device_p_region_of dvp)
                              (idc_get_cstate_footprint cstate))) in
  (**) assert(B.modifies l h0 h3);
  (**) assert(B.loc_includes l' l);
  (**) assert(B.modifies l' h0 h3);
  (**) assert(device_p_no_removal dvp h0 h1);
  (**) assert(device_p_no_removal dvp h1 h2);
  (**) assert(device_p_no_removal dvp h2 h3);
  (**) device_p_no_removal_trans_lem dvp h0 h1 h2;
  (**) device_p_no_removal_trans_lem dvp h0 h2 h3
  end;
  
  match res with
  | Fail e ->
    (* Update the state status so that it becomes unusable *)
    mk_dstate_p_set_stuck dst_p;
    (**) let h4 = ST.get () in
    (**) assert(dstate_p_invariant h3 dst_p);
    (**) begin
    (**) let dvp = dstate_p_g_get_device h0 dst_p in
    (**) assert(device_p_no_removal dvp h3 h4);
    (**) device_p_no_removal_trans_lem dvp h0 h3 h4
    (**) end;
    e
  | Res dst1 ->
    begin
    (**) let l = B.loc_addr_of_buffer pid_ptr in
    (**) let dvp = dstate_t_get_device dst1 in
    (**) let st1 = dstate_t_get_state dst1 in
    (**) state_t_footprint_full_inclusion_lem st1;
    (**) assert(B.loc_disjoint l (dstate_t_footprint_with_device dst1));
    (**) dstate_t_frame_invariant l dst1 h2 h3;
    (**) device_p_frame_invariant l dvp h2 h3
    end;

    B.upd dst_p.stp 0ul dst1;
    (**) let h4 = ST.get () in
    begin
    (**) let dvp = dstate_t_get_device dst1 in
    (**) let st = dstate_t_get_state dst1 in
    (**) state_t_footprint_full_inclusion_lem st;
    (**) let l = B.loc_buffer dst_p.stp in
    (**) let dv = dstate_t_get_device dst1 in
    (**) dstate_t_frame_invariant l dst1 h3 h4;
    (**) device_p_frame_invariant l dvp h3 h4;
    (**) assert(dstate_t_invariant h4 dst1);
    (**) assert(device_p_no_removal dvp h3 h4);
    (**) device_p_no_removal_trans_lem dvp h0 h3 h4
    end;
    (**) assert(dstate_p_invariant h4 dst_p);
    CSuccess
#pop-options

(**** Transport send message *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_t_transport_write_st (idc : valid_idc) =
     plen : size_t
  -> p : lbuffer uint8 plen
  -> clen : size_t
  -> c : lbuffer uint8 clen
  -> st:dstate_t idc ->
  Stack (ds_result_code (st:dstate_t idc{not (dstate_t_is_handshake st)}))
  (requires (fun h0 ->
    dstate_t_invariant h0 st /\

    live h0 p /\ live h0 c /\
  
    B.loc_disjoint (dstate_t_footprint_with_device st) (B.loc_buffer (p <: buffer uint8)) /\
    B.loc_disjoint (dstate_t_footprint_with_device st) (B.loc_buffer (c <: buffer uint8)) /\
    B.loc_disjoint (B.loc_buffer (p <: buffer uint8))
                   (B.loc_buffer (c <: buffer uint8)) /\
    get_aead_pre (idc_get_nc idc)))
  (ensures (fun h0 res h1 ->
    B.(modifies (B.loc_buffer (c <: buffer uint8)) h0 h1) /\
    begin
    let st0_v = dstate_t_v h0 st in
    let p_v = as_seq h0 p in
    let res_v = Spec.transport_write st0_v p_v in 
    match res with
    | Res st' ->
      Res? res_v /\
      begin
      let Res (c_v, st1_v) = res_v in
      dstate_t_v h1 st' == st1_v /\
      as_seq h1 c == c_v /\
      dstate_t_get_device st' == dstate_t_get_device st /\
      dstate_t_invariant h1 st' /\
      dstate_t_footprint st' == dstate_t_footprint st
      end
    | Fail _ ->
      // Note that the modifies clause gives us that the state remains unchanged
      ((idc_get_send idc (dstate_t_is_initiator st) /\
        size_v clen = size_v plen + aead_tag_size) ==> Fail? res_v)
    | _ -> False
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_transport_write :
     #idc:valid_idc
  -> encrypt : iaead_encrypt_type (idc_get_nc idc) ->
  dstate_t_transport_write_st idc

#push-options "--z3rlimit 100"
let mk_dstate_t_transport_write #idc encrypt plen p clen c dst =
  (**) let h0 = ST.get () in
  match dst with
  | DS_Initiator state id info spriv spub pid pinfo dv ->
    [@inline_let] let initiator = true in
    if not (idc_get_send idc initiator) then Fail CIncorrect_transition
    else if state_t_is_transport state then
      begin
      match mk_state_t_transport_write encrypt plen p clen c state with
      | Fail e -> Fail e
      | Res state' ->
        (**) let h1 = ST.get () in
        (**) assert(state_t_invariant_stateful h1 state');
        [@inline_let] let dst' = DS_Initiator state' id info spriv spub pid pinfo dv in

        begin
        (**) let l = B.loc_buffer (c <: buffer uint8) in
        (**) dstate_t_frame_invariant l dst h0 h1
        end;

        (**) state_t_transport_footprint_inclusion_lem state;
        (**) state_t_transport_footprint_inclusion_lem state';
        (**) assert(state_t_core_footprint state' == state_t_core_footprint state);
        Res dst'
      end
    else
      Fail CIncorrect_transition
  // There should be a way to factorize this
  | DS_Responder state id info spriv spub pid pinfo dv ->
    [@inline_let] let initiator = false in
    if not (idc_get_send idc initiator) then Fail CIncorrect_transition
    else if state_t_is_transport state then
      begin
      match mk_state_t_transport_write encrypt plen p clen c state with
      | Fail e -> Fail e
      | Res state' ->
        (**) let h1 = ST.get () in
        (**) assert(state_t_invariant_stateful h1 state');
        [@inline_let] let dst' = DS_Responder state' id info spriv spub pid pinfo dv in

        begin
        (**) let l = B.loc_buffer (c <: buffer uint8) in
        (**) dstate_t_frame_invariant l dst h0 h1
        end;

        (**) state_t_transport_footprint_inclusion_lem state;
        (**) state_t_transport_footprint_inclusion_lem state';
        (**) assert(state_t_core_footprint state' == state_t_core_footprint state);
        Res dst'
      end
    else
      Fail CIncorrect_transition
#pop-options

#push-options "--z3rlimit 100"
let mk_dstate_p_transport_write #idc encrypt plen p clen c dst_p =
  (**) let h0 = ST.get () in
  let dst = B.index dst_p.stp 0ul in
  (**) let h1 = ST.get () in
  (**) dstate_t_frame_invariant B.loc_none dst h0 h1;
  let r = mk_dstate_t_transport_write encrypt plen p clen c dst in
  (**) let h2 = ST.get () in
  begin
  (**) let l = B.loc_buffer (c <: buffer uint8) in
  (**) dstate_t_frame_invariant l dst h1 h2
  end;
  match r with
  | Fail e -> e
  | Res dst' ->
    B.upd dst_p.stp 0ul dst';
    (**) let h3 = ST.get () in
    (**) dstate_t_frame_invariant (B.loc_addr_of_buffer dst_p.stp) dst' h2 h3;
    CSuccess
#pop-options

(**** Transport receive message *)

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
type dstate_t_transport_read_st (idc : valid_idc) =
     plen : size_t
  -> p : lbuffer uint8 plen
  -> clen : size_t
  -> c : lbuffer uint8 clen
  -> st:dstate_t idc ->
  Stack (ds_result_code (st:dstate_t idc{not (dstate_t_is_handshake st)}))
  (requires (fun h0 ->
    dstate_t_invariant h0 st /\

    live h0 p /\ live h0 c /\
  
    B.loc_disjoint (dstate_t_footprint_with_device st) (B.loc_buffer (p <: buffer uint8)) /\
    B.loc_disjoint (dstate_t_footprint_with_device st) (B.loc_buffer (c <: buffer uint8)) /\
    B.loc_disjoint (B.loc_buffer (p <: buffer uint8))
                   (B.loc_buffer (c <: buffer uint8)) /\
    get_aead_pre (idc_get_nc idc)))
  (ensures (fun h0 res h1 ->
    B.(modifies (B.loc_buffer (p <: buffer uint8)) h0 h1) /\
    begin
    let st0_v = dstate_t_v h0 st in
    let c_v = as_seq h0 c in
    let res_v = Spec.transport_read st0_v c_v in
    match res with
    | Res st' ->
      Res? res_v /\
      begin
      let Res (p_v, st1_v) = res_v in
      dstate_t_v h1 st' == st1_v /\
      as_seq h1 p == p_v /\
      dstate_t_get_device st' == dstate_t_get_device st /\
      dstate_t_invariant h1 st' /\
      dstate_t_footprint st' == dstate_t_footprint st
      end
    | Fail _ ->
      // Note that the modifies clause gives us that the state remains unchanged
      ((idc_get_receive idc (dstate_t_is_initiator st) /\
        size_v clen = size_v plen + aead_tag_size) ==> Fail? res_v)
    | _ -> False
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_dstate_t_transport_read :
     #idc:valid_idc
  -> decrypt : iaead_decrypt_type (idc_get_nc idc) ->
  dstate_t_transport_read_st idc

#push-options "--z3rlimit 100"
let mk_dstate_t_transport_read #idc decrypt plen p clen c dst =
  (**) let h0 = ST.get () in
  match dst with
  | DS_Initiator state id info spriv spub pid pinfo dv ->
    [@inline_let] let initiator = true in
    if not (idc_get_receive idc initiator) then Fail CIncorrect_transition
    else if state_t_is_transport state then
      begin
      match mk_state_t_transport_read decrypt plen p clen c state with
      | Fail e -> Fail e
      | Res state' ->
        (**) let h1 = ST.get () in
        (**) assert(state_t_invariant_stateful h1 state');
        [@inline_let] let dst' = DS_Initiator state' id info spriv spub pid pinfo dv in

        begin
        (**) let l = B.loc_buffer (p <: buffer uint8) in
        (**) dstate_t_frame_invariant l dst h0 h1
        end;

        (**) state_t_transport_footprint_inclusion_lem state;
        (**) state_t_transport_footprint_inclusion_lem state';
        (**) assert(state_t_core_footprint state' == state_t_core_footprint state);
        Res dst'
      end
    else
      Fail CIncorrect_transition
  // There should be a way to factorize this
  | DS_Responder state id info spriv spub pid pinfo dv ->
    [@inline_let] let initiator = false in
    if not (idc_get_receive idc initiator) then Fail CIncorrect_transition
    else if state_t_is_transport state then
      begin
      match mk_state_t_transport_read decrypt plen p clen c state with
      | Fail e -> Fail e
      | Res state' ->
        (**) let h1 = ST.get () in
        (**) assert(state_t_invariant_stateful h1 state');
        [@inline_let] let dst' = DS_Responder state' id info spriv spub pid pinfo dv in

        begin
        (**) let l = B.loc_buffer (p <: buffer uint8) in
        (**) dstate_t_frame_invariant l dst h0 h1
        end;

        (**) state_t_transport_footprint_inclusion_lem state;
        (**) state_t_transport_footprint_inclusion_lem state';
        (**) assert(state_t_core_footprint state' == state_t_core_footprint state);
        Res dst'
      end
    else
      Fail CIncorrect_transition
#pop-options

#push-options "--z3rlimit 100"
let mk_dstate_p_transport_read #idc decrypt plen p clen c dst_p =
  (**) let h0 = ST.get () in
  let dst = B.index dst_p.stp 0ul in
  (**) let h1 = ST.get () in
  (**) dstate_t_frame_invariant (B.loc_addr_of_buffer dst_p.stp) dst h0 h1;
  let r = mk_dstate_t_transport_read decrypt plen p clen c dst in
  (**) let h2 = ST.get () in
  begin
  (**) let l = B.loc_buffer (p <: buffer uint8) in
  (**) dstate_t_frame_invariant l dst h1 h2
  end;
  match r with
  | Fail e -> e
  | Res dst' ->
    B.upd dst_p.stp 0ul dst';
    (**) let h3 = ST.get () in
    (**) dstate_t_frame_invariant (B.loc_addr_of_buffer dst_p.stp) dst' h2 h3;
    CSuccess
#pop-options
