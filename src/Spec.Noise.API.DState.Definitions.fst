module Spec.Noise.API.DState.Definitions

open Lib.ByteSequence
open FStar.Mul
open FStar.List.Tot

friend Spec.Noise.Base.Definitions
module Base = Spec.Noise.Base.Definitions
module State = Spec.Noise.API.State.Definitions
friend Spec.Noise.API.State.Definitions
friend Spec.Noise.API.Device.Definitions
module M = Spec.Noise.Map
open Spec.Noise.API.MetaInfo

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** API *)

let s_error_to_ds_error (e : State.s_error) : ds_error =
  match e with
  | State.Incorrect_transition -> Incorrect_transition
  | State.Premessage -> Premessage
  | State.No_key -> No_key
  | State.Already_key -> Already_key
  | State.Rs_not_valid -> Rs_rejected_by_policy
  | State.Input_size -> Input_size
  | State.DH_error -> DH_error
  | State.Decryption -> Decryption
  | State.Saturated_nonce -> Saturated_nonce

(*** Configuration *)

val apply_policy (dc : dconfig) :
  State.validation_function dc.dc_nc (device dc)
                            (option (peer_id & dc.dc_info))

let apply_policy dc dv rs =
  (* Lookup the associated peer *)
  match lookup_peer_by_static dv rs with
  | Some p ->
    (* There is a peer: nothing to validate *)
    Some (Some (p.p_id, p.p_info), p.p_psk)
  | None ->
    (* No peer: apply the policy *)
    if dc.dc_policy rs then
      (* Success *)
      Some (None, None)
    else
      (* Failure *)
      None

let dconfig_to_sconfig dc =
  {
    State.sc_config = dc.dc_nc;
    State.sc_vstate = device dc;
    State.sc_pinfo = option (peer_id & dc.dc_info);
    State.sc_validate = apply_policy dc;
  }

(*** DState *)

/// The dstate definition
// TODO: the implementation keeps the static keys even when in transport phase
noeq type dstate (dc : dconfig) = {
  dst_state : s:State.state (dconfig_to_sconfig dc){check_swf (State.state_get_pattern s)};
  dst_id : state_id;
  dst_info : dc.dc_info;
  dst_pid : option peer_id;
  dst_pinfo : option dc.dc_info;
}

let dstate_get_pattern #dc dst =
  State.state_get_pattern dst.dst_state

let dstate_get_status #dc dst =
  State.state_get_status dst.dst_state

let dstate_is_initiator #dc dst =
  State.state_is_initiator dst.dst_state

let dstate_is_handshake #dc dst =
  State.state_is_handshake dst.dst_state

let dstate_is_stuck #dc dst =
  let n = List.Tot.length (dstate_get_pattern #dc dst).messages in
  let status = dstate_get_status dst in
  let is_handshake_state = not (State.Transport? status) in
  if is_handshake_state then
    let step = match status with | State.Handshake_send i | State.Handshake_receive i -> i in
    step >= n + 1
  else false

let dstate_get_id #dc dst = dst.dst_id
let dstate_get_info #dc dst = dst.dst_info
let dstate_get_peer_id #dc dst = dst.dst_pid
let dstate_get_peer_info #dc dst = dst.dst_pinfo

let dstate_get_static #dc dst = State.state_get_s dst.dst_state
let dstate_get_remote_static #dc dst = State.state_get_rs dst.dst_state
let dstate_get_hash #dc dst = State.state_get_hash dst.dst_state

let dstate_received_transport_message #dc dst =
  State.state_received_transport_message dst.dst_state

(* Create a state. The returned state is initialized so that the premessages are
 * already processed.
 * Note that when creating a responder state, we need to provide the peer
 * identifier at the very beginning if we need to hash a remote static
 * key when processing the premessages. In the other situations, we should NOT
 * provide a peer (because otherwise we will fail when receiving the remote static
 * key during the handshake *)

(* When taking as input an optional peer id, we lookup the peer and abort
 * if a peer id was provided but we couldn't find any related peer *)
let lookup_opt_peer (#dc : dconfig) (dv : device dc) (opt_pid : option peer_id) :
  ds_result (option (peer dc)) =
  match opt_pid with
  | None -> Res None
  | Some pid ->
    match lookup_peer_by_id dv pid with
    | None -> Fail Unknown_peer_id
    | Some p -> Res (Some p)

let get_receive_pre (hsk : handshake_pattern) (initiator : bool) :
  option (list (premessage_token)) =
  if initiator then hsk.premessage_ri else hsk.premessage_ir

let pre_receives_rs (hsk : handshake_pattern) (initiator : bool) : bool =
  let pre = get_receive_pre hsk initiator in
  match pre with
  | None -> false
  | Some pre -> mem PS pre

let create_dstate #dc dv initiator e opt_pid =
  let pattern = dv.dv_pattern in
  (* Retrieve peer information *)
  let opt_peer = lookup_opt_peer dv opt_pid in
  match opt_peer with
  | Fail e -> Fail e
  | Res opt_peer ->
    let opt_pinfo, rs, psk =
      (match opt_peer with
      | None -> None, None, None
      | Some p ->
        // Use the remote static only if we need it
        let rs = if pre_receives_rs pattern initiator then p.p_s else None in
        Some p.p_info, rs, p.p_psk
      <: option dc.dc_info
                & option (public_key dc.dc_nc)
                & option preshared_key)
    in
    (* Initialize *)
    let sc = dconfig_to_sconfig dc in
    let ks = key_slots_from_pattern initiator pattern in
    let s = if ks.ks_s then dv.dv_static_identity else None in
    match State.create_state #sc pattern dv.dv_prologue initiator s e rs psk with
    | Fail e -> Fail (s_error_to_ds_error e)
    | Res st ->
      let st_id = dv.dv_states_counter in
      let dst =
      {
        dst_state = st;
        dst_id = st_id;
        dst_info = dv.dv_info;
        dst_pid = opt_pid;
        dst_pinfo = opt_pinfo;
      }
      in
      let dv = { dv with dv_states_counter = st_id+1; } in
      Res (dst, dv)

val try_split : #dc:dconfig -> st:dstate dc -> dstate dc
let try_split #dc st =
  match st.dst_state.State.st_hs_state with
  | State.IS_Transport _ _ _ _ -> st
  | State.IS_Handshake status hs_st ->
    match status with
    | State.Transport -> st (* inconsistent but ruled out elsewhere *)
    | State.Handshake_send i | State.Handshake_receive i ->
      let pat = st.dst_state.State.st_pattern.messages in
      if i = List.Tot.length pat then
        let st' = State.split st.dst_state in
        (**) assert(Res? st');
        { st with dst_state = Res?.v st'}
      else st

let handshake_write #dc payload st =
  match begin
  match State.handshake_write payload st.dst_state with
  | Fail e -> Fail (s_error_to_ds_error e)
  | Res (cipher, st') ->
    Res (cipher, {st with dst_state = st'})
  end with
  (* Try to split *)
  | Fail e -> Fail e
  | Res (cipher, st') -> Res (cipher, try_split st')

let handshake_read #dc cst dv msg st =
  match begin
  match State.handshake_read msg st.dst_state dv with
  | Fail e -> Fail (s_error_to_ds_error e)
  | Res (peer, payload, st') ->
    (* Is there already a peer? If yes: abort *)
    match st.dst_pid, peer with
    | Some _, Some _ ->
      (* We received an S token, but we already have a peer: abort *)
      Fail Already_peer
    | _, None ->
      (* We did not receive an S token: just update the state *)
      Res (dv, payload, {st with dst_state = st' })
    | None, Some (Some (pid, pinfo)) ->
      (* We received an already known remote static key: store the peer *)
      Res (dv, payload, {st with dst_state = st'; dst_pid = Some pid; dst_pinfo = Some pinfo })
    | None, Some None ->
      (* We received un unknown remote static: certify it and add it to the device *)
      let hs_st = State.IS_Handshake?.st st'.State.st_hs_state in
      let rs = hs_st.remote_static in
      match rs with
      | None -> Fail No_key (* can't happen *)
      | Some rs ->
        match dc.dc_certification cst rs payload with
        | None -> Fail Rs_not_certified
        | Some pinfo ->
          (* We received a valid static key for a new peer: add it to the device *)
          match add_peer_get dv pinfo (Some rs) hs_st.preshared with
          | None -> Fail Peer_conflict
          | Some (p, dv') ->
            Res (dv', payload, {st with dst_state = st'; dst_pid = Some p.p_id; dst_pinfo = Some pinfo })
  end with
  (* Try to split *)
  | Fail e -> Fail e
  | Res (dv', plain, st') ->
    Res (dv', plain, try_split st')

let transport_write #dc st msg =
  // We must check if the pattern is one-way, in which case only the initiator
  // can send messages.
  if length (dstate_get_pattern st).messages <= 1 && not (dstate_is_initiator st) then
    Fail Incorrect_transition
  else
    match State.transport_write st.dst_state msg with
    | Fail e -> Fail (s_error_to_ds_error e)
    | Res (msg, st') -> Res (msg, {st with dst_state = st'})

let transport_read #dc st cipher =
  // We must check if the pattern is one-way, in which case only the responder
  // can receive messages.
  if length (dstate_get_pattern st).messages <= 1 && dstate_is_initiator st then
    Fail Incorrect_transition
  else
    match State.transport_read st.dst_state cipher with
    | Fail e -> Fail (s_error_to_ds_error e)
    | Res (plain, st') -> Res (plain, {st with dst_state = st'})
