module Spec.Noise.API.DState.Lemmas

open Lib.ByteSequence
open Spec.Noise.API.State.Definitions
module State = Spec.Noise.API.State.Definitions
open Spec.Noise.API.Device.Definitions
friend Spec.Noise.API.Device.Definitions
open Spec.Noise.API.Device.Lemmas
friend Spec.Noise.API.Device.Lemmas
open Spec.Noise.API.DState.Definitions
friend Spec.Noise.API.DState.Definitions
module M = Spec.Noise.Map
open Spec.Noise.SPatterns
open Spec.Noise.CryptoPrimitives
open FStar.List.Tot

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

open Spec.Noise.Base
open Spec.Noise.API.DState.Definitions

/// Some helpers to split handshake_read into smaller functions - it is too
/// big to be implemented in one block without the proofs exploding.

(* We received a message and the current patter *)
val handshake_read_no_split_certify_static :
     #dc:dconfig
  -> cst:dc.dc_cert_state
  -> dv:device dc
  -> st:State.state (dconfig_to_sconfig dc){check_swf (State.state_get_pattern st)}
  -> dst_id:state_id
  -> dst_info:dc.dc_info
  -> payload:hashable dc.dc_nc ->
  Pure (ds_result (device dc & bytes & dstate dc))
  (requires (State.state_is_handshake st))
  (ensures (fun r -> True))

let handshake_read_no_split_certify_static #dc cst dv st dst_id dst_info payload =
  let hs_st = State.IS_Handshake?.st st.State.st_hs_state in
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
        let dst = {
          dst_state = st;
          dst_id = dst_id;
          dst_info = dst_info;
          dst_pid = Some p.p_id;
          dst_pinfo = Some pinfo
        } in
        Res (dv', payload, dst)

val handshake_read_no_split :
     #dc:dconfig
  -> cst:dc.dc_cert_state
  -> dv:device dc
  -> msg:bytes
  -> st:dstate dc ->
  Pure (ds_result (device dc & bytes & dstate dc))
  (requires True)
  (ensures (fun r -> True))

let handshake_read_no_split #dc cst dv msg st =
  match Spec.Noise.API.State.Definitions.handshake_read msg st.dst_state dv with
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
      handshake_read_no_split_certify_static cst dv st' st.dst_id st.dst_info payload

val handshake_read_no_split_lem :
     #dc:dconfig
  -> cst:dc.dc_cert_state
  -> dv:device dc (* we need the device for lookups *)
  -> msg:bytes
  -> st:dstate dc ->
  Lemma (
    Spec.Noise.API.DState.Definitions.handshake_read cst dv msg st ==
    begin match handshake_read_no_split cst dv msg st with
    | Fail e -> Fail e
    | Res (dv', plain, st') ->
      Res (dv', plain, try_split st')
    end)

let handshake_read_no_split_lem #dc cst dv msg st = ()

let apply_policy_on_peers_spec dc vs rs =
  (* Lookup the associated peer *)
  match M.lookup (peer_has_s #dc rs) vs with
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

val apply_policy_on_peers_spec_lem (dc : dconfig)
                                   (dv : device dc) (rs : public_key dc.dc_nc) :
  Lemma(
    let res = apply_policy_on_peers_spec dc dv.dv_peers rs in
    let res' = apply_policy dc dv rs in
    res == res')

let apply_policy_on_peers_spec_lem dc dv rs = ()
