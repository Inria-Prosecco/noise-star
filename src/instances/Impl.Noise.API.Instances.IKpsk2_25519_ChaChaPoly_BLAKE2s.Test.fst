/// This module implements a minimal example using the Noise API. Note that it
/// can't be extracted to C, and is here only to check that the API is usable
/// (ie: that the function preconditions are reasonable and that the API provides
/// enough information to reason about aliasing).

module Impl.Noise.API.Instances.IKpsk2_25519_ChaChaPoly_BLAKE2s.Test

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open LowStar.BufferOps
module B = LowStar.Buffer
module G = FStar.Ghost

open Spec.Noise.API.MetaInfo

open Impl.Noise.Types
open Impl.Noise.API.Device
open Impl.Noise.API.DState
open Impl.Noise.API.Session
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate
module Str = Impl.Noise.String
open Spec.Noise

open Impl.Noise.API.Instances.IKpsk2_25519_ChaChaPoly_BLAKE2s

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(*** Tests *)

let _ : squash(
 key_slots_from_pattern true (idc_get_pattern idc) =
 {
   ks_s = true;
   ks_e = true;
   ks_re = true;
   ks_rs = true;
   ks_psk = true;
   ks_send = true;
   ks_receive = true;
 }) = normalize_term_spec(key_slots_from_pattern true (idc_get_pattern idc))

let _ : squash(
 key_slots_from_pattern false (idc_get_pattern idc) =
 {
   ks_s = true;
   ks_e = true;
   ks_re = true;
   ks_rs = true;
   ks_psk = true;
   ks_send = true;
   ks_receive = true;
 }) = normalize_term_spec(key_slots_from_pattern false (idc_get_pattern idc))

/// In the case of IKpsk2, all the private key types are the same, and all the
/// public key types are the same

[@@ noextract_to "krml"] inline_for_extraction noextract
let private_key_t = sprivate_key_t idc true

[@@ noextract_to "krml"] inline_for_extraction noextract
let public_key_t = spublic_key_t idc true

[@@ noextract_to "krml"] inline_for_extraction noextract
let hashable_size_t = hashable_size_t (idc_get_nc idc)

let _ : squash(knows_remote_at_init idc true = true) =
  normalize_term_spec(knows_remote_at_init idc true)
let _ : squash(knows_remote_at_init idc false = false) =
  normalize_term_spec(knows_remote_at_init idc false)
let _ : squash(List.Tot.length (idc_get_pattern idc).messages = 2) =
  normalize_term_spec(List.Tot.length (idc_get_pattern idc).messages)
module Helpers = FStar.InteractiveHelpers

open Lib.RandomSequence
open Lib.RandomBuffer.System

[@@ noextract_to "krml"] inline_for_extraction noextract
let message0_length : l:nat{l = compute_message_length idc 0} =
  (**) normalize_term_spec (compute_message_length idc 0);
  96

[@@ noextract_to "krml"] inline_for_extraction noextract
let message0_len = size message0_length

[@@ noextract_to "krml"] inline_for_extraction noextract
let message1_length : l:nat{l = compute_message_length idc 1} =
  (**) normalize_term_spec (compute_message_length idc 1);
  48

[@@ noextract_to "krml"] inline_for_extraction noextract
let message1_len = size message1_length

/// First test to check that the lemmas are correctly applied by the SMT.
/// We do a very small example to interact quickly with the solver.
// TODO: relax the disjointness hypotheses
#restart-solver
#push-options "--z3rlimit 300"
[@@ noextract_to "krml"] inline_for_extraction noextract
let test1 (r0 : rid)
          (sk1 : aead_key_t)
          (spriv1 : private_key_t)
          (spub1 : public_key_t)
          (psk : preshared_key_t)
          (prlg_len : hashable_size_t)
          (prlg : lbuffer uint8 prlg_len)
          (encap0 : B.pointer encap_message_p_or_null)
          (outlen_p : B.pointer size_t)
          (temp0 : B.pointer (buffer uint8)) :
  ST bool
  (requires (fun h0 ->
    is_eternal_region r0 /\
    live h0 (sk1 <: buffer uint8) /\
    live h0 (spriv1 <: buffer uint8) /\
    live h0 (spub1 <: buffer uint8) /\
    live h0 (psk <: buffer uint8) /\
    live h0 prlg /\
    live h0 (encap0 <: buffer encap_message_p_or_null) /\
    live h0 (outlen_p <: buffer size_t) /\
    live h0 (temp0 <: buffer (buffer uint8)) /\
    get_dh_pre (idc ()).idc_nc /\
    begin
    let entr_loc = B.loc_addr_of_buffer (entropy_p <: buffer (G.erased entropy)) in
    let r0_loc = region_to_loc r0 in
    let sk1_loc = B.loc_addr_of_buffer (sk1 <: buffer uint8) in
    let spriv1_loc = B.loc_addr_of_buffer (spriv1 <: buffer uint8) in
    let spub1_loc = B.loc_addr_of_buffer (spub1 <: buffer uint8) in
    let psk_loc = B.loc_addr_of_buffer (psk <: buffer uint8) in
    let prlg_loc = B.loc_addr_of_buffer (prlg <: buffer uint8) in
    let encap0_loc = B.loc_addr_of_buffer (encap0 <: buffer encap_message_p_or_null) in
    let outlen_loc = B.loc_addr_of_buffer (outlen_p <: buffer size_t) in
    let temp0_loc = B.loc_addr_of_buffer (temp0 <: buffer (buffer uint8)) in
    B.all_disjoint [
      entr_loc; r0_loc; sk1_loc; spriv1_loc;
      spub1_loc; psk_loc; prlg_loc;
      encap0_loc; outlen_loc;
      temp0_loc]
    end))
  (ensures (fun h0 _ h1 -> True)) =

  (**) let h0 = ST.get () in
  (**) Lib.Buffer.recall entropy_p;
  // Create the regions
  let (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10) = create_regions10 r0 in

  // Create the devices
  let peer_info = Str.lstring_null MUT in
  let dvp1 = device_create r1 () prlg_len prlg peer_info sk1 spriv1 in
  let bdvp1 = device_p_is_null dvp1 in
  if bdvp1 then false
  else
  begin
  (**) let h3 = ST.get () in
  // Add some peers
  // TODO: relax the disjointness hypotheses here
  let peer1 = device_add_peer dvp1 peer_info spub1 psk in
  (**) let h4 = ST.get () in
  (**) let h5 = ST.get () in
  let bp1 = peer_p_is_null peer1 in
  if bp1 then false
  else
    begin
    let pid1 = peer_get_id peer1 in
    // Create the sessions
    (**) let h9 = ST.get () in
    let sn1 = session_create_initiator r3 dvp1 pid1 in
    (**) let h10 = ST.get () in
    let sn2 = session_create_responder r4 dvp1 () in
    (**) let h11 = ST.get () in
    // Test if the sessions are null
    let bs1 = session_p_is_null sn1 in
    let bs2 = session_p_is_null sn2 in
    // Exchange messages
    if bs1 || bs2 then
      begin
      if not bs1 then session_free sn1;
      if not bs2 then session_free sn2;
      device_free dvp1;
      false
      end
    else
      begin
      let payload0 = pack_message r6 0ul (B.null #uint8) in
      (**) let h12 = ST.get () in
      let res =
        match session_write payload0 sn1 r7 outlen_p temp0 with
        | Success ->
          let inlen0 = B.index outlen_p 0ul in
          let msg0 = B.index temp0 0ul in
          begin match session_read r8 encap0 sn2 inlen0 msg0 with
          | Success -> true
          | _ -> false
          end
        | _ -> false
      in
      // Clear
      (**) let h13 = ST.get () in
      if not (encap_message_p_is_null payload0)
      then encap_message_p_free payload0;
      let msg0 = B.index (temp0 <: buffer (buffer uint8)) 0ul in
      if not (B.is_null (msg0 <: buffer uint8)) then B.free msg0;
      session_free sn1;
      session_free sn2;
      device_free dvp1;
      // Return
      res
      end
    end
  end
#pop-options

/// Second test to check that the lemmas are correctly applied by the SMT.
// TODO: relax the disjointness hypotheses
// TODO: this proof works fine in interactive mode, but really causes trouble
// in command line mode
#restart-solver
#push-options "--z3rlimit 5000"
[@@ noextract_to "krml"] inline_for_extraction noextract
let test2 (r0 : rid)
          (sk1 sk2 : aead_key_t)
          (spriv1 spriv2 : private_key_t)
          (spub1 spub2 spub3 spub4 : public_key_t)
          (psk : preshared_key_t)
          (prlg_len : hashable_size_t)
          (prlg : lbuffer uint8 prlg_len)
          (encap0 encap1 : B.pointer encap_message_p_or_null)
          (outlen_p : B.pointer size_t)
          (temp0 temp1 : B.pointer (buffer uint8)) :
  ST bool
  (requires (fun h0 ->
    is_eternal_region r0 /\
    live h0 (sk1 <: buffer uint8) /\
    live h0 (sk2 <: buffer uint8) /\
    live h0 (spriv1 <: buffer uint8) /\
    live h0 (spriv2 <: buffer uint8) /\
    live h0 (spub1 <: buffer uint8) /\
    live h0 (spub2 <: buffer uint8) /\
    live h0 (spub3 <: buffer uint8) /\
    live h0 (spub4 <: buffer uint8) /\
    live h0 (psk <: buffer uint8) /\
    live h0 prlg /\
    live h0 (encap0 <: buffer encap_message_p_or_null) /\
    live h0 (encap1 <: buffer encap_message_p_or_null) /\
    live h0 (outlen_p <: buffer size_t) /\
    live h0 (temp0 <: buffer (buffer uint8)) /\
    live h0 (temp1 <: buffer (buffer uint8)) /\
    live h0 (B.deref h0 temp0) /\
    live h0 (B.deref h0 temp1) /\
    get_dh_pre (idc ()).idc_nc /\
    begin
    let entr_loc = B.loc_addr_of_buffer (entropy_p <: buffer (G.erased entropy)) in
    let r0_loc = region_to_loc r0 in
    let sk1_loc = B.loc_addr_of_buffer (sk1 <: buffer uint8) in
    let sk2_loc = B.loc_addr_of_buffer (sk2 <: buffer uint8) in
    let spriv1_loc = B.loc_addr_of_buffer (spriv1 <: buffer uint8) in
    let spriv2_loc = B.loc_addr_of_buffer (spriv2 <: buffer uint8) in
    let spub1_loc = B.loc_addr_of_buffer (spub1 <: buffer uint8) in
    let spub2_loc = B.loc_addr_of_buffer (spub2 <: buffer uint8) in
    let spub3_loc = B.loc_addr_of_buffer (spub3 <: buffer uint8) in
    let spub4_loc = B.loc_addr_of_buffer (spub4 <: buffer uint8) in
    let psk_loc = B.loc_addr_of_buffer (psk <: buffer uint8) in
    let prlg_loc = B.loc_addr_of_buffer (prlg <: buffer uint8) in
    let encap0_loc = B.loc_addr_of_buffer (encap0 <: buffer encap_message_p_or_null) in
    let encap1_loc = B.loc_addr_of_buffer (encap1 <: buffer encap_message_p_or_null) in
    let outlen_loc = B.loc_addr_of_buffer (outlen_p <: buffer size_t) in
    let temp0_loc = B.loc_addr_of_buffer (temp0 <: buffer (buffer uint8)) in
    let temp1_loc = B.loc_addr_of_buffer (temp1 <: buffer (buffer uint8)) in
    B.all_disjoint [
      entr_loc; r0_loc; sk1_loc; sk2_loc; spriv1_loc; spriv2_loc;
      spub1_loc; spub2_loc; spub3_loc; spub4_loc; psk_loc; prlg_loc;
      encap0_loc; encap1_loc; outlen_loc;
      temp0_loc; temp1_loc]
    end))
  (ensures (fun h0 _ h1 -> True)) =

  (**) let h0 = ST.get () in
  (**) Lib.Buffer.recall entropy_p;
  // Create the regions
  let (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12) = create_regions12 r0 in
  // Create the devices
  let peer_info = Str.lstring_null MUT in
  let dvp1 = device_create r1 () prlg_len prlg peer_info sk1 spriv1 in
  let dvp2 = device_create r2 () prlg_len prlg peer_info sk2 spriv2 in
  let bdvp1 = device_p_is_null dvp1 in
  let bdvp2 = device_p_is_null dvp2 in
  if bdvp1 || bdvp2 then false
  else
  begin
  (**) let h3 = ST.get () in
  // Add some peers
  // TODO: relax the disjointness hypotheses here
  let peer1 = device_add_peer dvp1 peer_info spub2 psk in
  let peer3 = device_add_peer dvp1 peer_info spub3 psk in
  (**) let h4 = ST.get () in
  let peer2 = device_add_peer dvp2 peer_info spub1 psk in
  (**) let h5 = ST.get () in
  // We call peer_p_is_null on peer1 only after the third call to
  // device_add_peer, to check that the patterns are correctly triggered.
  // Note that the invariants are preserved if we add/remove (under conditions)
  // peers to dvp1 - framing those properties was non-trivial.
  let bp1 = peer_p_is_null peer1 in
  let bp2 = peer_p_is_null peer2 in
  if bp1 || bp2 then false
  else
    begin
    let pid1 = peer_get_id peer1 in
    let pid2 = peer_get_id peer2 in
    // Create the sessions
    (**) let h9 = ST.get () in
    let sn1 = session_create_initiator r3 dvp1 pid1 in
    (**) let h10 = ST.get () in
    let sn2 = session_create_responder r4 dvp2 () in
    (**) let h11 = ST.get () in
    // This is only to test the SMT patterns: we add a peer in dvp1
    // (which is thus modified) and create a new session - the
    // predicate linking sn1 to dvp1 should be framed automatically
    let peer4 = device_add_peer dvp1 peer_info spub4 psk in
    (**) let h12 = ST.get () in
    let sn3 = session_create_responder r5 dvp1 () in
    (**) let h13 = ST.get () in
    // Test if the sessions are null
    let bs1 = session_p_is_null sn1 in
    let bs2 = session_p_is_null sn2 in
    let bs3 = session_p_is_null sn3 in
    // Exchange messages
    if bs1 || bs2 || bs3 then
      begin
      if not bs1 then session_free sn1;
      if not bs2 then session_free sn2;
      if not bs3 then session_free sn3;
      device_free dvp1;
      device_free dvp2;
      false
      end
    else
      begin
      let payload0 = pack_message r6 0ul (B.null #uint8) in
      let payload1 = pack_message r9 0ul (B.null #uint8) in
      let res =
        match session_write payload0 sn1 r7 outlen_p temp0 with
        | Success ->
          let inlen0 = B.index outlen_p 0ul in
          let msg0 = B.index temp0 0ul in
          begin match session_read r8 encap0 sn2 inlen0 msg0 with
          | Success ->
            begin match session_write payload1 sn2 r10 outlen_p temp1 with
            | Success ->
              let inlen1 = B.index outlen_p 0ul in
              let msg1 = B.index temp1 0ul in
              //begin match session_read r11 encap1 sn1 inlen1 msg1 with
              //| Success ->
                // The call to [session_free sn3/sn4] allows us to check that
                // the invariants are correctly framed - the ones linking
                // [dvp1] to [sn1] and [dvp2] to [sn2] are mostly preserved
                // by the read/write functions, however the one linking
                // [dvp1] to [sn3] requires a bit of work. We don't put
                // [session_free sn3] with the other calls to free because
                // it would require a lot more work from the SMT solver,
                // leading to an unreasonable rlimit, and if type-checking
                // for the current function, we already know that our patterns
                // work.
                session_free sn3;
                // Same problem here: too expensive to clear later,
                // and we don't really care for our test
                if not (encap_message_p_is_null payload0)
                then encap_message_p_free payload0;
                if not (encap_message_p_is_null payload1)
                then encap_message_p_free payload1;
                // Not freeing msg0 and msg1: consumes a lot of rlimit (I
                // don't understand why) and nothing really important to
                // test.
//                let msg0 = B.index (temp0 <: buffer (buffer uint8)) 0ul in
//                let msg1 = B.index (temp1 <: buffer (buffer uint8)) 0ul in
//                if not (B.is_null (msg0 <: buffer uint8)) then B.free msg0;
//                if not (B.is_null (msg1 <: buffer uint8)) then B.free msg1;
                true
              //| _ -> false
              //end
            | _ -> false
            end
          | _ -> false
          end
        | _ -> false
      in
      // Clear
      session_free sn1;
      session_free sn2;
      device_free dvp1;
      device_free dvp2;
      // Return
      res
      end
    end
  end
#pop-options

/// Third toy example: check SMT patterns on code which interleaves sessions/peers
/// deletion and creation
#restart-solver
[@@ noextract_to "krml"] inline_for_extraction noextract
let test3 (r0 : rid)
          (sk1 : aead_key_t)
          (spriv0 : private_key_t)
          (spub0 spub1 spub2 spub3 spub4 : public_key_t)
          (psk : preshared_key_t)
          (prlg_len : hashable_size_t)
          (prlg : lbuffer uint8 prlg_len) :
  ST bool
  (requires (fun h0 ->
    is_eternal_region r0 /\
    live h0 (sk1 <: buffer uint8) /\
    live h0 (spriv0 <: buffer uint8) /\
    live h0 (spub0 <: buffer uint8) /\
    live h0 (spub1 <: buffer uint8) /\
    live h0 (spub2 <: buffer uint8) /\
    live h0 (spub3 <: buffer uint8) /\
    live h0 (spub4 <: buffer uint8) /\
    live h0 (psk <: buffer uint8) /\
    live h0 prlg /\
    get_dh_pre (idc ()).idc_nc /\
    begin
    let entr_loc = B.loc_addr_of_buffer (entropy_p <: buffer (G.erased entropy)) in
    let r0_loc = region_to_loc r0 in
    let sk1_loc = B.loc_addr_of_buffer (sk1 <: buffer uint8) in
    let spriv0_loc = B.loc_addr_of_buffer (spriv0 <: buffer uint8) in
    let spub0_loc = B.loc_addr_of_buffer (spub0 <: buffer uint8) in
    let spub1_loc = B.loc_addr_of_buffer (spub1 <: buffer uint8) in
    let spub2_loc = B.loc_addr_of_buffer (spub2 <: buffer uint8) in
    let spub3_loc = B.loc_addr_of_buffer (spub3 <: buffer uint8) in
    let spub4_loc = B.loc_addr_of_buffer (spub4 <: buffer uint8) in
    let psk_loc = B.loc_addr_of_buffer (psk <: buffer uint8) in
    let prlg_loc = B.loc_addr_of_buffer (prlg <: buffer uint8) in
    B.all_disjoint [
      entr_loc; r0_loc; sk1_loc; spriv0_loc;
      spub0_loc; spub1_loc; spub2_loc; spub3_loc; spub4_loc; psk_loc; prlg_loc]
    end))
  (ensures (fun h0 _ h1 -> True)) =

  (**) let h0 = ST.get () in
  (**) Lib.Buffer.recall entropy_p;
  // Create the regions
  let (r1, r2, r3, r4, r5, r6) = create_regions6 r0 in
  // Create the devices
  let peer_info = Str.lstring_null MUT in
  let dvp1 = device_create r1 () prlg_len prlg peer_info sk1 spriv0 in
  let bdvp1 = device_p_is_null dvp1 in
  if bdvp1 then false
  else
  begin
  (**) let h3 = ST.get () in
  let peer1 = device_add_peer dvp1 peer_info spub1 psk in
  let peer2 = device_add_peer dvp1 peer_info spub2 psk in
  let peer3 = device_add_peer dvp1 peer_info spub3 psk in
  let bp1 = peer_p_is_null peer1 in
  let bp2 = peer_p_is_null peer2 in
  if bp1 || bp2 then false
  else
    begin
    let pid1 = peer_get_id peer1 in
    let pid2 = peer_get_id peer2 in
    // Remove peer1: peer2 and peer3 should still be valid
    device_remove_peer dvp1 pid1;
    // Test peer3
    let bp3 = peer_p_is_null peer3 in
    if bp3 then false
    else
      begin
      let pid3 = peer_get_id peer3 in
      // Create a session for peer2
      let sn2 = session_create_initiator r2 dvp1 pid2 in
      // Remove peer3: peer2 and session2 should still be valid
      device_remove_peer dvp1 pid3;
      // Free session2 - testing it is valid at the same time
      if session_p_is_null sn2 then false
      else
        begin
        session_free sn2;
        device_free dvp1;
        true
        end
      end
    end
  end

/// Fourth toy example: functional correctness.

[@@ noextract_to "krml"] inline_for_extraction noextract
let wg_dc = idc_get_dc idc

[@@ noextract_to "krml"] inline_for_extraction noextract
let wg_nc = idc_get_config idc

module DS = Spec.Noise.API.Device.Definitions
module S = Spec.Noise.API.Session

/// We only test the boolean returned by this function, but this is enough
/// to test what we want.
[@@ noextract_to "krml"] inline_for_extraction noextract
let test4_spec
  (sk1 sk2 : aead_key)
  (spriv1 spriv2 : private_key wg_nc)
  (spub1 spub2 : public_key wg_nc)
  (psk : preshared_key)
  (prlg : hashable wg_nc)
  (entr0 : entropy) :
  Tot bool =
  let dv1 = DS.create_device wg_dc pattern_IKpsk2 prlg "" (Some sk1) (Some spriv1) in
  let dv2 = DS.create_device wg_dc pattern_IKpsk2 prlg "" (Some sk2) (Some spriv2) in
  match dv1, dv2 with
  | Some dv1, Some dv2 ->
    let res1 = DS.add_peer_get dv1 "" (Some spub2) (Some psk) in
    let res2 = DS.add_peer_get dv2 "" (Some spub1) (Some psk) in
    begin match res1, res2 with
    | Some (p1, dv1), Some (p2, dv2) ->
      let pid1 = DS.peer_get_id p1 in
      let sn1, entr1 = S.create_session dv1 true entr0 (Some pid1) in
      let sn2, entr2 = S.create_session dv2 false entr1 None in
      begin match sn1, sn2 with
      | Res (sn1, dv1), Res (sn2, dv2) ->
        let payload0 = S.pack_message Seq.empty in
        begin match S.write payload0 sn1 with
        | Res (c1, sn1) ->
          begin match S.read () dv2 sn2 c1 with
          | Res (dv2, msg1, sn2) -> true
          | _ -> false
          // Don't do the full handshake: we don't need to test more
          // and it makes the proof a lot faster
          end
        | _ -> false
        end
      | _ -> false
      end
    | _ -> false
    end
  | _ -> false

/// Note that we can only prove partial correctness results.
/// Note that there are a lot of assertions: keep them. They were used to
/// debug the SMT patterns and the signatures, and will be useful to debug
/// them in the future if they are modified.
#push-options "--z3rlimit 200"
[@@ noextract_to "krml"] inline_for_extraction noextract
let test4 (r0 : rid)
          (sk1 sk2 : aead_key_t)
          (spriv1 spriv2 : private_key_t)
          (spub1 spub2 : public_key_t)
          (psk : preshared_key_t)
          (prlg_len : hashable_size_t)
          (prlg : lbuffer uint8 prlg_len)
          (encap0 encap1 : B.pointer encap_message_p_or_null)
          (outlen_p : B.pointer size_t)
          (temp0 temp1 : B.pointer (buffer uint8)) :
  ST bool
  (requires (fun h0 ->
    is_eternal_region r0 /\
    live h0 (sk1 <: buffer uint8) /\
    live h0 (sk2 <: buffer uint8) /\
    live h0 (spriv1 <: buffer uint8) /\
    live h0 (spriv2 <: buffer uint8) /\
    live h0 (spub1 <: buffer uint8) /\
    live h0 (spub2 <: buffer uint8) /\
    live h0 (psk <: buffer uint8) /\
    live h0 prlg /\
    live h0 (encap0 <: buffer encap_message_p_or_null) /\
    live h0 (encap1 <: buffer encap_message_p_or_null) /\
    live h0 (outlen_p <: buffer size_t) /\
    live h0 (temp0 <: buffer (buffer uint8)) /\
    live h0 (temp1 <: buffer (buffer uint8)) /\
    live h0 (B.deref h0 temp0) /\
    live h0 (B.deref h0 temp1) /\
    get_dh_pre (idc ()).idc_nc /\
    begin
    let entr_loc = B.loc_addr_of_buffer (entropy_p <: buffer (G.erased entropy)) in
    let r0_loc = region_to_loc r0 in
    let sk1_loc = B.loc_addr_of_buffer (sk1 <: buffer uint8) in
    let sk2_loc = B.loc_addr_of_buffer (sk2 <: buffer uint8) in
    let spriv1_loc = B.loc_addr_of_buffer (spriv1 <: buffer uint8) in
    let spriv2_loc = B.loc_addr_of_buffer (spriv2 <: buffer uint8) in
    let spub1_loc = B.loc_addr_of_buffer (spub1 <: buffer uint8) in
    let spub2_loc = B.loc_addr_of_buffer (spub2 <: buffer uint8) in
    let psk_loc = B.loc_addr_of_buffer (psk <: buffer uint8) in
    let prlg_loc = B.loc_addr_of_buffer (prlg <: buffer uint8) in
    let encap0_loc = B.loc_addr_of_buffer (encap0 <: buffer encap_message_p_or_null) in
    let encap1_loc = B.loc_addr_of_buffer (encap1 <: buffer encap_message_p_or_null) in
    let outlen_loc = B.loc_addr_of_buffer (outlen_p <: buffer size_t) in
    let temp0_loc = B.loc_addr_of_buffer (temp0 <: buffer (buffer uint8)) in
    let temp1_loc = B.loc_addr_of_buffer (temp1 <: buffer (buffer uint8)) in
    B.all_disjoint [
      entr_loc; r0_loc; sk1_loc; sk2_loc; spriv1_loc; spriv2_loc;
      spub1_loc; spub2_loc; psk_loc; prlg_loc;
      encap0_loc; encap1_loc; outlen_loc;
      temp0_loc; temp1_loc]
    end))
  (ensures (fun h0 b h1 ->
    let entr0_v = B.deref h0 (entropy_p <: buffer (G.erased entropy)) in
    let sk1_v = B.as_seq h0 (sk1 <: buffer uint8) in
    let sk2_v = B.as_seq h0 (sk2 <: buffer uint8) in
    let spriv1_v = B.as_seq h0 (spriv1 <: buffer uint8) in
    let spriv2_v = B.as_seq h0 (spriv2 <: buffer uint8) in
    let spub1_v = B.as_seq h0 (spub1 <: buffer uint8) in
    let spub2_v = B.as_seq h0 (spub2 <: buffer uint8) in
    let psk_v = B.as_seq h0 (psk <: buffer uint8) in
    let prlg_v = B.as_seq h0 (prlg <: buffer uint8) in
    b ==> test4_spec sk1_v sk2_v spriv1_v spriv2_v spub1_v spub2_v psk_v prlg_v entr0_v)) =

  (**) Lib.Buffer.recall entropy_p;
  (**) let h0 = ST.get () in

  // Create the regions
  let (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10) = create_regions10 r0 in
  // Create the devices
  let peer_info = Str.lstring_null MUT in
  let dvp1 = device_create r1 () prlg_len prlg peer_info sk1 spriv1 in
  let dvp2 = device_create r2 () prlg_len prlg peer_info sk2 spriv2 in
  let bdvp1 = device_p_is_null dvp1 in
  let bdvp2 = device_p_is_null dvp2 in
  if bdvp1 || bdvp2 then false
  else
  begin
  (**) let h3 = ST.get () in
  // Add the peers
  let peer1 = device_add_peer dvp1 peer_info spub2 psk in
  let peer2 = device_add_peer dvp2 peer_info spub1 psk in
  (**) let h5 = ST.get () in
  begin
  (**) let entr0_v = B.deref h0 (entropy_p <: buffer (G.erased entropy)) in
  (**) let sk1_v = B.as_seq h0 (sk1 <: buffer uint8) in
  (**) let sk2_v = B.as_seq h0 (sk2 <: buffer uint8) in
  (**) let spriv1_v = B.as_seq h0 (spriv1 <: buffer uint8) in
  (**) let spriv2_v = B.as_seq h0 (spriv2 <: buffer uint8) in
  (**) let spub1_v = B.as_seq h0 (spub1 <: buffer uint8) in
  (**) let spub2_v = B.as_seq h0 (spub2 <: buffer uint8) in
  (**) let psk_v = B.as_seq h0 (psk <: buffer uint8) in
  (**) let prlg_v = B.as_seq h0 (prlg <: buffer uint8) in
  (**) let dvp1_v0 = device_p_v h3 dvp1 in
  (**) let dvp2_v0 = device_p_v h3 dvp2 in
  (**) assert(dvp1_v0 == Some?.v (DS.create_device wg_dc pattern_IKpsk2 prlg_v "" (Some sk1_v) (Some spriv1_v)));
  (**) assert(dvp2_v0 == Some?.v (DS.create_device wg_dc pattern_IKpsk2 prlg_v "" (Some sk2_v) (Some spriv2_v)));
  (**) let res1 = DS.add_peer_get dvp1_v0 "" (Some spub2_v) (Some psk_v) in
  (**) let res2 = DS.add_peer_get dvp2_v0 "" (Some spub1_v) (Some psk_v) in
  (**) assert(not (peer_p_g_is_null peer1) ==> Some? res1);
  (**) assert(not (peer_p_g_is_null peer2) ==> Some? res2)
  end;

  // Test the peers
  let bp1 = peer_p_is_null peer1 in
  let bp2 = peer_p_is_null peer2 in
  if bp1 || bp2 then false
  else
    begin
    // Retrieve the peer ids
    let pid1 = peer_get_id peer1 in
    // Create the sessions
    (**) let h9 = ST.get () in
    let sn1 = session_create_initiator r3 dvp1 pid1 in
    (**) let h10 = ST.get () in
    let sn2 = session_create_responder r4 dvp2 () in
    (**) let h11 = ST.get () in
    // Check the sessions
    let bs1 = session_p_is_null sn1 in
    let bs2 = session_p_is_null sn2 in
    begin
    (**) let entr0_v = B.deref h0 (entropy_p <: buffer (G.erased entropy)) in
    (**) let sk1_v = B.as_seq h0 (sk1 <: buffer uint8) in
    (**) let sk2_v = B.as_seq h0 (sk2 <: buffer uint8) in
    (**) let spriv1_v = B.as_seq h0 (spriv1 <: buffer uint8) in
    (**) let spriv2_v = B.as_seq h0 (spriv2 <: buffer uint8) in
    (**) let spub1_v = B.as_seq h0 (spub1 <: buffer uint8) in
    (**) let spub2_v = B.as_seq h0 (spub2 <: buffer uint8) in
    (**) let psk_v = B.as_seq h0 (psk <: buffer uint8) in
    (**) let prlg_v = B.as_seq h0 (prlg <: buffer uint8) in
    (**) let dvp1_v0 = device_p_v h3 dvp1 in
    (**) let dvp2_v0 = device_p_v h3 dvp2 in
    (**) assert(dvp1_v0 == Some?.v (DS.create_device wg_dc pattern_IKpsk2 prlg_v "" (Some sk1_v) (Some spriv1_v)));
    (**) assert(dvp2_v0 == Some?.v (DS.create_device wg_dc pattern_IKpsk2 prlg_v "" (Some sk2_v) (Some spriv2_v)));
    (**) let res1 = DS.add_peer_get dvp1_v0 "" (Some spub2_v) (Some psk_v) in
    (**) let res2 = DS.add_peer_get dvp2_v0 "" (Some spub1_v) (Some psk_v) in
    (**) assert(Some? res1);
    (**) assert(Some? res2);
    (**) let (peer1_v, dvp1_v1) = Some?.v res1 in
    (**) let (peer2_v, dvp2_v1) = Some?.v res2 in
    (**) assert(peer1_v == peer_p_v h5 peer1);
    (**) assert(peer2_v == peer_p_v h5 peer2);
    (**) assert(peer_id_v pid1 == DS.peer_get_id peer1_v);
    (**) let pid1_v = peer_id_v pid1 in
    (**) assert(entr0_v == B.deref h9 (entropy_p <: buffer (G.erased entropy)));
    (**) let sn1_v0, entr1_v = S.create_session dvp1_v1 true entr0_v (Some pid1_v) in
    (**) let sn2_v0, entr2_v = S.create_session dvp2_v1 false entr1_v None in
    (**) assert(not bs1 ==> Res? sn1_v0);
    (**) assert(not bs2 ==> Res? sn2_v0);
    (**) assert(not bs1 ==> fst (Res?.v sn1_v0) == session_p_v h10 sn1);
    (**) assert(not bs1 ==> fst (Res?.v sn1_v0) == session_p_v h11 sn1)
    end;
    if bs1 || bs2 then false
    else
      begin

      let payload0 = pack_message r5 0ul (B.null #uint8) in
      (**) assert(B.as_seq h11 (B.null #uint8) `Seq.equal` Seq.empty #uint8);
      let write_res1 = session_write payload0 sn1 r6 outlen_p temp0 in

      (**) let h13 = ST.get () in

      match write_res1 with
      | Success ->
        let inlen0 = B.index outlen_p 0ul in
        let msg0 = B.index temp0 0ul in
        let read_res1 = session_read r7 encap0 sn2 inlen0 msg0 in
        begin match read_res1 with
        | Success -> true
        | _ -> false
        end
      | _ -> false
      end
    end
  end
#pop-options
