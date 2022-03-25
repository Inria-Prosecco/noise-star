module Impl.Noise.API.Device

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

open Spec.Noise.SPatterns
open Spec.Noise.API.State
open Spec.Noise.API.Device
module M = Spec.Noise.Map
module Spec = Spec.Noise.API.Device.Definitions

open Impl.Noise.Types
open Impl.Noise.HandshakeState
open Impl.Noise.SendReceive
open Impl.Noise.RecursiveMessages
open Impl.Noise.API.State
module State = Impl.Noise.API.State
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.BufferEquality
open Impl.Noise.TypeOrUnit
open Impl.Noise.Allocate
open Spec.Noise
open Spec.Noise.API.MetaInfo

open Meta.Noise

module LL = Impl.Noise.LinkedList
module St = Impl.Noise.Stateful

open Lib.Memzero0

open Lib.RandomSequence
open Lib.RandomBuffer.System

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

val _align_fsti : unit

(*** Type definitions *)

(*[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let stateful_info_buffer (a:Type0) (l: UInt32.t { UInt32.v l > 0 }) (zero: a):
  St.stateful_malloc_from_input_clone_copy unit =
  St.Stateful_malloc_from_input_clone_copy
    (* Stateful input *)
    (St.stateful_buffer a l zero)

    (* Stateful *)
    (St.stateful_buffer a l zero)

    (* Malloc *)
    (fun i r ->
      B.malloc r zero l)

    (* Malloc from input *)
    (fun i r x ->
      (**) let h0 = get () in
      let c = B.malloc r zero l in
      B.blit x 0ul c 0ul l;
      (**) let h1 = get () in
      (**) B.(modifies_only_not_unused_in loc_none h0 h1);
      c)

    (* Clone *)
    (fun #_ r x ->
      (**) let h0 = get () in
      let c = B.malloc r zero l in
      B.blit x 0ul c 0ul l;
      (**) let h1 = get () in
      (**) B.(modifies_only_not_unused_in loc_none h0 h1);
      c)
    
    (* Free *)
    (fun _ s ->
      (* Don't leave sensitive information on the heap - that may be
       * overconservative, but it shouldn't be a performance issue *)
      Lib.Memzero0.memzero s l;
      B.free s)

    (* Copy *)
    (fun _ s_dst s_src -> B.blit s_src 0ul s_dst 0ul l)

    (* Input from output *)
    (fun _ x -> x)*)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let stateful_info_unit :
  St.stateful_malloc_from_input_clone_copy unit =
  St.Stateful_malloc_from_input_clone_copy
    (* Stateful input *)
    (St.stateful_unused unit)

    (* Stateful *)
    (St.stateful_unused unit)

    (* Malloc *)
    (fun i r -> ())

    (* Malloc from input *)
    (fun i r x -> ())
    
    (* Clone *)
    (fun #_ r x -> ())
    
    (* Free *)
    (fun _ s -> ())

    (* Copy *)
    (fun _ s_dst s_src -> ())

    (* Input from output *)
    (fun _ x -> x)

    (* Conversion to sequences/bytes *)
    (fun #_ x -> Seq.empty)
    (fun #_ x ->
      (**) let h0 = ST.get () in
      (**) assert(Seq.equal (B.as_seq h0 (B.null #uint8)) Seq.empty);
      (0ul, B.null))
    (fun #_ x -> Seq.empty)
    (fun #_ x ->
      (**) let h0 = ST.get () in
      (**) assert(Seq.equal (B.as_seq h0 (B.null #uint8)) Seq.empty);
      (0ul, B.null))

/// We try to do something general for the policy function: it is thus a stateful
/// function. However, for now, we will only use constant functions, so we provide
/// a way to simplify a bit the control-flow so that no dynamic tests happen when
/// it is not necessary.
/// The [recv_psk] parameter controls whether we should lookup a psk when receiving
/// a remote static. If it is the case, then the policy should always fail: the policy
/// is applied on unknown remote static keys, and so far, the only way to lookup a psk
/// is to lookup a peer).

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type constrained_policy_function (nc : config) (always_false : bool) =
  f:policy_function nc{always_false ==> (forall rs. f rs = false)}

inline_for_extraction noextract noeq
type stateful_policy_function (nc : iconfig) (recv_psk : bool) =
| Stateful_policy_function:
  
  // Return type
  rtype: Type0 ->
  
  // Used to simplify the control flow
  is_success: (rtype -> Tot bool) ->

  // Used to simplify the control flow
  always_false : bool{recv_psk ==> always_false} ->

  // Spec
  apply_policy_spec: constrained_policy_function (get_config nc) always_false ->
  
  // Implementation
  apply_policy: (
    k:public_key_t nc ->
    Stack rtype
    (requires (fun h0 -> live h0 k))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      is_success r = apply_policy_spec (as_seq h0 k))))  ->
  
  stateful_policy_function nc recv_psk

/// Two policy implementations: always true (WhatsApp flavour), always false (Wireguard flavour)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let true_stateful_policy_function (nc : iconfig) :
  stateful_policy_function nc false =
Stateful_policy_function
  unit // rtype
  (fun x -> true) // is_success
  false // always false
  (fun x -> true) // apply_policy_spec
  (fun x -> ()) // apply_policy

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let false_stateful_policy_function (nc : iconfig) (recv_psk : bool) :
  stateful_policy_function nc recv_psk =
Stateful_policy_function
  unit // rtype
  (fun x -> false) // is_success
  true // always false
  (fun x -> false) // apply_policy_spec
  (fun x -> ()) // apply_policy

inline_for_extraction noextract noeq
type stateful_certification_state (nc : iconfig) (peer_info : stateful_peer_info) =
| Stateful_cstate:
  cstate:St.stateful unit ->
  
  // Return type
  cst_rtype: Type0 ->
  
  // Used to simplify the control flow (could always return true, for instance)
  cst_is_success: (cst_rtype -> Tot bool) ->
  
  // Used to simplify the control flow
  cst_always_success: bool{cst_always_success ==> (forall r. cst_is_success r)} ->
  
  // Pure operations
  certify_spec : certification_function (get_config nc) (peer_info.St.t ())
                                        (cstate.St.t ()) ->

  // Stateful operations
  certify: (
    state:cstate.St.s () ->
    rs:public_key_t nc ->
    payload_len:hashable_size_t nc ->
    payload:hashable_t nc payload_len ->
    // TODO: we should rather take a pointer to a peer
    pinfo:peer_info.St.s () ->
    // Updating pinfo might require stateful modifications
    ST cst_rtype
    (requires (fun h0 ->
      cstate.St.invariant h0 state /\
      peer_info.St.invariant h0 pinfo /\
      live h0 payload /\
      
      begin
      let state_loc = cstate.St.footprint state in
      let rs_loc = B.loc_buffer (rs <: buffer uint8) in
      let payload_loc = B.loc_buffer (payload <: buffer uint8) in
      let pinfo_loc = peer_info.St.footprint pinfo in
      B.all_disjoint [state_loc; rs_loc; payload_loc; pinfo_loc]
      end
      ))

    (ensures (fun h0 res h1 ->
      B.(modifies (peer_info.St.footprint pinfo) h0 h1) /\
    
      cstate.St.invariant h1 state /\
      peer_info.St.invariant h1 pinfo /\
      (peer_info.St.freeable h0 pinfo ==>
       peer_info.St.freeable h1 pinfo) /\
      
      begin
      let state_v0 = cstate.St.v () h0 state in
      let rs_v = B.as_seq h0 (rs <: buffer uint8) in
      let payload_v = as_seq h0 payload in
      let res_v = certify_spec state_v0 rs_v payload_v in
      begin match res_v with
      | None -> not (cst_is_success res)
      | Some pinfo_v ->
        cst_is_success res /\
        pinfo_v == peer_info.St.v () h1 pinfo
      end
      end))) ->

  stateful_certification_state nc peer_info

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type true_certification_state
  (nc : iconfig)
  (peer_info : stateful_peer_info{peer_info.St.s () == unit /\ peer_info.St.t () == unit}) :
  stateful_certification_state nc peer_info =
 Stateful_cstate
  (St.stateful_unused unit) // cstate
  unit // return type
  (fun b -> true) // is success
  true // always success
  (fun _ _ _ -> Some ()) // certify spec
  (fun _ _ _ _ _ -> ()) // certify

/// In theory this is useless, because if we don't want to certify any
/// new, unregistered key, the user should set up the policy to reject all
/// unknown keys and the certification function will never get called.
/// But we still need to provide a certification state implementation.
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type false_certification_state
  (nc : iconfig)
  (peer_info : stateful_peer_info) :
  stateful_certification_state nc peer_info =
 Stateful_cstate
  (St.stateful_unused unit) // cstate
  unit // return type
  (fun b -> false) // is success
  false // always success
  (fun _ _ _ -> None) // certify spec
  (fun _ _ _ _ _ -> ()) // certify

/// Peer/state id implementation
inline_for_extraction noextract
noeq type id_cl = {
  id_t : eqtype;
  id_none : id_t; // None element: means there is no id
  id_zero : zero:id_t{zero <> id_none}; // First pid
  id_max : max:id_t{max <> id_none};
  id_v : id:id_t{id <> id_none} -> GTot peer_id;
  id_increment :
    id:id_t{id <> id_none /\ id <> id_max} ->
    Tot (id':id_t{id' <> id_none /\ id_v id' = id_v id + 1 });
  id_zero_v_lem : unit -> Lemma (id_v id_zero = 0);
  id_v_injective_lem :
    x:id_t{x <> id_none} ->
    y:id_t{y <> id_none} ->
    Lemma (id_v x = id_v y ==>  x = y);
}

/// An implementation of the identifiers
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let uint_id_cl (t : inttype{unsigned t}) : id_cl = {
  id_t = int_t t PUB;
  id_none = uint 0;
  id_zero = uint 1;
  id_max = with_onorm #(int_t t PUB) (uint (maxint t));
  id_increment = (fun x -> add x (uint 1));
  id_v = (fun x -> uint_v x - 1);
  id_zero_v_lem = (fun _ -> ());
  id_v_injective_lem = (fun x y -> ());
}

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type id_cl_opt_t (idc : id_cl) = idc.id_t
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type id_cl_t (idc : id_cl) = id:idc.id_t{id <> idc.id_none}

[@@ noextract_to "Kremlin"] noextract
let id_cl_v (#idc : id_cl) (id : id_cl_t idc) : GTot peer_id =
  idc.id_v id

[@@ noextract_to "Kremlin"] noextract
let id_cl_opt_v (#idc : id_cl) (id : idc.id_t) : (GTot (option peer_id)) =
  if id = idc.id_none then None else Some (idc.id_v id)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let id_cl_none (idc : id_cl) : id:id_cl_opt_t idc{id_cl_opt_v id == None} = idc.id_none
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let id_cl_max (idc : id_cl) : id_cl_t idc = idc.id_max
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let id_cl_max_v (idc : id_cl) : GTot nat = Some?.v (id_cl_opt_v idc.id_max)

/// A device contains a static key if the initiator or the responder uses a
/// static key, because it can be used to produce initiators and responders.
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_has_s (hsk : handshake_pattern) : Tot bool =
  [@inline_let] let init_ks = with_onorm (key_slots_from_pattern true hsk) in
  [@inline_let] let resp_ks = with_onorm (key_slots_from_pattern false hsk) in
  init_ks.ks_s || resp_ks.ks_s

/// Peers contain keys if the initiator or the responder uses a remote static key
/// (any peer can be used as initiator or responder).
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peers_have_s (hsk : handshake_pattern) : Tot bool =
  [@inline_let] let init_ks = with_norm (key_slots_from_pattern true hsk) in
  [@inline_let] let resp_ks = with_norm (key_slots_from_pattern false hsk) in
  init_ks.ks_rs || resp_ks.ks_rs

/// Configuration
inline_for_extraction noextract
noeq type idconfig_raw : Type u#1 = {
  idc_nc : iconfig;
  idc_dc : dc:dconfig{dc.dc_nc = get_config idc_nc};
  idc_pattern : wfs_handshake_pattern; // TODO: in the spec, stored directly in the state
  idc_sid_cl : id_cl;
  idc_pid_cl : id_cl;
  // TODO: we should use malloc_from_input only (with a null pointer value)
  idc_info : pi:St.stateful_malloc_from_input_clone_copy unit{
    pi.St.smficc_stateful.St.t () == idc_dc.dc_info /\
    pi.St.smficc_to_bytes_seq #() == idc_dc.dc_info_to_bytes};
  idc_policy : p:stateful_policy_function idc_nc (with_onorm (check_hsk_is_psk idc_pattern)) {
    Stateful_policy_function?.apply_policy_spec p == idc_dc.dc_policy // TODO: not sure we shouldn't parameterize by the spec function instead
    };
  idc_cert_state : c:stateful_certification_state idc_nc idc_info.St.smficc_stateful{
    c.cstate.St.t () == idc_dc.dc_cert_state /\
    c.certify_spec == idc_dc.dc_certification};
  // Do we use serialization/deserialization?
  idc_serialize : bool;
}

/// Small trick to prevent normalization explosion: rather than directly
/// manipulating a dconfig, we manipulate a function: unit -> dconfig.
/// This function can be made [strict_on_arguments], allowing to hide
/// the (huge) dconfig body until the moment we actually need to access
/// a precise field, at which point the definition is immediately reduced (as
/// we only need part of it) to a term of a reasonable size.
type idconfig = unit -> idconfig_raw

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_nc (idc : idconfig) : iconfig =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> nc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_config (idc : idconfig) : config =
  get_config (idc_get_nc idc)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_dc (idc : idconfig) : dconfig =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> dc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_pattern (idc : idconfig) : wfs_handshake_pattern =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> pat

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_sid (idc : idconfig) : id_cl =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> sid

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_pid (idc : idconfig) : id_cl =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> pid

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_info (idc : idconfig) : St.stateful_malloc_from_input_clone_copy unit =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> pinfo

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_is_psk (idc : idconfig) : bool =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> with_onorm (check_hsk_is_psk pat)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_policy (idc : idconfig) : stateful_policy_function (idc_get_nc idc) (idc_is_psk idc) =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> policy

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_policy_spec (idc : idconfig) :
  constrained_policy_function (idc_get_config idc) (idc_is_psk idc) =
  (idc_get_policy idc).apply_policy_spec

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_cstate (idc : idconfig) : stateful_certification_state (idc_get_nc idc) (idc_get_info idc).St.smficc_stateful =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> cert

inline_for_extraction
let idc_get_cstate_s (idc : idconfig) : Type0 =
  (idc_get_cstate idc).cstate.St.s ()
inline_for_extraction
let idc_get_cstate_t (idc : idconfig) : Type0 =
  (idc_get_cstate idc).cstate.St.t ()
inline_for_extraction
let idc_get_cstate_v (#idc : idconfig) : mem -> idc_get_cstate_s idc -> GTot (idc_get_cstate_t idc) =
  (idc_get_cstate idc).cstate.St.v ()

inline_for_extraction
let idc_get_cstate_footprint (#idc : idconfig) =
  (idc_get_cstate idc).cstate.St.footprint
inline_for_extraction
let idc_get_cstate_invariant (#idc : idconfig) =
  (idc_get_cstate idc).cstate.St.invariant
inline_for_extraction
let idc_get_cstate_frame_invariant (#idc : idconfig) =
  (idc_get_cstate idc).cstate.St.frame_invariant
inline_for_extraction
let idc_get_cstate_frame_freeable (#idc : idconfig) =
  (idc_get_cstate idc).cstate.St.frame_freeable

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_get_serialize (idc : idconfig) : bool =
  match idc () with Mkidconfig_raw nc dc pat sid pid pinfo policy cert srlz -> srlz

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_uses_s (idc : idconfig) : bool =
  device_has_s (idc_get_pattern idc)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_peers_have_s (idc : idconfig) : bool =
  peers_have_s (idc_get_pattern idc)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_input_t (idc : idconfig) : Type0 =
  (idc_get_info idc).St.smficc_input.St.s ()
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_input_s (idc : idconfig) : Type0 =
  (idc_get_info idc).St.smficc_input.St.t ()
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_input_v (#idc : idconfig) (h : mem) (info : info_input_t idc) :
  GTot (info_input_s idc) =
  (idc_get_info idc).St.smficc_input.St.v () h info
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_input_footprint (#idc : idconfig) =
  (idc_get_info idc).St.smficc_input.St.footprint
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_input_invariant (#idc : idconfig) =
  (idc_get_info idc).St.smficc_input.St.invariant
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_input_frame_invariant (#idc : idconfig) =
  (idc_get_info idc).St.smficc_input.St.frame_invariant

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_t (idc : idconfig) : Type0 =
  (idc_get_info idc).St.smficc_stateful.St.s ()
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_s (idc : idconfig) : Type0 =
  (idc_get_info idc).St.smficc_stateful.St.t ()
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_v (#idc : idconfig) (h : mem) (info : info_t idc) :
  GTot (info_s idc) =
  (idc_get_info idc).St.smficc_stateful.St.v () h info
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_footprint (#idc : idconfig) =
  (idc_get_info idc).St.smficc_stateful.St.footprint
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_invariant (#idc : idconfig) =
  (idc_get_info idc).St.smficc_stateful.St.invariant
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_freeable (#idc : idconfig) =
  (idc_get_info idc).St.smficc_stateful.St.freeable
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_frame_invariant (#idc : idconfig) =
  (idc_get_info idc).St.smficc_stateful.St.frame_invariant
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let info_frame_freeable (#idc : idconfig) =
  (idc_get_info idc).St.smficc_stateful.St.frame_freeable

// TODO: we might remove those definitions in the future
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_info_t (idc : idconfig) : Type0 = info_t idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_info_s (idc : idconfig) : Type0 = info_s idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_info_v (#idc : idconfig) (h : mem) (pinfo : peer_info_t idc) = info_v h pinfo
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_info_footprint (#idc : idconfig) = info_footprint #idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_info_invariant (#idc : idconfig) = info_invariant #idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_info_freeable (#idc : idconfig) = info_freeable #idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_info_frame_invariant (#idc : idconfig) = info_frame_invariant #idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_info_frame_freeable (#idc : idconfig) = info_frame_freeable #idc

/// Serialization/deserialization types
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let serialize_key_t (idc : idconfig) : Type0 = type_or_unit aead_key_t (idc_get_serialize idc)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let enc_private_key_vsv (nc : iconfig) : size_nat = private_key_vsv nc + aead_tag_vsv
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let enc_private_key_vs (nc : iconfig) = size (enc_private_key_vsv nc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let enc_private_key_t (idc : idconfig) =
  type_or_unit (lbuffer uint8 (enc_private_key_vs (idc_get_nc idc))) (idc_uses_s idc) 

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let enc_private_key_with_nonce_vsv (nc : iconfig) : size_nat =
  enc_private_key_vsv nc + aead_nonce_size
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let enc_private_key_with_nonce_vs (nc : iconfig) = size (enc_private_key_with_nonce_vsv nc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let enc_private_key_with_nonce_t (idc : idconfig) =
  type_or_unit (lbuffer uint8 (enc_private_key_with_nonce_vs (idc_get_nc idc))) (idc_uses_s idc) 

(*** Peers *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val peer_t (idc : idconfig) : Type0

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val peer_p_or_null (idc : idconfig) : Type0

val peer_p_g_is_null (#idc : idconfig) (p : peer_p_or_null idc) : GTot bool

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val peer_p_null (idc : idconfig) : p:peer_p_or_null idc{peer_p_g_is_null p}

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_p (idc : idconfig) : Type0 = p:peer_p_or_null idc{not (peer_p_g_is_null p)}

val peer_p_invariant (#idc : idconfig) (h : mem) (p : peer_p idc) : GTot Type0
val peer_p_footprint (#idc : idconfig) (p : peer_p idc) : GTot B.loc

val peer_p_live (#idc : idconfig) (h : mem) (p : peer_p_or_null idc) :
  Ghost Type0
  (ensures (True))
  (ensures (fun t ->
    t ==> (if peer_p_g_is_null p then True else peer_p_invariant h p)))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val peer_p_is_null (#idc : idconfig) (p : peer_p_or_null idc) :
  Stack bool
  (requires (fun h0 -> peer_p_live h0 p))
  (ensures (fun h0 b h1 ->
    h0 == h1 /\ b == peer_p_g_is_null p))

let peer_p_or_null_footprint (#idc : idconfig) (p : peer_p_or_null idc) : GTot B.loc =
  if peer_p_g_is_null p then B.loc_none
  else peer_p_footprint p

val peer_p_invariant_live_lem (#idc : idconfig) (h : mem) (p : peer_p idc) :
  Lemma
  (requires (peer_p_invariant h p))
  (ensures (peer_p_live h p))
  [SMTPat (peer_p_invariant h p)]

[@@ noextract_to "Kremlin"] noextract
let peer_s (idc : idconfig) : Type0 = peer (idc_get_dc idc)

val peer_p_v (#idc : idconfig) (h : mem) (p : peer_p idc) : GTot (peer_s idc)

let peer_p_or_null_v (#idc : idconfig) (h : mem) (p : peer_p_or_null idc) :
  GTot (option (peer_s idc)) =
  if peer_p_g_is_null p then None
  else Some (peer_p_v h p)

let peer_p_g_get_id (#idc : idconfig) (h : mem) (p : peer_p idc) : GTot peer_id =
  let p_v = peer_p_v h p in
  peer_get_id p_v

let peer_p_g_get_info (#idc : idconfig) (h : mem) (p : peer_p idc) : GTot (idc_get_dc idc).dc_info =
  let p_v = peer_p_v h p in
  peer_get_info p_v

let peer_p_g_get_static (#idc : idconfig) (h : mem) (p : peer_p idc) :
  GTot (option (public_key (idc_get_config idc))) =
  let p_v = peer_p_v h p in
  peer_get_static p_v

let peer_p_g_get_psk (#idc : idconfig) (h : mem) (p : peer_p idc) :
  GTot (option (preshared_key)) =
  let p_v = peer_p_v h p in
  peer_get_psk p_v

let peer_p_or_null_g_get_pid (#idc : idconfig) (h : mem) (p : peer_p_or_null idc) :
  GTot (option peer_id) =
  if peer_p_g_is_null p then None
  else Some (peer_p_g_get_id h p)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_rs_t idc = public_key_t_or_unit (idc_get_nc idc) (peers_have_s (idc_get_pattern idc))
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let idc_psk_t idc = preshared_key_t_or_unit (idc_is_psk idc)

//[@@ noextract_to "Kremlin"] inline_for_extraction noextract
//let states_id_opt_t idc = (idc_get_sid idc).id_t
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_id_t idc = id_cl_t (idc_get_sid idc)
//[@@ noextract_to "Kremlin"] inline_for_extraction noextract
//let states_id_opt_v (#idc : idconfig) = id_cl_opt_v #(idc_get_sid idc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_id_v (#idc : idconfig) = id_cl_v #(idc_get_sid idc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_id_max (idc : idconfig) : state_id_t idc = id_cl_max (idc_get_sid idc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let state_id_max_v (idc : idconfig) : GTot nat = id_cl_max_v (idc_get_sid idc)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let session_id_t idc = state_id_t idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let session_id_v (#idc : idconfig) = state_id_v #idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let session_id_max (idc : idconfig) = state_id_max idc
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let session_id_max_v (idc : idconfig) = state_id_max_v idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_id_opt_t idc = (idc_get_pid idc).id_t
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_id_t idc = id_cl_t (idc_get_pid idc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_id_opt_v (#idc : idconfig) = id_cl_opt_v #(idc_get_pid idc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_id_v (#idc : idconfig) = id_cl_v #(idc_get_pid idc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_id_none (idc : idconfig) : z:peer_id_opt_t idc{peer_id_opt_v z = None} = id_cl_none (idc_get_pid idc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_id_max (idc : idconfig) : peer_id_t idc = id_cl_max (idc_get_pid idc)
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_id_max_v (idc : idconfig) : GTot nat = id_cl_max_v (idc_get_pid idc)

/// Some framing lemmas. Note that those lemmas don't have SMT patterns:
/// we don't use them in practice. See the framing lemmas for peer_p_or_null.
val peer_p_frame_live :
     #idc:idconfig
  -> l:B.loc
  -> p:peer_p_or_null idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    peer_p_live h0 p /\
    B.loc_disjoint l (peer_p_or_null_footprint p) /\
    B.modifies l h0 h1))
  (ensures (
    peer_p_live h1 p))

val peer_p_frame_invariant :
     #idc:idconfig
  -> l:B.loc
  -> p:peer_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    peer_p_invariant h0 p /\
    B.loc_disjoint l (peer_p_footprint p) /\
    B.modifies l h0 h1))
  (ensures (
    peer_p_invariant h1 p /\
    peer_p_v h0 p == peer_p_v h1 p))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type peer_p_get_id_st (idc : idconfig) =
  p:peer_p idc ->
  Stack (peer_id_t idc)
  (requires (fun h0 -> peer_p_invariant h0 p))
  (ensures (fun h0 pid h1 ->
    h1 == h0 /\
    peer_id_v pid = peer_p_g_get_id h0 p))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_peer_p_get_id :
  #idc:idconfig ->
  peer_p_get_id_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type peer_p_get_info_st (idc : idconfig) =
  // We copy the peer information to out
  out:peer_info_t idc ->
  p:peer_p idc ->
  ST unit
  (requires (fun h0 ->
    peer_info_invariant h0 out /\
    peer_p_invariant h0 p /\
    B.(all_disjoint [peer_info_footprint out; peer_p_footprint p])))
  (ensures (fun h0 _ h1 ->
    B.(modifies (peer_info_footprint out) h0 h1) /\
    (peer_info_freeable h0 out ==> peer_info_freeable h1 out) /\
    peer_info_invariant h1 out /\
    peer_info_v h1 out == peer_p_g_get_info h0 p))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_peer_p_get_info :
     #idc:idconfig
  -> peer_p_get_info_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type peer_p_get_static_st (idc : idconfig{idc_peers_have_s idc}) =
  out:public_key_t_or_unit (idc_get_nc idc) (idc_peers_have_s idc) ->
  p:peer_p idc ->
  ST unit
  (requires (fun h0 ->
    lbuffer_or_unit_live h0 out /\
    peer_p_invariant h0 p /\
    B.(all_disjoint [lbuffer_or_unit_loc out; peer_p_footprint p])))
  (ensures (fun h0 pid h1 ->
    B.(modifies (lbuffer_or_unit_loc out) h0 h1) /\
    lbuffer_or_unit_to_opt_lseq h1 out == peer_p_g_get_static h0 p))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_peer_p_get_static :
     #idc:idconfig{idc_peers_have_s idc}
  -> peer_p_get_static_st idc

/// Extraction helpers for the instanciation: if the peers have a static key, the
/// definition implements peer_get_static, otherwise it is unit, meaning the
/// definition gets erased at extraction.
// The following type definition doesn't typecheck if we use type_or_unit
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_p_get_static_st_or_unit (idc:idconfig) : Type0=
  if idc_peers_have_s idc then peer_p_get_static_st idc else unit
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_peer_p_get_static_or_unit :
     #idc:idconfig
  -> peer_p_get_static_st_or_unit idc =
  fun #idc -> if idc_peers_have_s idc then mk_peer_p_get_static #idc else ()

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type peer_p_get_psk_st (idc : idconfig{idc_is_psk idc}) =
  out:preshared_key_t ->
  p:peer_p idc ->
  ST unit
  (requires (fun h0 ->
    live h0 out /\
    peer_p_invariant h0 p /\
    B.all_disjoint [loc out; peer_p_footprint p]))
  (ensures (fun h0 pid h1 ->
    B.modifies (loc out) h0 h1 /\
    Some? (peer_p_g_get_psk h0 p) /\
    as_seq h1 out == Some?.v (peer_p_g_get_psk h0 p)))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_peer_p_get_psk :
     #idc:idconfig{idc_is_psk idc}
  -> peer_p_get_psk_st idc

/// Extraction helpers for the instanciation: see the comment for mk_peer_p_get_static_or_unit
// The following type definition doesn't typecheck if we use type_or_unit
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let peer_p_get_psk_st_or_unit (idc:idconfig) : Type0=
  if idc_is_psk idc then peer_p_get_psk_st idc else unit
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_peer_p_get_psk_or_unit :
     #idc:idconfig
  -> peer_p_get_psk_st_or_unit idc =
  fun #idc -> if idc_is_psk idc then mk_peer_p_get_psk #idc else ()

(*** Configuration *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let knows_rs_at_init (idc : idconfig) (initiator : bool) =
  Spec.Noise.API.MetaInfo.knows_remote_at_init (idc_get_pattern idc) initiator

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let knows_psk_at_init (idc : idconfig) (initiator : bool) =
  Spec.Noise.API.MetaInfo.knows_psk_at_init (idc_get_pattern idc) initiator

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let knows_remote_at_init (idc : idconfig) (initiator : bool) =
  Spec.Noise.API.MetaInfo.knows_remote_at_init (idc_get_pattern idc) initiator

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type opt_pid_t (idc : idconfig) (initiator : bool) =
  type_or_unit (idc_get_pid idc).id_t (with_onorm (knows_remote_at_init idc initiator))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type opt_pid_s = option (peer_id)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let opt_pid_v (#idc : idconfig) (#initiator : bool) (pid : opt_pid_t idc initiator) :
  GTot opt_pid_s =
  if knows_remote_at_init idc initiator then peer_id_opt_v #idc pid
  else None

[@@ (strict_on_arguments [0]); noextract_to "Kremlin"] noextract
let check_pattern (pattern : handshake_pattern) : Tot bool =
  let is_psk = check_hsk_is_psk pattern in
  let b1 = Impl.Noise.API.State.Base.handshake_pattern_is_valid pattern in
  let b2 = Impl.Noise.API.State.StateMachine.check_pattern pattern in
  // We need an extra value to encode the error state (if a state
  // encounter an error while processing a message, we update its
  // status so that it gets stuck and unusable)
  let b3 = List.Tot.length pattern.messages + 1 <= max_size_t in
  b1 && b2 && b3

[@@ noextract_to "Kremlin"] noextract
let idc_is_valid_compute (idc : idconfig) : Tot bool =
  let pattern = idc_get_pattern idc in
  let is_psk = idc_is_psk idc in
  check_pattern pattern

// TODO: make this visible and remove the lemma?
//[@@ (strict_on_arguments [0]); noextract_to "Kremlin"]
[@@ noextract_to "Kremlin"]
inline_for_extraction noextract
val idc_is_valid (idc : idconfig) : Tot bool

val idc_is_valid_lem (idc : idconfig) :
  Lemma(idc_is_valid idc = idc_is_valid_compute idc)
  [SMTPat (idc_is_valid idc)]

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type valid_idc = idc:idconfig{idc_is_valid idc}

(*** Device *)
(**** Types and helpers *)
noeq type sized_buffer = {
  size : UInt32.t;
  buffer : lbuffer uint8 size;
}

[@@ noextract_to "Kremlin"] noextract
let sized_buffer_to_loc (b : sized_buffer) : GTot B.loc =
  if g_is_null b.buffer then B.loc_buffer (b.buffer <: buffer uint8)
  else B.loc_addr_of_buffer (b.buffer <: buffer uint8)

[@@ noextract_to "Kremlin"] noextract
let sized_buffer_live (h : mem) (b : sized_buffer) : GTot Type0 =
  B.live h (b.buffer <: buffer uint8)

[@@ noextract_to "Kremlin"] noextract
let sized_buffer_freeable (b : sized_buffer) : GTot Type0 =
  not(g_is_null b.buffer) ==> B.freeable (b.buffer <: buffer uint8)

[@@ noextract_to "Kremlin"] noextract
let sized_buffer_to_seq (h : mem) (b : sized_buffer) : GTot (seq uint8) =
  B.as_seq h (b.buffer <: buffer uint8)

/// Hashable sized buffer
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let hsized_buffer (nc : iconfig) =
  sb:sized_buffer{is_hashable_size (get_config nc) (size_v sb.size)}

// We reveal this for the type abbreviations
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_t (idc : idconfig) : Type0

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_p_or_null (idc : idconfig) : Type0

val device_p_g_is_null (#idc : idconfig) (dvp : device_p_or_null idc) : GTot bool

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
type device_p (idc : idconfig) =
  dvp:device_p_or_null idc{not (device_p_g_is_null dvp)}

val device_p_live (#idc : idconfig) (h : mem) (dvp : device_p_or_null idc) : GTot Type0
val device_p_invariant (#idc : idconfig) (h : mem) (dvp : device_p idc) : GTot Type0

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_p_is_null (#idc : idconfig) (dvp : device_p_or_null idc) :
  Stack bool
  (requires (fun h0 ->
    device_p_live h0 dvp))
  (ensures (fun h0 b h1 ->
    h0 == h1 /\ b == device_p_g_is_null dvp))

let device_p_or_null_invariant
  (#idc : idconfig) (h : mem)
  (dvp : device_p_or_null idc) : GTot Type0 =
  device_p_live h dvp /\
  begin
  if device_p_g_is_null dvp then True
  else device_p_invariant h dvp
  end

// By providing an access to the device rid and revealing the fact that the
// device footprint is in this region, rather than only providing [device_p_region_of],
// we allow ourselves to write recall lemmas like [device_p_recall_region].
val device_p_rid_of (#idc : idconfig) (dvp : device_p idc) :
  GTot HS.rid

let device_p_region_of (#idc : idconfig) (dvp : device_p idc) : GTot B.loc =
  region_to_loc (device_p_rid_of dvp)

let device_p_or_null_region_of (#idc : idconfig) (dvp : device_p_or_null idc) : GTot B.loc =
  if device_p_g_is_null dvp then B.loc_none
  else region_to_loc (device_p_rid_of dvp)

// Recall lemma for the device region
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_p_recall_region (#idc : idconfig) (dvp : device_p idc) :
  Stack unit
  (requires (fun h0 ->
    device_p_invariant h0 dvp))
  (ensures (
    fun h0 _ h1 ->
    h0 == h1 /\
    // The device region is in the current memory (note: doesn't give
    // us that all its locs are in the memory)
    device_p_rid_of dvp `is_in` get_hmap h1 /\
    // The region is disjoint from the stack (note: gives us that all
    // is locs are disjoint from the stack)
    (is_stack_region (get_tip h0) ==>
     Monotonic.HyperHeap.disjoint (get_tip h1) (device_p_rid_of dvp))))

val device_p_owns_peer :
     #idc:idconfig
  -> h:mem
  -> dvp:device_p idc
  -> p:peer_p_or_null idc ->
  GTot Type0

val device_p_owns_peer_lem :
     #idc:idconfig
  -> h:mem
  -> dvp:device_p idc
  -> p:peer_p_or_null idc ->
  Lemma
  (requires (
    device_p_invariant h dvp /\
    device_p_owns_peer h dvp p))
  (ensures (
    if peer_p_g_is_null p then True
    else
      peer_p_invariant h p /\
      region_includes (device_p_rid_of dvp) (peer_p_footprint p)))

[@@ noextract_to "Kremlin"] noextract
let device_s (idc : idconfig) = device (idc_get_dc idc)

[@@ noextract_to "Kremlin"] noextract
val device_p_v (#idc : idconfig) (m : mem) (dvp : device_p idc) : GTot (device_s idc)

[@@ noextract_to "Kremlin"] noextract
val device_p_get_cstate (#idc : idconfig) (h : mem) (dv : device_p idc) :
  GTot (idc_get_cstate_s idc)

[@@ noextract_to "Kremlin"] noextract
let device_p_g_get_states_counter_v (#idc : idconfig) (h : mem) (dv : device_p idc) :
  GTot state_id =
  let dv_v = device_p_v h dv in
  device_get_states_counter dv_v

[@@ noextract_to "Kremlin"] noextract
let device_p_g_get_sessions_counter_v #idc =
  device_p_g_get_states_counter_v #idc

[@@ noextract_to "Kremlin"] noextract
let device_p_g_get_peers_counter_v (#idc : idconfig) (h : mem) (dv : device_p idc) :
  GTot peer_id =
  let dv_v = device_p_v h dv in
  device_get_peers_counter dv_v

[@@ noextract_to "Kremlin"] noextract
val device_p_g_get_states_counter (#idc : idconfig) (h : mem) (dv : device_p idc) :
  Ghost (state_id_t idc)
  (requires True)
  (ensures (fun cnt -> state_id_v cnt = device_p_g_get_states_counter_v h dv))

[@@ noextract_to "Kremlin"] noextract
let device_p_g_get_sessions_counter #idc = device_p_g_get_states_counter #idc

[@@ noextract_to "Kremlin"] noextract
val device_p_g_get_peers_counter (#idc : idconfig) (h : mem) (dv : device_p idc) :
  Ghost (peer_id_t idc)
  (requires True)
  (ensures (fun cnt -> peer_id_v cnt = device_p_g_get_peers_counter_v h dv))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_get_states_counter_st (idc : idconfig) =
  dvp:device_p idc ->
  Stack (state_id_t idc)
  (requires (fun h0 -> device_p_invariant h0 dvp))
  (ensures (fun h0 cnt h1 ->
    h1 == h0 /\
    cnt = device_p_g_get_states_counter h0 dvp))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_get_states_counter :
  #idc:idconfig ->
  device_p_get_states_counter_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_get_sessions_counter_st (idc : idconfig) =
  device_p_get_states_counter_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_get_sessions_counter :
  #idc:idconfig ->
  device_p_get_sessions_counter_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_get_peers_counter_st (idc : idconfig) =
  dvp:device_p idc ->
  Stack (peer_id_t idc)
  (requires (fun h0 -> device_p_invariant h0 dvp))
  (ensures (fun h0 cnt h1 ->
    h1 == h0 /\
    cnt = device_p_g_get_peers_counter h0 dvp))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_get_peers_counter :
  #idc:idconfig ->
  device_p_get_peers_counter_st idc

[@@ noextract_to "Kremlin"] noextract
let device_p_g_states_counter_is_saturated (#idc : idconfig) (h : mem) (dvp : device_p idc) :
  GTot bool =
  let dv_v = device_p_v h dvp in
  device_p_g_get_states_counter h dvp = state_id_max idc

[@@ noextract_to "Kremlin"] noextract
let device_p_g_sessions_counter_is_saturated #idc h dvp =
  device_p_g_states_counter_is_saturated #idc h dvp

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_states_counter_is_saturated_st (idc : idconfig) =
  dvp:device_p idc ->
  Stack bool
  (requires (fun h0 -> device_p_invariant h0 dvp))
  (ensures (fun h0 b h1 ->
    h1 == h0 /\
    b = device_p_g_states_counter_is_saturated h0 dvp))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_states_counter_is_saturated :
  #idc:idconfig ->
  device_p_states_counter_is_saturated_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_sessions_counter_is_saturated_st (idc : idconfig) =
  device_p_states_counter_is_saturated_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_sessions_counter_is_saturated :
  #idc:idconfig ->
  device_p_sessions_counter_is_saturated_st idc

[@@ noextract_to "Kremlin"] noextract
let device_p_g_peers_counter_is_saturated (#idc : idconfig) (h : mem) (dvp : device_p idc) :
  GTot bool =
  let dv_v = device_p_v h dvp in
  device_p_g_get_peers_counter h dvp = peer_id_max idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_peers_counter_is_saturated_st (idc : idconfig) =
  dvp:device_p idc ->
  Stack bool
  (requires (fun h0 -> device_p_invariant h0 dvp))
  (ensures (fun h0 b h1 ->
    h1 == h0 /\
    b = (device_p_g_peers_counter_is_saturated h0 dvp)))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_peers_counter_is_saturated :
  #idc:idconfig ->
  device_p_peers_counter_is_saturated_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_g_get_info (#idc : idconfig) (h : mem) (dvp : device_p idc) :
  GTot (idc_get_dc idc).dc_info =
  let dv_v = device_p_v h dvp in
  device_get_info dv_v

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_get_info_st (idc : idconfig) =
  // We copy the device information to out
  out:info_t idc ->
  dvp:device_p idc ->
  ST unit
  (requires (fun h0 ->
    info_invariant h0 out /\
    device_p_invariant h0 dvp /\
    B.(all_disjoint [info_footprint out; device_p_region_of dvp])))
  (ensures (fun h0 _ h1 ->
    B.(modifies (info_footprint out) h0 h1) /\
    (info_freeable h0 out ==> info_freeable h1 out) /\
    info_invariant h1 out /\
    info_v h1 out == device_p_g_get_info h0 dvp))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_get_info :
  #idc:idconfig ->
  device_p_get_info_st idc

[@@ noextract_to "Kremlin"] noextract
let device_p_g_get_static_v (#idc : idconfig) (h : mem) (dvp : device_p idc) :
  GTot (option (keypair (idc_get_config idc))) =
  let dv_v = device_p_v h dvp in
  device_get_static dv_v

// This signature may seem overly complicated, but it was designed to allow
// sharing keys with the sessions.
[@@ noextract_to "Kremlin"] noextract
val device_p_g_get_static (#idc : idconfig) (h : mem) (dv : device_p idc) :
  Ghost
    (private_key_t_or_unit (idc_get_nc idc) (device_has_s (idc_get_pattern idc)) &
     public_key_t_or_unit (idc_get_nc idc) (device_has_s (idc_get_pattern idc)))
  (requires True)
  (ensures (
    fun (spriv, spub) ->
    let kp_v = keys_t_or_unit_to_keypair h spriv spub in
    let kp'_v = device_p_g_get_static_v h dv in
    kp_v == kp'_v))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_get_static_priv_st (idc : idconfig{idc_uses_s idc}) =
  // We copy the device static to out
  out:private_key_t (idc_get_nc idc) ->
  dvp:device_p idc ->
  ST unit
  (requires (fun h0 ->
    live h0 out /\
    device_p_invariant h0 dvp /\
    B.all_disjoint [loc out; device_p_region_of dvp]))
  (ensures (fun h0 _ h1 ->
    B.modifies (loc out) h0 h1 /\
    Some? (device_p_g_get_static_v h0 dvp) /\
    as_seq h1 out == (Some?.v (device_p_g_get_static_v h0 dvp)).priv))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_get_static_priv :
  #idc:idconfig{idc_uses_s idc} ->
  device_p_get_static_priv_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_get_static_pub_st (idc : idconfig{idc_uses_s idc}) =
  // We copy the device static to out
  out:public_key_t (idc_get_nc idc) ->
  dvp:device_p idc ->
  Stack unit
  (requires (fun h0 ->
    live h0 out /\
    device_p_invariant h0 dvp /\
    B.all_disjoint [loc out; device_p_region_of dvp]))
  (ensures (fun h0 _ h1 ->
    B.modifies (loc out) h0 h1 /\
    Some? (device_p_g_get_static_v h0 dvp) /\
    as_seq h1 out == (Some?.v (device_p_g_get_static_v h0 dvp)).pub))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_get_static_pub :
  #idc:idconfig{idc_uses_s idc} ->
  device_p_get_static_pub_st idc

/// Extraction helpers which are used to define and extract functions only if they make sense
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_get_static_priv_st_or_unit (idc:idconfig) : Type0 =
  if idc_uses_s idc then device_p_get_static_priv_st idc else unit
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_device_p_get_static_priv_or_unit :
  #idc:idconfig ->
  device_p_get_static_priv_st_or_unit idc =
  fun #idc -> if idc_uses_s idc then mk_device_p_get_static_priv #idc else ()

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_get_static_pub_st_or_unit (idc:idconfig) : Type0 =
  if idc_uses_s idc then device_p_get_static_pub_st idc else unit
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_device_p_get_static_pub_or_unit :
  #idc:idconfig ->
  device_p_get_static_pub_st_or_unit idc =
  fun #idc -> if idc_uses_s idc then mk_device_p_get_static_pub #idc else ()


/// Three predicates describing how the device is modified after a peer has been
/// added or removed or after a state/session has been created. They are used to
/// communicate information to the user to reason about aliasing.
/// [device_p_only_changed_peers_or_counters] is implied (see lemma below) by
/// [device_p_no_removal] and [device_p_removed_peer], and is mostly used in
/// cases where we don't need precise information for the framing.
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_p_only_changed_peers_or_counters (#idc : idconfig) (dvp : device_p idc) (h0 h1 : mem) :
  GTot Type0

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_p_no_removal (#idc : idconfig) (dvp : device_p idc) (h0 h1 : mem) :
  GTot Type0

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_p_removed_peer
  (#idc : idconfig) (dvp : device_p idc) (pid : peer_id) (h0 h1 : mem) :
  GTot Type0

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_p_no_removal_implies_only_changed_peers_or_counters
  (#idc : idconfig) (dvp : device_p idc) (h0 h1 : mem) :
  Lemma (requires (device_p_no_removal dvp h0 h1))
  (ensures (device_p_only_changed_peers_or_counters dvp h0 h1))
  [SMTPat (device_p_no_removal dvp h0 h1)]

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val device_p_removed_peer_implies_only_changed_peers_or_counters
  (#idc : idconfig) (dvp : device_p idc) (pid : peer_id) (h0 h1 : mem) :
  Lemma (requires (device_p_removed_peer dvp pid h0 h1))
  (ensures (device_p_only_changed_peers_or_counters dvp h0 h1))
  [SMTPat (device_p_removed_peer dvp pid h0 h1)]

val device_p_frame_invariant :
     #idc:idconfig
  -> l:B.loc
  -> dv:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    device_p_invariant h0 dv /\
    B.loc_disjoint l (device_p_region_of dv) /\
    B.modifies l h0 h1))
  (ensures (
    device_p_invariant h1 dv /\
    device_p_v h0 dv == device_p_v h1 dv /\
    device_p_get_cstate h0 dv == device_p_get_cstate h1 dv /\
    device_p_no_removal dv h0 h1))
  [SMTPat (device_p_invariant h0 dv); SMTPat (B.modifies l h0 h1)]

val device_p_or_null_frame_invariant :
     #idc:idconfig
  -> l:B.loc
  -> dv:device_p_or_null idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    device_p_or_null_invariant h0 dv /\
    B.loc_disjoint l (device_p_or_null_region_of dv) /\
    B.modifies l h0 h1))
  (ensures (
    device_p_or_null_invariant h1 dv /\
    begin if device_p_g_is_null dv then True
    else
      device_p_v h0 dv == device_p_v h1 dv /\
      device_p_get_cstate h0 dv == device_p_get_cstate h1 dv /\
      device_p_no_removal dv h0 h1
    end))
  [SMTPat (device_p_or_null_invariant h0 dv); SMTPat (B.modifies l h0 h1)]

/// Additional lemmas and predicates for the peers
let peer_p_or_null_invariant
  (#idc : idconfig) (h : mem) (p : peer_p_or_null idc)
  (dvp : device_p idc) :
  GTot Type0 =
  peer_p_live h p /\
  device_p_invariant h dvp /\
  begin
  if peer_p_g_is_null p then True
  else
    begin
    peer_p_invariant h p /\
    device_p_owns_peer h dvp p
    end
  end

val device_p_no_removal_trans_lem :
     #idc:idconfig
  -> dv:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem
  -> h2:HS.mem ->
  Lemma
  (requires (
    device_p_no_removal dv h0 h1 /\
    device_p_no_removal dv h1 h2))
  (ensures (
    device_p_no_removal dv h0 h2))

/// The framing lemmas for the peers. There are 3 of them, for the following cases:
/// - a location disjoint from the peer's device is modified
/// - the peer's device is modified by adding a peer
/// - the peer's device is modified by removing a peer
val peer_p_or_null_frame_invariant :
     #idc:idconfig
  -> l:B.loc
  -> p:peer_p_or_null idc
  -> dvp:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    peer_p_or_null_invariant h0 p dvp /\
    B.loc_disjoint l (device_p_region_of dvp) /\
    B.modifies l h0 h1))
  (ensures (
    peer_p_or_null_invariant h1 p dvp /\
    peer_p_or_null_v h0 p == peer_p_or_null_v h1 p))
  [SMTPat (peer_p_or_null_invariant h0 p dvp);
   SMTPat (B.modifies l h0 h1)]

val peer_p_or_null_no_removal_frame_invariant :
     #idc:idconfig
  -> p:peer_p_or_null idc
  -> dvp:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    peer_p_or_null_invariant h0 p dvp /\
    device_p_no_removal dvp h0 h1))
  (ensures (
    peer_p_or_null_invariant h1 p dvp /\
    peer_p_or_null_v h0 p == peer_p_or_null_v h1 p))
  [SMTPat (peer_p_or_null_invariant h0 p dvp);
   SMTPat (device_p_no_removal dvp h0 h1)]

val peer_p_or_null_removed_peer_frame_invariant :
     #idc:idconfig
  -> pid:peer_id
  -> p:peer_p_or_null idc
  -> dvp:device_p idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    peer_p_or_null_invariant h0 p dvp /\
    device_p_removed_peer dvp pid h0 h1 /\
    peer_p_or_null_g_get_pid h0 p <> Some pid))
  (ensures (
    peer_p_or_null_invariant h1 p dvp /\
    peer_p_or_null_v h0 p == peer_p_or_null_v h1 p))
  [SMTPat (peer_p_or_null_invariant h0 p dvp);
   SMTPat (device_p_removed_peer dvp pid h0 h1)]

(**** Create/free device *)
#push-options "--ifuel 1"
[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_create_st (idc : idconfig) =
     r : HS.rid
  -> cstate : idc_get_cstate_s idc
  -> prlg_len : hashable_size_t (idc_get_nc idc)
  -> prlg : lbuffer uint8 prlg_len
  -> info : info_input_t idc
  -> sk : serialize_key_t idc
  -> spriv : private_key_t_or_unit (idc_get_nc idc) (idc_uses_s idc) ->  
  ST (device_p_or_null idc)
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    live h0 prlg /\ info_input_invariant h0 info /\
    lbuffer_or_unit_live h0 sk /\ lbuffer_or_unit_live h0 spriv /\
    get_dh_pre (idc_get_nc idc)))
  (ensures (fun h0 dvp h1 ->
    B.(modifies loc_none h0 h1) /\
    device_p_or_null_invariant h1 dvp /\
    begin
    let pattern = idc_get_pattern idc in
    let prlg_v = as_seq h0 prlg in
    let info_v = info_input_v h0 info in
    let sk_v = lbuffer_or_unit_to_opt_lseq h0 sk in
    let s_v = lbuffer_or_unit_to_opt_lseq h0 spriv in
    let opt_dv_v = Spec.create_device (idc_get_dc idc) pattern prlg_v info_v sk_v s_v in
    match opt_dv_v with
    | None -> device_p_g_is_null dvp
    | Some dv_v->
      not (device_p_g_is_null dvp) /\
      region_includes r (device_p_region_of dvp) /\
      device_p_get_cstate h1 dvp == cstate /\
      device_p_v h1 dvp == dv_v
    end))
#pop-options

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_create
  (#idc : idconfig)
  (csi:config_impls (idc_get_nc idc)) :
  device_p_create_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_create_from_secret_st (idc : idconfig{idc_get_serialize idc}) =
     r : HS.rid
  -> cstate : idc_get_cstate_s idc
  -> prlg_len : hashable_size_t (idc_get_nc idc)
  -> prlg : lbuffer uint8 prlg_len
  -> info : info_input_t idc
  -> sk : serialize_key_t idc
  -> spriv : enc_private_key_with_nonce_t idc ->  
  ST (device_p_or_null idc)
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    live h0 prlg /\ info_input_invariant h0 info /\
    lbuffer_or_unit_live h0 sk /\ lbuffer_or_unit_live h0 spriv /\
    // The caller function should always recall the entropy at the very
    // beginning, otherwise Z3 can't reason properly about it, and the
    // resulting proof obligations failures are very hard to understand.
    // This precondition enforces that the user has done that.
    B.live h0 (entropy_p <: B.buffer (G.erased entropy)) /\
    // Contrary to the simple "device_create" function, we need some disjointness
    // hypotheses to perform AEAD decryption
    B.all_disjoint [info_input_footprint info;
                    region_to_loc r;
                    lbuffer_or_unit_to_loc sk;
                    lbuffer_or_unit_to_loc spriv] /\
    // Hardware preconditions
    get_aead_pre (idc_get_nc idc) /\
    get_dh_pre (idc_get_nc idc)))
  (ensures (fun h0 dvp h1 ->
    B.(modifies (Lib.Buffer.loc entropy_p) h0 h1) /\
    device_p_or_null_invariant h1 dvp /\
    begin
    let pattern = idc_get_pattern idc in
    let prlg_v = as_seq h0 prlg in
    let info_v = info_input_v h0 info in
    let sk_v = lbuffer_or_unit_to_seq h0 sk in
    let s_v = lbuffer_or_unit_to_opt_lseq h0 spriv in
    let opt_dv_v = Spec.create_device_from_secret (idc_get_dc idc) pattern prlg_v info_v sk_v s_v in
    match opt_dv_v with
    | None -> device_p_g_is_null dvp
    | Some dv_v->
      not (device_p_g_is_null dvp) /\
      region_includes r (device_p_region_of dvp) /\
      device_p_get_cstate h1 dvp == cstate /\
      device_p_v h1 dvp == dv_v
    end))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_create_from_secret
  (#idc : idconfig{idc_get_serialize idc})
  (csi:config_impls (idc_get_nc idc)) :
  device_p_create_from_secret_st idc

/// Extraction helpers for the instanciation
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_create_from_secret_st_or_unit (idc:valid_idc) : Type0=
  if idc_get_serialize idc then device_p_create_from_secret_st idc else unit

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_device_p_create_from_secret_or_unit :
     #idc:valid_idc
  -> csi:config_impls (idc_get_nc idc)
  -> device_p_create_from_secret_st_or_unit idc =
  fun #idc csi ->
  if idc_get_serialize idc
  then mk_device_p_create_from_secret #idc csi else ()

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_free_st (idc : idconfig) =
  dvp : device_p idc ->
  ST unit
  (requires (fun h0 ->
    device_p_invariant h0 dvp))
  (ensures (fun h0 _ h1 ->
    B.(modifies (device_p_region_of dvp) h0 h1)))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_free :
  #idc : idconfig ->
  device_p_free_st idc


(**** Lookup *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_lookup_peer_by_id_st (idc:idconfig) =
     dv:device_p idc
  -> id:peer_id_opt_t idc ->
  Stack (peer_p_or_null idc)
  (requires (fun h0 ->
    device_p_invariant h0 dv))
  (ensures (fun h0 p h1 ->
    B.(modifies loc_none h0 h1) /\
    peer_p_or_null_invariant h1 p dv /\
    device_p_invariant h1 dv /\ // Not necessary but helps the proofs
    device_p_v h1 dv == device_p_v h0 dv /\ // Not necessary but helps the proofs
    begin
    let id_v = peer_id_opt_v id in
    if None? id_v then peer_p_g_is_null p else
    let r_v = Spec.lookup_peer_by_id (device_p_v h0 dv) (peer_id_v #idc id) in
    if peer_p_g_is_null p then r_v == None
    else
      Some? r_v /\ peer_p_v h1 p == Some?.v r_v /\
      peer_p_g_get_id h1 p == peer_id_v #idc id
    end))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_lookup_peer_by_id :
     #idc:idconfig
  -> device_p_lookup_peer_by_id_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_lookup_peer_by_static_st (idc : idconfig{normalize_term #bool (idc_peers_have_s idc)}) =
     dv:device_p idc
  -> s:public_key_t (idc_get_nc idc) ->
  Stack (peer_p_or_null idc)
  (requires (fun h0 ->
    device_p_invariant h0 dv /\
    live h0 s))
  (ensures (fun h0 p h1 ->
    B.(modifies loc_none h0 h1) /\
    peer_p_or_null_invariant h1 p dv /\
    device_p_invariant h1 dv /\ // Not necessary but helps the proofs
    device_p_v h1 dv == device_p_v h0 dv /\ // Not necessary but helps the proofs
    begin
    let r_v = Spec.lookup_peer_by_static (device_p_v h0 dv) (as_seq h0 s) in
    if peer_p_g_is_null p then r_v == None
    else Some? r_v /\ peer_p_v h1 p == Some?.v r_v
    end))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_lookup_peer_by_static :
     #idc:idconfig{normalize_term #bool (idc_peers_have_s idc)}
  -> device_p_lookup_peer_by_static_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_lookup_peer_by_static_st_or_unit (idc : valid_idc) : Type0 =
  if idc_peers_have_s idc then device_p_lookup_peer_by_static_st idc else unit
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_device_p_lookup_peer_by_static_or_unit :
  #idc:valid_idc ->
  device_p_lookup_peer_by_static_st_or_unit idc =
  fun #idc -> if idc_peers_have_s idc then mk_device_p_lookup_peer_by_static #idc else ()

(**** Add/remove peer *)

// We use an optional peer id on purpose: the end-user, not working in F*,
// might accidentally use 0 as a peer id (a valid peer id is > 0).

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_add_peer_get_st_pre (#idc : valid_idc) :
     dv:device_p idc
  -> pinfo:info_input_t idc
  -> rs:idc_rs_t idc
  -> psk:idc_psk_t idc
  -> h0:mem -> GTot Type0 =
  fun dv pinfo rs psk h0 ->
  device_p_invariant h0 dv /\
  info_input_invariant h0 pinfo /\
  lbuffer_or_unit_live h0 rs /\
  lbuffer_or_unit_live h0 psk

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_add_peer_get_st_post (#idc : valid_idc) :
     dv:device_p idc
  -> pinfo:info_input_t idc
  -> rs:idc_rs_t idc
  -> psk:idc_psk_t idc
  -> h0:mem
  -> p:peer_p_or_null idc
  -> h1:mem -> GTot Type0 =
  fun dv pinfo rs psk h0 p h1 ->
  B.(modifies (device_p_region_of dv) h0 h1) /\
  device_p_invariant h1 dv /\
  device_p_get_cstate h1 dv == device_p_get_cstate h0 dv /\
  device_p_g_get_static h1 dv == device_p_g_get_static h0 dv /\
  device_p_no_removal dv h0 h1 /\
  peer_p_or_null_invariant h1 p dv /\
  begin
  let pinfo_v = info_input_v h0 pinfo in
  let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
  let psk_v = lbuffer_or_unit_to_opt_lseq h0 psk in
  let dv0_v = device_p_v h0 dv in
  let dv1_v = device_p_v h1 dv in
  let r_v = Spec.add_peer_get dv0_v pinfo_v rs_v psk_v in
  if not (peer_p_g_is_null p) then
    Some? r_v /\
    begin
    let Some (p_v, dv1'_v) = r_v in
    not (peer_p_g_is_null p) /\
    peer_p_v h1 p == p_v /\
    dv1_v == dv1'_v /\
    // This is mostly to help with the aliasing
    device_p_g_get_peers_counter_v h1 dv = device_p_g_get_peers_counter_v h0 dv + 1 /\
    peer_p_g_get_id h1 p = device_p_g_get_peers_counter_v h0 dv
    end
  else
    (* Couldn't add the peer: nothing changed. Note that this does not
     * strictly correspond to the spec: in the implementation we have to
     * take into account the counter saturation, which is why we can't
     * match the errors *)
    dv1_v == dv0_v
  end

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_add_peer_get_st (idc : valid_idc) =
     dv:device_p idc
  -> pinfo:info_input_t idc
  -> rs:idc_rs_t idc
  -> psk:idc_psk_t idc ->
  ST (peer_p_or_null idc)
  (requires (fun h0 -> device_p_add_peer_get_st_pre dv pinfo rs psk h0))
  (ensures (fun h0 p h1 -> device_p_add_peer_get_st_post dv pinfo rs psk h0 p h1))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_add_peer_get :
     #idc:valid_idc
  -> device_p_add_peer_get_st idc

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_add_peer_st_pre (#idc : valid_idc) :
     dv:device_p idc
  -> pinfo:info_input_t idc
  -> rs:idc_rs_t idc
  -> psk:idc_psk_t idc
  -> h0:mem -> GTot Type0 =
  fun dv pinfo rs psk h0 ->
  device_p_add_peer_get_st_pre dv pinfo rs psk h0

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_add_peer_st_post (#idc : valid_idc) :
     dv:device_p idc
  -> pinfo:info_input_t idc
  -> rs:idc_rs_t idc
  -> psk:idc_psk_t idc
  -> h0:mem
  -> pid:peer_id_opt_t idc
  -> h1:mem -> GTot Type0 =
  fun dv pinfo rs psk h0 pid h1 ->
  B.(modifies (device_p_region_of dv) h0 h1) /\
  device_p_invariant h1 dv /\
  device_p_get_cstate h1 dv == device_p_get_cstate h0 dv /\
  device_p_g_get_static h1 dv == device_p_g_get_static h0 dv /\
  device_p_no_removal dv h0 h1 /\
  begin
  let pinfo_v = info_input_v h0 pinfo in
  let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
  let psk_v = lbuffer_or_unit_to_opt_lseq h0 psk in
  let dv0_v = device_p_v h0 dv in
  let dv1_v = device_p_v h1 dv in
  let r_v = Spec.add_peer dv0_v pinfo_v rs_v psk_v in
  let opt_pid_v = peer_id_opt_v pid in
  match opt_pid_v, r_v with
  | Some pid_v, Some (pid_v', dv1'_v) ->
    pid_v == pid_v' /\
    dv1_v == dv1'_v /\
    // This is mostly to help with the aliasing
    device_p_g_get_peers_counter_v h1 dv = device_p_g_get_peers_counter_v h0 dv + 1 /\
    pid_v = device_p_g_get_peers_counter_v h0 dv
  | None, _ ->
    (* Couldn't add the peer: nothing changed. Note that this does not
     * strictly correspond to the spec: in the implementation we have to
     * take into account the counter saturation, which is why we can't
     * match the errors *)
    dv1_v == dv0_v
  | _ -> False
  end

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_add_peer_st (idc : valid_idc) =
     dv:device_p idc
  -> pinfo:info_input_t idc
  -> rs:idc_rs_t idc
  -> psk:idc_psk_t idc ->
  ST (peer_id_opt_t idc)
  (requires (fun h0 -> device_p_add_peer_st_pre dv pinfo rs psk h0))
  (ensures (fun h0 p h1 -> device_p_add_peer_st_post dv pinfo rs psk h0 p h1))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_add_peer :
     #idc:valid_idc
  -> device_p_add_peer_st idc

// We use an optional peer id on purpose: the end-user, not working in F*,
// might accidentally use 0 as a peer id (a valid peer id is > 0).
[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_remove_peer_st (idc : valid_idc) =
     dv:device_p idc
  -> pid:peer_id_opt_t idc ->
  ST unit
  (requires (fun h0 ->
    device_p_invariant h0 dv))
  (ensures (fun h0 b h1 ->
    B.(modifies (device_p_region_of dv) h0 h1) /\
    device_p_invariant h1 dv /\
    device_p_get_cstate h1 dv == device_p_get_cstate h0 dv /\
    begin
    let dv0_v = device_p_v h0 dv in
    let dv1_v = device_p_v h1 dv in
    match peer_id_opt_v pid with
    | Some pid ->
      dv1_v == remove_peer dv0_v pid /\
      device_p_removed_peer dv pid h0 h1
    | None -> dv1_v == dv0_v /\ device_p_no_removal dv h0 h1
    end))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_remove_peer :
  #idc:valid_idc ->
  device_p_remove_peer_st idc

(**** Serialization/deserialization *)
(***** Device serialization *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_serialize_device_secret_st (idc : valid_idc{idc_get_serialize idc /\ idc_uses_s idc}) =
     r:HS.rid
  -> outlen:B.pointer size_t
  -> out:B.pointer (B.buffer uint8)
  -> dvp:device_p idc ->
  ST unit
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    B.live h0 outlen /\ B.live h0 out /\
    device_p_invariant h0 dvp /\
    B.all_disjoint [B.loc_buffer outlen;
                    B.loc_buffer out;
                    Lib.Buffer.loc entropy_p;
                    device_p_region_of dvp;
                    region_to_loc r] /\
    // As usual, forcing the user to recall the entropy in the caller function
    B.live h0 (entropy_p <: B.buffer (G.erased entropy)) /\
    // Hardware preconditions
    get_aead_pre (idc_get_nc idc)))
  (ensures (fun h0 () h1 ->
    B.(modifies (loc_union (loc_union (loc_buffer outlen) (loc_buffer out))
                (Lib.Buffer.loc entropy_p)) h0 h1) /\
    begin
    let dv_v = device_p_v h0 dvp in
    let entr0 = B.deref h0 (entropy_p <: B.buffer (G.erased entropy)) in
    match Spec.serialize_device_secret dv_v entr0 with
    | None, _ -> False
    | Some enc_key, entr1 ->
      let out1 = B.deref h1 out in
      let outlen1_v = size_v (B.deref h1 outlen) in
      B.length out1 = outlen1_v /\
      B.as_seq h1 out1 == enc_key /\
      G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr1 /\
      B.live h1 out1 /\
      buffer_or_null_freeable out1 /\
      region_includes r (buffer_or_null_loc_addr out1)
    end))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_serialize_device_secret :
  #idc:valid_idc{idc_get_serialize idc /\ idc_uses_s idc} ->
  csi:config_impls (idc_get_nc idc) ->
  device_p_serialize_device_secret_st idc

/// Extraction helpers for the instanciation
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_serialize_device_secret_st_or_unit (idc:valid_idc) : Type0=
  if idc_get_serialize idc && idc_uses_s idc
  then device_p_serialize_device_secret_st idc else unit
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_device_p_serialize_device_secret_or_unit :
     #idc:valid_idc
  -> csi:config_impls (idc_get_nc idc)
  -> device_p_serialize_device_secret_st_or_unit idc =
  fun #idc csi ->
  if idc_get_serialize idc && idc_uses_s idc
  then mk_device_p_serialize_device_secret #idc csi else ()

(***** Peer serialization *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_serialize_peer_secret_st (idc : valid_idc) =
     r:HS.rid
  -> outlen:B.pointer size_t
  -> out:B.pointer (B.buffer uint8)
  -> dvp:device_p idc
  -> peer:peer_p_or_null idc -> // The user may have forgotten to check if the peer is null
  ST unit
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    B.live h0 outlen /\ B.live h0 out /\
    device_p_invariant h0 dvp /\
    peer_p_live h0 peer /\
    // The peer should be part of the device, but actually nothing prevents
    // a user from mixing peers and devices, and preventing this
    // behaviour should be done elsewhere
    // So at this point we need pretty involved disjointness conditions.
    (device_p_owns_peer h0 dvp peer \/
     B.loc_disjoint (device_p_region_of dvp) (peer_p_or_null_footprint peer)) /\
    B.all_disjoint [B.loc_buffer outlen;
                    B.loc_buffer out;
                    Lib.Buffer.loc entropy_p;
                    (B.loc_union (device_p_region_of dvp) (peer_p_or_null_footprint peer));
                    region_to_loc r] /\
    // As usual, forcing the user to recall the entropy in the caller function
    B.live h0 (entropy_p <: B.buffer (G.erased entropy)) /\
    // Hardware preconditions
    get_aead_pre (idc_get_nc idc)))
  (ensures (fun h0 () h1 ->
    B.(modifies (loc_union (loc_union (loc_buffer outlen) (loc_buffer out))
                (Lib.Buffer.loc entropy_p)) h0 h1) /\
    begin
    let entr0 = B.deref h0 (entropy_p <: B.buffer (G.erased entropy)) in
    if peer_p_g_is_null peer then
      begin
      B.g_is_null (B.deref h1 out) /\
      size_v (B.deref h1 outlen) = 0 /\
      G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == G.reveal entr0
      end
    else
      let dv_v = device_p_v h0 dvp in
      let p_v = peer_p_v h0 peer in
      match Spec.serialize_peer_secret dv_v p_v entr0 with
      | None, _ -> False
      | Some enc_keys, entr1 ->
        let out1 = B.deref h1 out in
        let outlen1_v = size_v (B.deref h1 outlen) in
        B.length out1 = outlen1_v /\
        B.as_seq h1 out1 == enc_keys /\
        G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr1 /\
        B.live h1 out1 /\
        buffer_or_null_freeable out1 /\
        region_includes r (buffer_or_null_loc_addr out1)
    end))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_serialize_peer_secret :
  #idc:valid_idc{idc_get_serialize idc /\ (idc_is_psk idc || idc_peers_have_s idc)} ->
  csi:config_impls (idc_get_nc idc) ->
  device_p_serialize_peer_secret_st idc

/// Extraction helpers for the instanciation
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_serialize_peer_secret_st_or_unit (idc:valid_idc) : Type0=
  if idc_get_serialize idc && (idc_is_psk idc || idc_peers_have_s idc)
  then device_p_serialize_peer_secret_st idc else unit

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_device_p_serialize_peer_secret_or_unit :
     #idc:valid_idc
  -> csi:config_impls (idc_get_nc idc)
  -> device_p_serialize_peer_secret_st_or_unit idc =
  fun #idc csi ->
  if idc_get_serialize idc && (idc_is_psk idc || idc_peers_have_s idc)
  then mk_device_p_serialize_peer_secret #idc csi else ()

[@@ noextract_to "Kremlin"] inline_for_extraction noextract unfold
type device_p_deserialize_peer_secret_st (idc : valid_idc) =
     // We need this one to allocate a buffer in which to decrypt the keys
     // TODO: remove it and use a sub-region in the device.
     // Another possibility would be to allocate this buffer on the stack.
     r:HS.rid
  -> dv:device_p idc
  -> peer_name:info_input_t idc
  -> inlen:size_t
  -> enc_keys:lbuffer uint8 inlen ->
  ST (peer_p_or_null idc)
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    device_p_invariant h0 dv /\
    info_input_invariant h0 peer_name /\
    live h0 enc_keys /\
    B.all_disjoint [region_to_loc r;
                    device_p_region_of dv;
                    info_input_footprint peer_name;
                    loc enc_keys] /\
    // Hardware preconditions
    get_aead_pre (idc_get_nc idc)))
  (ensures (fun h0 p h1 ->
    B.(modifies (device_p_region_of dv) h0 h1) /\
    device_p_invariant h1 dv /\
    device_p_get_cstate h1 dv == device_p_get_cstate h0 dv /\
    device_p_g_get_static h1 dv == device_p_g_get_static h0 dv /\
    device_p_no_removal dv h0 h1 /\
    peer_p_or_null_invariant h1 p dv /\
    begin
    let pname_v = info_input_v h0 peer_name in
    let enc_keys_v = as_seq h0 enc_keys in
    let dv0_v = device_p_v h0 dv in
    let dv1_v = device_p_v h1 dv in
    let r_v = Spec.deserialize_peer_secret dv0_v pname_v (idc_peers_have_s idc) (idc_is_psk idc) enc_keys_v in
    if not (peer_p_g_is_null p) then
      Some? r_v /\
      begin
      let Some (p_v, dv1'_v) = r_v in
      not (peer_p_g_is_null p) /\
      peer_p_v h1 p == p_v /\
      dv1_v == dv1'_v /\
      // This is mostly to help with the aliasing
      device_p_g_get_peers_counter_v h1 dv = device_p_g_get_peers_counter_v h0 dv + 1 /\
      peer_p_g_get_id h1 p = device_p_g_get_peers_counter_v h0 dv
      end
    else
      (* Couldn't add the peer: nothing changed. Note that this does not
       * strictly correspond to the spec: in the implementation we have to
       * take into account the counter saturation, which is why we can't
       * match the errors *)
      dv1_v == dv0_v
    end))

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val mk_device_p_deserialize_peer_secret :
  #idc:valid_idc{idc_get_serialize idc /\ (idc_is_psk idc || idc_peers_have_s idc)} ->
  csi:config_impls (idc_get_nc idc) ->
  device_p_deserialize_peer_secret_st idc

/// Extraction helpers for the instanciation
[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let device_p_deserialize_peer_secret_st_or_unit (idc:valid_idc) : Type0=
  if idc_get_serialize idc && (idc_is_psk idc || idc_peers_have_s idc)
  then device_p_deserialize_peer_secret_st idc else unit

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
let mk_device_p_deserialize_peer_secret_or_unit :
     #idc:valid_idc
  -> csi:config_impls (idc_get_nc idc)
  -> device_p_deserialize_peer_secret_st_or_unit idc =
  fun #idc csi ->
  if idc_get_serialize idc && (idc_is_psk idc || idc_peers_have_s idc)
  then mk_device_p_deserialize_peer_secret #idc csi else ()

