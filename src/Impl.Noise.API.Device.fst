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
open Spec.Noise.API.State.Definitions
friend Spec.Noise.API.State.Definitions
open Spec.Noise.API.State
module M = Spec.Noise.Map
module Spec = Spec.Noise.API.Device.Definitions
friend Spec.Noise.API.Device.Definitions
open Spec.Noise.API.Device.Lemmas
friend Spec.Noise.API.Device.Lemmas

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

module LL = Impl.Noise.LinkedList
module St = Impl.Noise.Stateful
module M = Spec.Noise.Map

open Lib.Memzero0

open Lib.RandomSequence
open Lib.RandomBuffer.System

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

let _align_fsti = ()

(*** Type definitions *)

/// Peers - we start with "raw" peers, which take various parameters, then lift
/// them to "peers" which only take a configuration as parameter.

/// This is not the same as peer information. Peer information is user meta-data stored
/// with a peer (like its name). [raw_peer_t] is a a peer stored in a device
/// (user meta-data but also keys...).
[@CAbstractStruct]
noeq type raw_peer_t_raw t0 t1 t2 t3 = {
  p_id: t0;
  p_info : t1;
  p_s : t2;
  p_psk : t3;
}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type raw_peer_t
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : stateful_peer_info) (has_s has_psk : bool) =
  raw_peer_t_raw 
                 (id_cl_t peer_id) (peer_info.St.s ())
                 (public_key_t_or_unit nc has_s)
                 (preshared_key_t_or_unit has_psk)

/// Adding pointer indirection and abstraction
noeq type raw_peer_p_or_null_raw
  (t : Type0) = {
  pp : B.pointer_or_null t;
  pp_r : HS.rid; // Parent region: used to make the footprint independent from the memory snapshot
}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type raw_peer_p_or_null
  (nc : iconfig)
  (peer_id : id_cl)
  (peer_info : stateful_peer_info)
  (has_s has_psk : bool) =
  raw_peer_p_or_null_raw (raw_peer_t nc peer_id peer_info has_s has_psk)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type raw_peer_p (nc : iconfig) (peer_id : id_cl)
                (peer_info : stateful_peer_info) (has_s has_psk : bool) =
  pp:raw_peer_p_or_null nc peer_id peer_info has_s has_psk{not (B.g_is_null pp.pp)}

[@@ noextract_to "Karamel"] noextract
let raw_peer_s (nc : iconfig) (pinfo_ty : Type0) = raw_peer (get_config nc) pinfo_ty

let raw_peer_t_v (#nc : iconfig) (#peer_id : id_cl)
                 (#peer_info : stateful_peer_info) (#has_s #has_psk : bool)
                 (h : mem)
                 (p : raw_peer_t nc peer_id peer_info has_s has_psk) :
  GTot (raw_peer_s nc (peer_info.St.t ())) =
  let s = if has_s then Some (lbuffer_or_unit_to_seq h p.p_s) else None in
  let psk = if has_psk then Some (lbuffer_or_unit_to_seq h p.p_psk) else None in
  let info = peer_info.St.v () h p.p_info in
  {
    Spec.p_id = peer_id.id_v p.p_id;
    Spec.p_info = info;
    Spec.p_s = s;
    Spec.p_psk = psk;
  }

let raw_peer_p_v (#nc : iconfig) (#peer_id : id_cl)
                 (#peer_info : stateful_peer_info) (#has_s #has_psk : bool)
                 (h : mem)
                 (p : raw_peer_p nc peer_id peer_info has_s has_psk) :
  GTot (raw_peer_s nc (peer_info.St.t ())) =
  let p = B.deref h p.pp in
  raw_peer_t_v h p

let raw_peer_t_get_pid
  (#nc : iconfig) (#peer_id : id_cl)
  (#peer_info : stateful_peer_info) (#has_s #has_psk : bool)
  (p : raw_peer_t nc peer_id peer_info has_s has_psk) :
  GTot Spec.peer_id =
  peer_id.id_v p.p_id

let raw_peer_p_g_get_id
  (#nc : iconfig) (#peer_id : id_cl)
  (#peer_info : stateful_peer_info) (#has_s #has_psk : bool)
  (h : mem)
  (p : raw_peer_p nc peer_id peer_info has_s has_psk) :
  GTot Spec.peer_id =
  let p = B.deref h p.pp in
  raw_peer_t_get_pid p

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let raw_stateful_peer_t_prim
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : stateful_peer_info) (has_s has_psk : bool) : St.stateful unit =
St.Stateful
  (* s *)
  (fun _ -> raw_peer_t nc peer_id peer_info has_s has_psk)
  
  (* footprint *)
  (fun #_ p ->
    B.loc_union (peer_info.St.footprint p.p_info)
    (B.loc_union (lbuffer_or_unit_to_loc p.p_s)
                 (lbuffer_or_unit_to_loc p.p_psk)))

  (* freeable *)
  (fun #_ h p ->
    peer_info.St.freeable h p.p_info /\
    lbuffer_or_unit_freeable p.p_s /\
    lbuffer_or_unit_freeable p.p_psk)

  (* invariant *)
  (fun #_ h p ->
    B.live h (lbuffer_or_unit_to_buffer p.p_s) /\
    B.live h (lbuffer_or_unit_to_buffer p.p_psk) /\
    peer_info.St.invariant h p.p_info /\
    begin
    let s_loc = lbuffer_or_unit_to_loc p.p_s in
    let psk_loc = lbuffer_or_unit_to_loc p.p_psk in
    let pinfo_loc = peer_info.St.footprint p.p_info in
    B.all_disjoint [s_loc; psk_loc; pinfo_loc]
    end)

  (fun _ -> raw_peer_s nc (peer_info.St.t ()))  (* t *)
  (fun _ h p -> raw_peer_t_v h p) (* v *)

  (* frame_invariant *)
  (fun #_ l p h0 h1 -> peer_info.St.frame_invariant l p.p_info h0 h1)
  
  (* frame_freeable *)
  (fun #_ l p h0 h1 -> peer_info.St.frame_freeable l p.p_info h0 h1)

/// This stateful class is used as input to the peers list push function.
/// We use it to relax the disjointness hypotheses and to use the input
/// stateful class of the peer information. In practice, it allows us
/// to use strings as input, rather than pointers to strings.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let raw_stateful_peer_t_input_prim
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : stateful_peer_info) (has_s has_psk : bool) : St.stateful unit =
St.Stateful
  (* s *)
  (fun _ -> raw_peer_t nc peer_id peer_info has_s has_psk)
  
  (* footprint *)
  (fun #_ p ->
    B.loc_union (peer_info.St.footprint p.p_info)
    (B.loc_union (lbuffer_or_unit_to_loc p.p_s)
                 (lbuffer_or_unit_to_loc p.p_psk)))

  (* freeable *)
  (fun #_ h p -> False) // We never use that

  (* invariant *)
  (fun #_ h p ->
    // No disjointness hypotheses
    B.live h (lbuffer_or_unit_to_buffer p.p_s) /\
    B.live h (lbuffer_or_unit_to_buffer p.p_psk) /\
    peer_info.St.invariant h p.p_info)

  (fun _ -> raw_peer_s nc (peer_info.St.t ()))  (* t *)
  (fun _ h p -> raw_peer_t_v h p) (* v *)

  (* frame_invariant *)
  (fun #_ l p h0 h1 -> peer_info.St.frame_invariant l p.p_info h0 h1)
  
  (* frame_freeable *)
  (fun #_ l p h0 h1 -> ())

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let raw_stateful_peer_p_prim
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : stateful_peer_info) (has_s has_psk : bool) : St.stateful unit =
St.Stateful
  (* s *)
  (fun _ -> raw_peer_p nc peer_id peer_info has_s has_psk)
  
  (* footprint *)
  (fun #_ pp -> region_to_loc pp.pp_r)

  (* freeable *)
  (fun #_ h pp ->
    let p = B.deref h pp.pp in
    (raw_stateful_peer_t_prim nc peer_id peer_info has_s has_psk).St.freeable h p /\
    B.freeable pp.pp)

  (* invariant *)
  (fun #_ h pp ->
    let p = B.deref h pp.pp in
    let peer_t_st = raw_stateful_peer_t_prim nc peer_id peer_info has_s has_psk in
    let ptr_loc = B.loc_addr_of_buffer pp.pp in
    let p_loc = peer_t_st.St.footprint p in

    peer_t_st.St.invariant h p /\

    ST.is_eternal_region pp.pp_r /\

    B.live h pp.pp /\

    region_includes pp.pp_r p_loc /\
    region_includes pp.pp_r (B.loc_addr_of_buffer pp.pp) /\
    
    B.live h (lbuffer_or_unit_to_buffer p.p_s) /\
    B.live h (lbuffer_or_unit_to_buffer p.p_psk) /\
    peer_info.St.invariant h p.p_info /\
    B.all_disjoint [ptr_loc; p_loc])

  (fun _ -> raw_peer_s nc (peer_info.St.t ()))  (* t *)
  (fun _ h pp -> let p = B.deref h pp.pp in raw_peer_t_v h p) (* v *)

  (* frame_invariant *)
  (fun #_ l pp h0 h1 ->
    let p = B.deref h0 pp.pp in
    let peer_t_st = raw_stateful_peer_t_prim nc peer_id peer_info has_s has_psk in
    peer_t_st.St.frame_invariant l p h0 h1)
  
  (* frame_freeable *)
  (fun #_ l pp h0 h1 ->
    let p = B.deref h0 pp.pp in
    let p = B.deref h0 pp.pp in
    let peer_t_st = raw_stateful_peer_t_prim nc peer_id peer_info has_s has_psk in
    peer_t_st.St.frame_freeable l p h0 h1)

// Controling unfolding for type inference
[@@ (strict_on_arguments [0;1;2]); noextract_to "Karamel"]
inline_for_extraction noextract
val raw_stateful_peer_t
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : St.stateful_malloc_from_input_clone_copy unit) (has_s has_psk : bool) :
  St.stateful_clone unit

let raw_stateful_peer_t nc peer_id peer_info has_s has_psk =
St.Stateful_clone

  (raw_stateful_peer_t_prim nc peer_id peer_info.St.smficc_stateful has_s has_psk)

  (* clone *)
  (fun #_ r x ->
    (**) let h0 = ST.get () in
    (**) let r_buffers = ST.new_region r in
    (**) let r_pinfo = ST.new_region r in
    let s = lbuffer_or_unit_malloc r_buffers (u8 0) in
    let psk = lbuffer_or_unit_malloc r_buffers (u8 0) in
    lbuffer_or_unit_copy s x.p_s;
    lbuffer_or_unit_copy psk x.p_psk;
    (**) let h1 = ST.get () in
    (**) peer_info.St.smficc_stateful.St.frame_invariant B.loc_none x.p_info h0 h1;
    let pinfo = peer_info.St.smficc_clone r_pinfo x.p_info in
    (**) let h2 = ST.get () in
    begin
    (**) assert(region_includes_region r r_buffers);
    (**) assert(region_includes_region r r_pinfo);
    (**) assert(region_includes r (lbuffer_or_unit_to_loc s));
    (**) assert(region_includes r (lbuffer_or_unit_to_loc psk));
    (**) assert(region_includes r (peer_info.St.smficc_stateful.St.footprint pinfo))
    end;
    [@inline_let] let res =
    ({
      p_id = x.p_id;
      p_info = pinfo;
      p_s = s;
      p_psk = psk;
    }) in
    res)

  (* free *)
  (fun _ p ->
    peer_info.St.smficc_free () p.p_info;
    (* Don't leave sensitive information on the heap - note that in the case of
     * the peer name, the sensitive information should be erased by the [free]
     * function *)
    if has_s then
      Lib.Memzero0.memzero (lbuffer_or_unit_to_buffer p.p_s) (public_key_vs nc);
    if has_psk then
      Lib.Memzero0.memzero (lbuffer_or_unit_to_buffer p.p_psk) preshared_key_vs;
    (* Free *)
    lbuffer_or_unit_free p.p_s;
    lbuffer_or_unit_free p.p_psk)

// Malloc a peer_t from a peer_t_input (note that the latter one has a weaker
// invariant and a different type for the peer information).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val raw_stateful_peer_t_prim_malloc_from_input
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : St.stateful_malloc_from_input_clone_copy unit) (has_s has_psk : bool) :
  St.malloc_from_input_st
    (raw_stateful_peer_t_input_prim nc peer_id peer_info.St.smficc_input
                                 has_s has_psk)
    (raw_stateful_peer_t_prim nc peer_id peer_info.St.smficc_stateful
                                 has_s has_psk)

let raw_stateful_peer_t_prim_malloc_from_input nc peer_id peer_info has_s has_psk () r input =
  (**) let h0 = ST.get () in
  (**) let r_buffers = ST.new_region r in
  (**) let r_pinfo = ST.new_region r in
  [@inline_let]
  let Mkraw_peer_t_raw id pinfo0 rs0 psk0 = input in
  let rs = lbuffer_or_unit_malloc r_buffers (u8 0) in
  let psk = lbuffer_or_unit_malloc r_buffers (u8 0) in
  lbuffer_or_unit_copy rs rs0;
  lbuffer_or_unit_copy psk psk0;
  (**) let h1 = ST.get () in
  (**) peer_info.St.smficc_input.St.frame_invariant B.loc_none pinfo0 h0 h1;
  let pinfo = peer_info.St.smficc_malloc_from_input () r_pinfo pinfo0 in
  (**) let h2 = ST.get () in
  begin
  (**) assert(region_includes_region r r_buffers);
  (**) assert(region_includes_region r r_pinfo);
  (**) assert(region_includes r (lbuffer_or_unit_to_loc rs));
  (**) assert(region_includes r (lbuffer_or_unit_to_loc psk));
  (**) assert(region_includes r (peer_info.St.smficc_stateful.St.footprint pinfo))
  end;
  [@inline_let] let res =
  ({
    p_id = id;
    p_info = pinfo;
    p_s = rs;
    p_psk = psk;
  }) in
  res

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let raw_stateful_peer_p_malloc_from_input
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : St.stateful_malloc_from_input_clone_copy unit) (has_s has_psk : bool) :
  St.malloc_from_input_st
    (raw_stateful_peer_t_input_prim nc peer_id peer_info.St.smficc_input has_s has_psk)
    (raw_stateful_peer_p_prim nc peer_id peer_info.St.smficc_stateful has_s has_psk) =
  fun i r x ->
  (**) let h0 = ST.get () in
  (**) let r_parent = new_region r in
  (**) let r_peer = new_region r_parent in
  (**) let r_ptr = new_region r_parent in
  (**) let h1 = ST.get () in
  [@inline_let]
  let peer_input_t_st = raw_stateful_peer_t_input_prim nc peer_id peer_info.St.smficc_input has_s has_psk in
  [@inline_let]
  let peer_p_prim_st =
    raw_stateful_peer_p_prim nc peer_id peer_info.St.smficc_stateful has_s has_psk in
  (**) peer_input_t_st.St.frame_invariant B.loc_none x h0 h1;
  let x' = raw_stateful_peer_t_prim_malloc_from_input nc peer_id peer_info has_s has_psk () r_peer x in
  (**) let h2 = ST.get () in
  let xp' = B.malloc r_ptr x' 1ul in
  (**) let h3 = ST.get () in
  [@inline_let] let pp =
  {
    pp = xp';
    pp_r = r_parent;
  } in
  [@inline_let]
  let peer_t_st = raw_stateful_peer_t_prim nc peer_id peer_info.St.smficc_stateful has_s has_psk in
  (**) B.(modifies_only_not_unused_in loc_none h0 h3);
  (**) B.(modifies_only_not_unused_in loc_none h2 h3);
  (**) peer_t_st.St.frame_invariant B.loc_none x' h2 h3;
  (**) peer_t_st.St.frame_freeable B.loc_none x' h2 h3;
  (**) assert(region_includes pp.pp_r (B.loc_addr_of_buffer pp.pp));
  (**) assert(peer_t_st.St.invariant h3 x');
  (**) assert(peer_p_prim_st.St.invariant h3 pp);
  (**) assert(peer_p_prim_st.St.freeable h3 pp);
  pp

// Controling unfolding for type inference
[@@ (strict_on_arguments [0; 1; 2]); noextract_to "Karamel"]
inline_for_extraction noextract
val raw_stateful_peer_p
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : St.stateful_malloc_from_input_clone_copy unit) (has_s has_psk : bool) :
  LL.stateful unit

let raw_stateful_peer_p nc peer_id peer_info has_s has_psk =

  St.Stateful_malloc_from_input

  // Stateful input
  (raw_stateful_peer_t_input_prim nc peer_id peer_info.St.smficc_input has_s has_psk)

  // Stateful
  (raw_stateful_peer_p_prim nc peer_id peer_info.St.smficc_stateful has_s has_psk)

  (* malloc from input *)
  (raw_stateful_peer_p_malloc_from_input nc peer_id peer_info has_s has_psk)

  (* free *)
  (fun _ pp ->
    (**) let h0 = ST.get () in
    let p = B.index pp.pp 0ul in
    (**) let h1 = ST.get () in
    [@inline_let]
    let peer_t_st = raw_stateful_peer_t nc peer_id peer_info has_s has_psk in    
    (**) peer_t_st.St.sc_stateful.St.frame_invariant B.loc_none p h0 h1;
    peer_t_st.St.sc_free () p;
    B.free pp.pp)

/// Functor which transforms a policy function into a validation function (actually
/// not exactly a validation function, because validation functions apply on
/// devices - see the [apply_policy_stateful] functor down below).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let raw_apply_policy_stateful
  (nc : iconfig) (peer_id : id_cl)
  (peer_info : St.stateful_malloc_from_input_clone_copy unit) (has_s has_psk recv_psk : bool)
  (policy : stateful_policy_function nc recv_psk) :
  St.stateful unit =
St.Stateful
  (* s *)
  (fun _ -> LL.t (raw_stateful_peer_p nc peer_id peer_info has_s has_psk))
  (* footprint *)
  (fun #_ s -> LL.region_of s)
  (* freeable *)
  (fun #_ h s -> LL.invariant h s) // the state is freeable only if the invariant is satisfied
  (* invariant *)
  (fun #_ h s -> LL.invariant h s)
  (* t *)
  (fun _ -> list (raw_peer_s nc (peer_info.St.smficc_stateful.St.t ())))
  (* v *)
  (fun _ h s -> LL.v h s)
  (* frame invariant *)
  (fun l s h0 h1 -> LL.frame_invariant s l h0 h1)
  (* frame freeable *)
  (fun l s h0 h1 -> LL.frame_invariant s l h0 h1)

/// The following functors implement the type: [option (peer_id & peer_info)]
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val raw_stateful_validation_info
  (pid_t : id_cl)
  (st:St.stateful unit) :
  stateful_peer_info

let raw_stateful_validation_info id_cl st =
St.Stateful
  (fun i -> B.pointer id_cl.id_t & st.St.s i)
  (fun #i s -> let id, pinfo = s in B.loc_union (B.loc_buffer id) (st.St.footprint #i pinfo))
  (* freeable - we don't support freeability of the whole pair for now: the
   * freeability of the peer information, which has to be maintained, is
   * kept in the invariant *)
  (fun #i h p -> False) //let id, pinfo = p in st.St.freeable #i h pinfo) // only the peer information should be freeable
  (fun #i h s ->
    let id, pinfo = s in
    B.live h id /\
    st.St.invariant #i h pinfo /\
    st.St.freeable #i h pinfo /\
    B.loc_disjoint (B.loc_buffer id) (st.St.footprint #i pinfo))
  (fun i -> option (Spec.peer_id & st.St.t i))
  (fun i h s ->
    let id, pinfo = s in
    let id = B.deref h id in
    if id = id_cl.id_none then None
    else Some (id_cl.id_v id, st.St.v i h pinfo))
  (fun #i l s h0 h1 ->
    let id, pinfo = s in
    st.St.frame_invariant #i l pinfo h0 h1;
    st.St.frame_freeable #i l pinfo h0 h1)
  (fun #i l s h0 h1 -> ()) // Nothing to prove

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let raw_apply_policy
  (nc : iconfig) (id_cl : id_cl)
  (peer_info : St.stateful_malloc_from_input_clone_copy unit)
  (has_s has_psk : bool)
  (policy : stateful_policy_function nc has_psk) :
  stateful_validation_state nc (raw_stateful_validation_info id_cl peer_info.St.smficc_stateful) =

Stateful_vstate

  (* vst *)
  (raw_apply_policy_stateful nc id_cl peer_info has_s has_psk has_psk policy)

  (* recv_psk *)
  has_psk

  (* validate_spec *)
  (fun st rs ->
   begin
   match M.lookup (raw_peer_has_s #(get_config nc) #(peer_info.St.smficc_stateful.St.t ()) rs) st with
   | Some p -> Some (Some (p.Spec.p_id, p.Spec.p_info), p.Spec.p_psk)
   | None ->
     if Stateful_policy_function?.apply_policy_spec policy rs
     then Some (None, None)
     else None
   end <: (option (option (Spec.peer_id & peer_info.St.smficc_stateful.St.t ()) &
                  (option preshared_key))))

  // validate
  (fun st rs pinfo psk ->
   (**) let h0 = ST.get () in
   [@inline_let]
   let pred : LL.pred_st #(raw_stateful_peer_p nc id_cl peer_info has_s has_psk) st B.loc_none
                         (fun h1 -> live h1 rs /\ B.(modifies loc_none h0 h1))
                         (fun _ _ -> ())
                         (raw_peer_has_s #(get_config nc)
                                         #(peer_info.St.smficc_stateful.St.t ()) (as_seq h0 rs)) =
     (fun (xp:raw_peer_p nc id_cl (peer_info.St.smficc_stateful) has_s has_psk) ->
       (**) let h1 = ST.get () in
       if has_s then
         begin
         let x = B.index xp.pp 0ul in
         (**) assert(as_seq h1 rs == as_seq h0 rs);
         lbytes_eq x.p_s rs
         end
       else false)
   in
   (**) assert(has_type pinfo (B.pointer id_cl.id_t & peer_info.St.smficc_stateful.St.s ()));
   [@inline_let] let pinfo : B.pointer id_cl.id_t & peer_info.St.smficc_stateful.St.s () = pinfo in
   [@inline_let] let id, info = pinfo in
   (**) [@inline_let] let vst =
   (**)   raw_apply_policy_stateful nc id_cl peer_info has_s has_psk has_psk policy in
   (**) [@inline_let] let peer_vinfo =
   (**)   raw_stateful_validation_info id_cl peer_info.St.smficc_stateful in

   [@inline_let] let stateful = (raw_stateful_peer_p nc id_cl peer_info has_s has_psk) in
   [@inline_let]
   let return_type : LL.find_return_type stateful = let open Impl.Noise.LinkedList in {
     f_rty = raw_peer_p_or_null nc id_cl peer_info.St.smficc_stateful has_s has_psk;
     f_g_get_elem = (fun p -> if B.g_is_null p.pp then None else Some p);
     f_from_elem = (fun p -> p);
     f_no_elem = { pp = B.null; pp_r = root; };
   } in

   let peer_ptr = LL.find #stateful st
                     #(fun h1 -> live h1 rs /\ B.(modifies loc_none h0 h1))
                     #(fun _ _ -> ())
                     #(raw_peer_has_s #(get_config nc)
                                      #(peer_info.St.smficc_stateful.St.t ()) (as_seq h0 rs))
                     return_type
                     pred
   in
   (**) let h1 = ST.get () in
   (**) peer_vinfo.St.frame_invariant B.loc_none pinfo h0 h1;
   (**) assert(peer_vinfo.St.invariant h1 pinfo);
   (**) vst.St.frame_invariant B.loc_none st h0 h1;
   (**) assert(vst.St.v () h0 st == vst.St.v () h1 st);
   (**) assert(peer_vinfo.St.v () h0 pinfo == peer_vinfo.St.v () h1 pinfo);

   if not (B.is_null #(raw_peer_t nc id_cl peer_info.St.smficc_stateful has_s has_psk) peer_ptr.pp) then
     begin
     begin
     (**) let st0_v = vst.St.v () h0 st in
     (**) let rs_v = as_seq h0 rs in
     (**) let peer_v = raw_peer_p_v #nc #id_cl #(peer_info.St.smficc_stateful) #has_s #has_psk h1 peer_ptr in
     (**) assert(M.lookup (raw_peer_has_s rs_v) st0_v == Some peer_v)
     end;
     (**) peer_vinfo.St.frame_invariant B.loc_none pinfo h0 h1;
     [@inline_let] let peer_ptr : raw_peer_p nc id_cl (peer_info.St.smficc_stateful) has_s has_psk = peer_ptr in
     let peer = B.index peer_ptr.pp 0ul in
     (**) let h2 = ST.get () in
     (**) peer_vinfo.St.frame_invariant B.loc_none pinfo h1 h2;
     (**) peer_info.St.smficc_stateful.St.frame_invariant B.loc_none peer.p_info h1 h2;
     (* Copy the peer id, the peer info and the psk - TODO: this proof may be factorized
      * with the proofs above *)
     peer_info.St.smficc_copy () info peer.p_info;
     (**) let h3 = ST.get () in
     B.upd id 0ul peer.p_id;
     (**) let h4 = ST.get () in
     lbuffer_or_unit_copy #uint8 #preshared_key_vs #has_psk psk peer.p_psk;
     (**) let h5 = ST.get () in
     (**) assert(B.loc_disjoint (B.loc_buffer id) (peer_info.St.smficc_stateful.St.footprint info));
     begin
     (**) let info_loc = peer_info.St.smficc_stateful.St.footprint info in
     (**) let id_loc = B.loc_buffer id in
     (**) let psk_loc = if has_psk then B.loc_buffer (psk <: buffer uint8) else B.loc_none in
     (**) let id_psk_loc = B.loc_union id_loc psk_loc in
     (**) let id_psk_info_loc = B.loc_union id_psk_loc info_loc in
     (**) assert(B.loc_disjoint (B.loc_buffer id) psk_loc);
     (**) assert(B.loc_disjoint id_psk_loc info_loc);
     (**) assert(B.loc_disjoint id_psk_info_loc (vst.St.footprint st));
//     (**) info_frame_invariant (B.loc_union id_loc psk_loc) info h3 h5;
//     (**) info_frame_freeable (B.loc_union id_loc psk_loc) info h3 h5;
     (**) peer_info.St.smficc_stateful.St.frame_invariant (B.loc_union id_loc psk_loc) info h3 h5;
     (**) peer_info.St.smficc_stateful.St.frame_freeable (B.loc_union id_loc psk_loc) info h3 h5;
//     (**) assert(info_invariant h5 info);
//     (**) assert(info_freeable h5 info);
     (**) assert(peer_info.St.smficc_stateful.St.invariant h5 info);
     (**) assert(peer_info.St.smficc_stateful.St.freeable h5 info);
     (**) assert(B.live h5 id);
     (**) assert(peer_vinfo.St.invariant h5 pinfo);
//     (**) assert(info_v h5 info == info_v h1 peer.p_info);
     (**) assert(peer_info.St.smficc_stateful.St.v () h5 info == peer_info.St.smficc_stateful.St.v () h1 peer.p_info);
     (**) vst.St.frame_invariant id_psk_info_loc st h1 h5;
     (**) assert(vst.St.v () h1 st == vst.St.v () h5 st);
     (**) assert(vst.St.invariant h5 st);
     (**) assert(B.modifies id_psk_info_loc h1 h5);
     (**) assert(B.(modifies (loc_union id_psk_info_loc (vst.St.footprint st)) h0 h5));
     (**) assert(B.(loc_includes (peer_vinfo.St.footprint pinfo) (loc_union id_loc info_loc)));
     (**) assert(B.deref h5 id == peer.p_id);
     (**) assert(peer.p_id <> id_cl.id_none);
     (**) assert(lbuffer_or_unit_live h5 psk);
     (**) assert(
     (**)   B.(modifies (loc_union (vst.St.footprint st)
     (**)               (loc_union (peer_vinfo.St.footprint pinfo) psk_loc)) h0 h5))
     end;
     true
     end
   else
     begin
     (* Update the peer id to 0: no peer was looked up *)
     B.upd id 0ul id_cl.id_none;
     (**) let b =
     (* No peer already registered: apply the policy *)
     Stateful_policy_function?.is_success policy
       (Stateful_policy_function?.apply_policy policy rs)
     in
     (**) let h2 = ST.get () in
     (**) vst.St.frame_invariant (B.loc_buffer id) st h1 h2;
//     (**) info_frame_invariant (B.loc_buffer id) info h1 h2;
//     (**) info_frame_freeable (B.loc_buffer id) info h1 h2;
     (**) peer_info.St.smficc_stateful.St.frame_invariant (B.loc_buffer id) info h1 h2;
     (**) peer_info.St.smficc_stateful.St.frame_freeable (B.loc_buffer id) info h1 h2;
     (**) assert(peer_vinfo.St.invariant h2 pinfo);
     (**) assert(vst.St.v () h1 st == vst.St.v () h2 st);
     (**) assert(B.deref h2 id = id_cl.id_none);
     b
     end)

(*** Peers *)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_stateful_peer_t (idc : idconfig) : St.stateful_clone unit =
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let peers_have_s = with_onorm(peers_have_s pattern) in
  [@inline_let] let is_psk = with_onorm(check_hsk_is_psk pattern) in
  raw_stateful_peer_t (idc_get_nc idc) (idc_get_pid idc) (idc_get_info idc)
                      peers_have_s is_psk

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_stateful_peer_p (idc : idconfig) : LL.stateful unit =
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let peers_have_s = with_onorm(peers_have_s pattern) in
  [@inline_let] let is_psk = with_onorm(check_hsk_is_psk pattern) in
  raw_stateful_peer_p (idc_get_nc idc) (idc_get_pid idc) (idc_get_info idc)
                      peers_have_s is_psk

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let peer_t (idc : idconfig) : Type0 =
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let peers_have_s = with_onorm(peers_have_s pattern) in
  [@inline_let] let is_psk = with_onorm(check_hsk_is_psk pattern) in
  raw_peer_t (idc_get_nc idc) (idc_get_pid idc) (idc_get_info idc).St.smficc_stateful
             peers_have_s is_psk

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let peer_p_or_null (idc : idconfig) : Type0 =
  [@inline_let] let pattern = idc_get_pattern idc in
  [@inline_let] let peers_have_s = with_onorm(peers_have_s pattern) in
  [@inline_let] let is_psk = with_onorm(check_hsk_is_psk pattern) in
  raw_peer_p_or_null (idc_get_nc idc) (idc_get_pid idc) (idc_get_info idc).St.smficc_stateful
                     peers_have_s is_psk

let peer_p_g_is_null #idc p =
  B.g_is_null p.pp

let peer_p_null idc =
  { pp = B.null; pp_r = root; } // The region is dummy

let peer_p_invariant #idc h p =
  let sp = LL.stateful_get_prim (idc_stateful_peer_p idc) in
  sp.St.invariant h p

let peer_p_footprint #idc p =
  let sp = LL.stateful_get_prim (idc_stateful_peer_p idc) in
  sp.St.footprint p

let peer_p_live #idc h p =
  live #MUT #_ h p.pp /\
  begin
  if peer_p_g_is_null p then True
  else peer_p_invariant h p
  end

let peer_p_is_null #idc p =
  B.is_null p.pp

let peer_p_invariant_live_lem #idc h p = ()

[@@ noextract_to "Karamel"] noextract
let peer_t_v (#idc : idconfig) (h : mem) (p : peer_t idc) :
  GTot (peer_s idc) =
  let pattern = idc_get_pattern idc in
  let peers_have_s = peers_have_s pattern in
  let is_psk = check_hsk_is_psk pattern in
  raw_peer_t_v #(idc_get_nc idc) #(idc_get_pid idc) #(idc_get_info idc).St.smficc_stateful
               #peers_have_s #is_psk h (convert_type p)

let peer_p_v (#idc : idconfig) (h : mem) (p : peer_p idc) =
  let pattern = idc_get_pattern idc in
  let peers_have_s = peers_have_s pattern in
  let is_psk = check_hsk_is_psk pattern in
  raw_peer_p_v #(idc_get_nc idc) #(idc_get_pid idc) #(idc_get_info idc).St.smficc_stateful
               #peers_have_s #is_psk h p

//[@@ noextract_to "Karamel"] inline_for_extraction noextract
//let peer_id_none (idc : idconfig) = (idc_get_pid idc).id_none
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let peer_id_is_none (#idc : idconfig) = fun (pid : peer_id_opt_t idc) -> pid = peer_id_none idc
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let peer_id_is_some (#idc : idconfig) = fun (pid : peer_id_opt_t idc) -> not (pid = peer_id_none idc)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_info_footprint (#idc : idconfig) = (idc_get_info idc).St.smficc_stateful.St.footprint
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_info_invariant (#idc : idconfig) = (idc_get_info idc).St.smficc_stateful.St.invariant
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_info_freeable (#idc : idconfig) = (idc_get_info idc).St.smficc_stateful.St.freeable
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_info_frame_invariant (#idc : idconfig) = (idc_get_info idc).St.smficc_stateful.St.frame_invariant
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_info_frame_freeable (#idc : idconfig) = (idc_get_info idc).St.smficc_stateful.St.frame_freeable
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let idc_get_info_v (#idc : idconfig) = (idc_get_info idc).St.smficc_stateful.St.v ()

/// We redefine the info frame invariants so that the SMT patterns are triggered -
/// makes the proofs a lot easier. Note that this is internal - those patterns
/// are only revealed if we friend the module.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val info_frame_invariant_smt (#idc : idconfig) (l : B.loc) (info : info_t idc) (h0 h1 : mem) :
  Lemma
  (requires (
    info_invariant h0 info /\
    B.loc_disjoint l (info_footprint info) /\
    B.modifies l h0 h1))
  (ensures (
    info_invariant h1 info /\
    info_v h1 info == info_v h0 info))
  [SMTPat (info_invariant h0 info);
   SMTPat (B.modifies l h0 h1) ]

let info_frame_invariant_smt #idc l info h0 h1 =
  info_frame_invariant l info h0 h1

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val info_frame_freeable_smt (#idc : idconfig) (l : B.loc) (info : info_t idc) (h0 h1 : mem) :
  Lemma
  (requires (
    info_invariant h0 info /\
    info_freeable h0 info /\
    B.loc_disjoint l (info_footprint info) /\
    B.modifies l h0 h1))
  (ensures (
    info_freeable h1 info))
  [SMTPat (info_freeable h0 info);
   SMTPat (B.modifies l h0 h1) ]

let info_frame_freeable_smt #idc l info h0 h1 =
  info_frame_freeable l info h0 h1

let peer_p_frame_live #idc l p h0 h1 =
  let sp = LL.stateful_get_prim (idc_stateful_peer_p idc) in
  if peer_p_g_is_null p then ()
  else sp.St.frame_invariant l p h0 h1

let peer_p_frame_invariant #idc l p h0 h1 =
  let sp = LL.stateful_get_prim (idc_stateful_peer_p idc) in
  sp.St.frame_invariant l p h0 h1

let mk_peer_p_get_id #idc pp =
  let p = B.index pp.pp 0ul in
  p.p_id

let mk_peer_p_get_info #idc out pp =
  let p = B.index pp.pp 0ul in
  (idc_get_info idc).St.smficc_copy () out p.p_info

let mk_peer_p_get_static #idc out pp =
  let p = B.index pp.pp 0ul in
  lbuffer_or_unit_copy out p.p_s

let mk_peer_p_get_psk #idc out pp =
  let p = B.index pp.pp 0ul in
  copy #MUT #uint8 #preshared_key_vs out p.p_psk

/// This lemma is necessary because of the F* encoding to Z3
val peer_p_eq_lem (idc : idconfig) :
  Lemma (
    peer_p idc ==
    (idc_stateful_peer_p idc).St.smfi_stateful.St.s ())
  [SMTPat (peer_p idc)]

#push-options "--ifuel 0"
let peer_p_eq_lem idc =
  let pattern = idc_get_pattern idc in
  // If we don't put the [with_onorm] in the below let-bindings, the proof fails
  let peers_have_s = with_onorm(peers_have_s pattern) in
  let is_psk = with_onorm(check_hsk_is_psk pattern) in
  let nc = idc_get_nc idc in
  let pid = idc_get_pid idc in
  let pinfo = idc_get_info idc in
  assert(peer_p idc == p:peer_p_or_null idc{not (peer_p_g_is_null p)});
  assert(
    peer_p_or_null idc ==
    raw_peer_p_or_null nc pid pinfo.St.smficc_stateful peers_have_s is_psk);
  assert_norm(
    peer_p idc ==
    pp:raw_peer_p_or_null nc pid pinfo.St.smficc_stateful peers_have_s is_psk{not(peer_p_g_is_null #idc pp)});
  assert_norm(
    pp:raw_peer_p_or_null nc pid pinfo.St.smficc_stateful peers_have_s is_psk{not(peer_p_g_is_null #idc pp)} ==
    pp:raw_peer_p_or_null nc pid pinfo.St.smficc_stateful peers_have_s is_psk{not (B.g_is_null pp.pp)});
  assert(
    (idc_stateful_peer_p idc).St.smfi_stateful.St.s () ==
    (idc_stateful_peer_p idc).St.smfi_stateful.St.s ());
  assert(
    (idc_stateful_peer_p idc).St.smfi_stateful.St.s () ==
    (raw_stateful_peer_p nc pid pinfo
                      peers_have_s is_psk).St.smfi_stateful.St.s ());
  assert(
    (idc_stateful_peer_p idc).St.smfi_stateful.St.s () ==
    (raw_stateful_peer_p_prim nc pid pinfo.St.smficc_stateful peers_have_s is_psk).St.s ());
  assert(
    (idc_stateful_peer_p idc).St.smfi_stateful.St.s () ==
    (raw_peer_p nc pid pinfo.St.smficc_stateful peers_have_s is_psk));
  assert_norm(
    raw_peer_p nc pid pinfo.St.smficc_stateful peers_have_s is_psk ==
    (pp:raw_peer_p_or_null nc pid pinfo.St.smficc_stateful peers_have_s is_psk{not (B.g_is_null pp.pp)}));
  assert(
    peer_p idc ==
    (idc_stateful_peer_p idc).St.smfi_stateful.St.s ())
#pop-options


(*** Configuration *)

// Controling unfolding for type inference
let idc_is_valid (idc : idconfig) : Tot bool = idc_is_valid_compute idc
let idc_is_valid_lem idc = ()

(*** Device *)

[@CAbstractStruct]
noeq type device_t_raw
  (info_t sk_t spriv_t spub_t prologue_t states_counter_t peers_t peers_counter_t cstate_t : Type0) :
  Type0 = {
  (* Info *)
  dv_info : info_t;
  (* AEAD key used for serialization/deserialization *)
  dv_sk : sk_t;
  (* Static key *)
  dv_spriv : spriv_t;
  dv_spub : spub_t;
  (* Prologue *)
  dv_prologue : prologue_t;
  (* States *)
  dv_states_counter : states_counter_t;
  (* Peers *)
  dv_peers : peers_t;
  dv_peers_counter : peers_counter_t;
  (* Certification state *)
  dv_cstate : cstate_t;
}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type device_t (idc : idconfig) : Type0 =
  device_t_raw
    (info_t idc) (serialize_key_t idc)
    (private_key_t_or_unit (idc_get_nc idc) (device_has_s (idc_get_pattern idc)))
    (public_key_t_or_unit (idc_get_nc idc) (device_has_s (idc_get_pattern idc)))
    (hsized_buffer (idc_get_nc idc))
    (state_id_t idc)
    (LL.t (idc_stateful_peer_p idc))
    (peer_id_t idc)
    (idc_get_cstate_s idc)

noeq type device_p_raw (device_t : Type0) : Type0 = {
  dvp : B.pointer_or_null device_t;
  // Parent region: used to make the footprint independent from the memory snapshot
  dvp_r : HS.rid;
}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type device_p_or_null (idc : idconfig) : Type0 =
  device_p_raw (device_t idc)

let device_p_g_is_null #idc dvp =
  B.g_is_null dvp.dvp

#push-options "--ifuel 1"
let peers_counter_invariant (#idc : idconfig) (counter : peer_id)
                            (peers : list (peer_s idc)) : GTot Type0 =
  List.Tot.for_all (peer_has_smaller_id #(idc_get_dc idc) counter) peers
#pop-options

#push-options "--ifuel 1"
let peers_pairwise_distinct_ids (#idc : idconfig) (peers : list (peer_s idc)) : GTot Type0 =
  Spec.peers_pairwise_distinct_ids #(idc_get_dc idc) peers
#pop-options

#push-options "--ifuel 1"
let peers_pairwise_distinct_statics  (#idc : idconfig) (peers : list (peer_s idc)) : GTot Type0 =
  Spec.peers_pairwise_distinct_statics #(idc_get_dc idc) peers
#pop-options

/// Note that we don't request anything about the certification state: 
/// by providing precise pre and postconditions, we give enough information
/// to the user for him to take care of the certification state. Otherwise,
/// we would have to define several invariants/footprints to include or not
/// conditions about the certification state. In practice, we need
/// disjointness and validity (i.e.: the invariant is satisfied) conditions
/// only for the handshake read messages function, and thus add those
/// conditions to the signature of those functions.
let device_t_invariant (#idc : idconfig) (h : mem) (dv : device_t idc) : GTot Type0 =
  let Mkdevice_t_raw info sk spriv spub prologue scounter peers pcounter cert = dv in

  (*
   * Administrative
   *)
  (* Buffers *)
  // Disjointness
  begin
  let sk_loc = lbuffer_or_unit_to_loc sk in
  let spriv_loc = lbuffer_or_unit_to_loc spriv in
  let spub_loc = lbuffer_or_unit_to_loc spub in
  let prologue_loc = sized_buffer_to_loc prologue in
  let info_loc = info_footprint info in
  let peers_loc = LL.region_of peers in
  B.all_disjoint [sk_loc; spriv_loc; spub_loc; prologue_loc; info_loc; peers_loc]
  end /\
  
  // Buffers are live and freeable
  lbuffer_or_unit_live h sk /\
  lbuffer_or_unit_live h spriv /\
  lbuffer_or_unit_live h spub /\
  sized_buffer_live h prologue /\
  
  lbuffer_or_unit_freeable sk /\
  lbuffer_or_unit_freeable spriv /\
  lbuffer_or_unit_freeable spub /\
  sized_buffer_freeable prologue /\
  
  (* Info *)
  info_invariant h info /\
  info_freeable h info /\

  (* Peers' list invariant *)
  LL.invariant h peers /\
  
  (* Functional specification *)
  // The peer id counter must be greater than all the peers' ids
  peers_counter_invariant #idc (peer_id_v pcounter) (LL.v h peers) /\
  
  // Peers' ids must be pairwise distinct
  peers_pairwise_distinct_ids #idc (LL.v h peers) /\

  // Peers' static keys must be pairwise distinct
  peers_pairwise_distinct_statics #idc (LL.v h peers)

let device_t_footprint (#idc : idconfig) (dv : device_t idc) : GTot B.loc =
  let Mkdevice_t_raw info sk spriv spub prologue scounter peers pcounter cert = dv in
  let sk_loc = lbuffer_or_unit_to_loc sk in
  let spriv_loc = lbuffer_or_unit_to_loc spriv in
  let spub_loc = lbuffer_or_unit_to_loc spub in
  let prologue_loc = sized_buffer_to_loc prologue in
  let info_loc = info_footprint info in
  let peers_loc = LL.region_of peers in
  B.(loc_union (loc_union sk_loc (loc_union spriv_loc spub_loc))
               (loc_union prologue_loc (loc_union info_loc peers_loc)))

let device_t_peers_footprint (#idc : idconfig) (dv : device_t idc) : GTot B.loc =
  let Mkdevice_t_raw info sk spriv spub prologue scounter peers pcounter cert = dv in
  LL.region_of peers

let device_p_live (#idc : idconfig) (h : mem) (dvp : device_p_or_null idc) : GTot Type0 =
  B.live h dvp.dvp

let device_p_invariant (#idc : idconfig) (h : mem) (dvp : device_p idc) : GTot Type0 =
  let dv = B.deref h dvp.dvp in

  // If dvp.dvp_r <> FStar.Monotonic.HyperHeap.root, we can use:
  // * [ST.recall_region]
  // * [FStar.Monotonic.HyperStack.eternal_disjoint_from_tip]
  // to show that the region is disjoint from the stack.
  // This won't appear on the user side: at allocation time, we use the trick
  // of allocating a new region inside the region the user provides for heap
  // allocation, and allocate the new device in this new region.
  ST.is_eternal_region dvp.dvp_r /\
  dvp.dvp_r <> root /\

  B.live h dvp.dvp /\
  B.freeable dvp.dvp /\

  region_includes dvp.dvp_r (device_t_footprint dv) /\
  region_includes dvp.dvp_r (B.loc_addr_of_buffer dvp.dvp) /\

  B.loc_disjoint (B.loc_addr_of_buffer dvp.dvp) (device_t_footprint dv) /\
  
  device_t_invariant h dv

let device_p_footprint (#idc : idconfig) (h : mem) (dvp : device_p idc) : GTot B.loc =
  let dv = B.deref h dvp.dvp in
  B.loc_union (B.loc_addr_of_buffer dvp.dvp) (device_t_footprint dv)

let device_p_is_null #idc dvp =
  B.is_null dvp.dvp

let device_p_rid_of (#idc : idconfig) (dvp : device_p idc) :
  GTot HS.rid =
  dvp.dvp_r

val device_p_footprint_in_region (#idc : idconfig) (h : mem)
                                 (dvp : device_p idc) :
  Lemma
  (requires (device_p_invariant h dvp))
  (ensures (B.loc_includes (device_p_region_of dvp) (device_p_footprint h dvp)))
  [SMTPat (B.loc_includes (device_p_region_of dvp) (device_p_footprint h dvp))]

let device_p_footprint_in_region #idc h dvp = ()

let device_p_recall_region #idc dvp =
  (**) let h0 = ST.get () in
  recall_region dvp.dvp_r;
  // We could use a pattern instead, but it would be cumbersome
  if IndefiniteDescription.strong_excluded_middle (is_stack_region (get_tip h0)) then
    eternal_disjoint_from_tip h0 dvp.dvp_r
  else ()

val device_t_owns_peer :
     #idc:idconfig
  -> h:mem
  -> dv:device_t idc
  -> p:option (peer_p idc) ->
  GTot Type0

let device_t_owns_peer #idc h dv p =
  match p with
  | None -> True
  | Some p ->
    let peers = dv.dv_peers in
    let sp = LL.stateful_get_prim (idc_stateful_peer_p idc) in
    LL.list_owns_element h dv.dv_peers p /\
    // Those are actually given by list_owns_element in combination with
    // the linked list invariant
    sp.St.invariant h p /\
    B.loc_includes (LL.region_of peers) (sp.St.footprint p)

let device_p_owns_peer #md h dvp p =
  let dv = B.deref h dvp.dvp in
  if peer_p_g_is_null p then device_t_owns_peer h dv None
  else device_t_owns_peer h dv (Some p)

let device_p_owns_peer_lem #idc h dvp p = ()

#push-options "--ifuel 1"
let device_t_v (#idc : idconfig) (m : mem) (dv : device_t idc) : GTot (device_s idc) =
  let pattern = idc_get_pattern idc in
  let nc = idc_get_nc idc in
  let ks_init = key_slots_from_pattern true pattern in
  let ks_resp = key_slots_from_pattern false pattern in
  let Mkdevice_t_raw info sk spriv spub prlg scounter peers pcounter cert = dv in
  let info_v = info_v m info in
  let sk_v = lbuffer_or_unit_to_opt_lseq m sk in
  let s_v = keys_t_or_unit_to_keypair m spriv spub in
  let prlg_v = sized_buffer_to_seq m prlg in
  let scounter_v = state_id_v scounter in
  let peers_v = LL.v m peers in
  let pcounter_v = peer_id_v pcounter in
  {
    Spec.dv_pattern = idc_get_pattern idc;
    Spec.dv_info = info_v;
    Spec.dv_sk = sk_v;
    Spec.dv_static_identity = s_v;
    Spec.dv_prologue = prlg_v;
    Spec.dv_states_counter = scounter_v;
    Spec.dv_peers = peers_v;
    Spec.dv_peers_counter = pcounter_v;
  }
#pop-options

let device_p_v (#idc : idconfig) (m : mem) (dvp : device_p idc) : GTot (device_s idc) =
  let dv = B.deref m dvp.dvp in
  device_t_v m dv

let device_t_g_get_peers_counter (#idc : idconfig) (h : mem) (dv : device_t idc) :
  GTot peer_id =
  let dv_v = device_t_v h dv in
  device_get_peers_counter dv_v

val device_t_get_cstate (#idc : idconfig) (dv : device_t idc) : GTot (idc_get_cstate_s idc)
let device_t_get_cstate #idc dv =
  let Mkdevice_t_raw info sk spriv spub prlg scounter peers pcounter cstate = dv in
  cstate

let device_p_get_cstate #idc h dvp =
  let dv = B.deref h dvp.dvp in
  device_t_get_cstate dv

val device_t_get_static (#idc : idconfig) (dv : device_t idc) :
  GTot (
    private_key_t_or_unit (idc_get_nc idc) (device_has_s (idc_get_pattern idc)) &
    public_key_t_or_unit (idc_get_nc idc) (device_has_s (idc_get_pattern idc)))
let device_t_get_static #idc dv =
  let Mkdevice_t_raw info sk spriv spub prlg scounter peers pcounter cstate = dv in
  spriv, spub

let device_p_g_get_states_counter #idc h dvp =
  let dv = B.deref h dvp.dvp in
  let Mkdevice_t_raw info sk spriv spub prlg scounter peers pcounter cstate = dv in
  scounter

let device_p_g_get_peers_counter #idc h dvp =
  let dv = B.deref h dvp.dvp in
  let Mkdevice_t_raw info sk spriv spub prlg scounter peers pcounter cstate = dv in
  pcounter

let mk_device_p_get_states_counter #idc dvp =
  let dv = B.index dvp.dvp 0ul in
  let Mkdevice_t_raw _ _ _ _ _ scounter _ _ _ = dv in
  scounter

let mk_device_p_get_sessions_counter #idc dvp =
  mk_device_p_get_states_counter #idc dvp

let mk_device_p_get_peers_counter #idc dvp =
  let dv = B.index dvp.dvp 0ul in
  let Mkdevice_t_raw _ _ _ _ _ _ _ pcounter _ = dv in
  pcounter

let mk_device_p_states_counter_is_saturated #idc dvp =
  let cnt = mk_device_p_get_states_counter dvp in
  cnt = with_onorm (state_id_max idc)

let mk_device_p_sessions_counter_is_saturated #idc dvp =
  mk_device_p_states_counter_is_saturated #idc dvp

let mk_device_p_peers_counter_is_saturated #idc dvp =
  let cnt = mk_device_p_get_peers_counter dvp in
  cnt = with_onorm (peer_id_max idc)

let mk_device_p_get_info #idc out dvp =
  let dv = B.index dvp.dvp 0ul in
  (idc_get_info idc).St.smficc_copy () out dv.dv_info

let device_p_g_get_static #idc h dvp =
  let dv = B.deref h dvp.dvp in
  device_t_get_static dv

let mk_device_p_get_static_priv #idc out dvp =
  let dv = B.index dvp.dvp 0ul in
  lbuffer_or_unit_copy out dv.dv_spriv

let mk_device_p_get_static_pub #idc out dvp =
  let dv = B.index dvp.dvp 0ul in
  lbuffer_or_unit_copy out dv.dv_spub

let device_t_g_get_peers (#idc : idconfig) (h : mem) (dv : device_t idc) :
  GTot (list (LL.dt_s (idc_stateful_peer_p idc))) =
  LL.get_elems h dv.dv_peers

let device_p_g_get_peers (#idc : idconfig) (h : mem) (dvp : device_p idc) :
  GTot (list (LL.dt_s (idc_stateful_peer_p idc))) =
  let dv = B.deref h dvp.dvp in
  device_t_g_get_peers h dv

/// Note that the pointers can't change.
/// TODO: is this predicate really useful?
let device_t_only_changed_peers_or_counters (#idc : idconfig) (dv : device_t idc) (h0 h1 : mem) :
  GTot Type0 =
  let spriv, spub = device_t_get_static dv in
  lbuffer_or_unit_to_opt_lseq h1 spriv == lbuffer_or_unit_to_opt_lseq h0 spriv /\
  lbuffer_or_unit_to_opt_lseq h1 spub == lbuffer_or_unit_to_opt_lseq h0 spub /\
  True

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val device_t_no_removal (#idc : idconfig) (dv : device_t idc) (h0 h1 : mem) :
  GTot Type0
let device_t_no_removal #idc dv h0 h1 =
  device_t_only_changed_peers_or_counters dv h0 h1 /\
  device_t_invariant h0 dv /\
  device_t_invariant h1 dv /\
  // The peers present in the device in h0 are also present
  // in the device in h1
  M.list_in_listP (device_t_g_get_peers h0 dv) (device_t_g_get_peers h1 dv) /\
  // The peers are not modified between h0 and h1
  LL.gsame_elementsp (device_t_g_get_peers h0 dv) h0 h1

val device_t_frame_invariant :
     #idc:idconfig
  -> l:B.loc
  -> dv:device_t idc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    device_t_invariant h0 dv /\
    B.loc_disjoint l (device_t_footprint dv) /\
    B.modifies l h0 h1))
  (ensures (
    device_t_invariant h1 dv /\
    device_t_v h0 dv == device_t_v h1 dv /\
    device_t_no_removal dv h0 h1))
  [SMTPat (device_t_invariant h0 dv); SMTPat (B.modifies l h0 h1)]

#push-options "--ifuel 1"
let device_t_frame_invariant #idc l dv h0 h1 =
  let peers_l0 = device_t_g_get_peers h0 dv in
  let peers_l1 = device_t_g_get_peers h1 dv in
  assert(peers_l0 == peers_l1);
  M.list_in_listP_refl peers_l0;
  assert(M.list_in_listP peers_l0 peers_l1);
  assert(LL.gsame_elementsp peers_l0 h0 h1);
  LL.frame_invariant dv.dv_peers l h0 h1;
  assert(LL.v h1 dv.dv_peers == LL.v h0 dv.dv_peers);
  info_frame_invariant l dv.dv_info h0 h1;
  info_frame_freeable l dv.dv_info h0 h1
#pop-options

let device_p_only_changed_peers_or_counters (#idc : idconfig) (dvp : device_p idc) (h0 h1 : mem) :
  GTot Type0 =
  let dv0 = B.deref h0 dvp.dvp in
  let dv1 = B.deref h1 dvp.dvp in
  // Note that the peer counter might have changed
  dv1.dv_sk == dv0.dv_sk /\
  dv1.dv_spriv == dv0.dv_spriv /\
  dv1.dv_spub == dv0.dv_spub /\
  dv1.dv_prologue == dv0.dv_prologue /\
  dv1.dv_peers == dv0.dv_peers /\
  dv1.dv_cstate == dv0.dv_cstate /\
  dv1.dv_info == dv0.dv_info /\
  device_t_only_changed_peers_or_counters dv0 h0 h1

let device_p_no_removal #idc dvp h0 h1 =
  device_p_only_changed_peers_or_counters dvp h0 h1 /\
  device_p_invariant h0 dvp /\
  device_p_invariant h1 dvp /\
  // The peers present in the device in h0 are also present
  // in the device in h1
  M.list_in_listP (device_p_g_get_peers h0 dvp) (device_p_g_get_peers h1 dvp) /\
  // The peers are not modified between h0 and h1
  LL.gsame_elementsp (device_p_g_get_peers h0 dvp) h0 h1

// Sanity check
let device_p_t_no_removal_lem
  (#idc : idconfig) (dvp : device_p idc) (h0 h1 : mem) :
  Lemma
  (requires (
    let dv0 = B.deref h0 dvp.dvp in
    let dv1 = B.deref h1 dvp.dvp in
    dv0 == dv1 /\
    device_p_invariant h0 dvp /\
    device_p_invariant h1 dvp /\
    device_t_no_removal dv0 h0 h1))
  (ensures (device_p_no_removal dvp h0 h1)) =
  let dv0 = B.deref h0 dvp.dvp in
  let dv1 = B.deref h1 dvp.dvp in
  assert(device_p_only_changed_peers_or_counters dvp h0 h1);
  assert(device_p_invariant h0 dvp);
  assert(device_p_invariant h1 dvp);
  assert(M.list_in_listP (device_p_g_get_peers h0 dvp) (device_p_g_get_peers h1 dvp));
  assert(LL.gsame_elementsp (device_p_g_get_peers h0 dvp) h0 h1)

val device_t_removed_peer 
  (#idc : idconfig) (dv : device_t idc) (pid : peer_id) (h0 h1 : mem) :
  GTot Type0

/// This is really annoying: when giving functions to other functions, F* often
/// messes up the SMT encoding, leading to impossible proofs. The only way to
/// get out of this situation is to introduce auxiliary functions and reuse them
/// everywhere. I let you admire the beautiful code it leads to.
// First function. I love duplicating code.
let remove_peer_filter_pred_s (idc : idconfig) (pid : peer_id) (h : mem) :
  peer_p idc -> GTot bool =
  fun x -> peer_p_g_get_id #idc h x <> pid

// Second function.
let remove_peer_unchanged_pred_s (idc : idconfig) (h0 h1 : mem) :
  peer_p idc -> GTot Type0 =
  let dt = idc_stateful_peer_p idc in
  LL.gsame_elementp #dt h0 h1

let device_t_removed_peer #idc dv pid h0 h1 =
  device_t_only_changed_peers_or_counters dv h0 h1 /\
  device_t_invariant h0 dv /\
  device_t_invariant h1 dv /\
  begin
  let filter_pred = remove_peer_filter_pred_s idc pid h0 in
  let filtered = M.gfilter_one filter_pred (device_t_g_get_peers h0 dv) in
  let unchanged_pred = remove_peer_unchanged_pred_s idc h0 h1 in
  M.list_in_listP filtered (device_t_g_get_peers h1 dv) /\
  M.gfor_allP unchanged_pred filtered
  end

let device_p_removed_peer #idc dvp pid h0 h1 =
  let dv = B.deref h0 dvp.dvp in
  device_p_only_changed_peers_or_counters dvp h0 h1 /\
  device_p_invariant h0 dvp /\
  device_p_invariant h1 dvp /\
  device_t_removed_peer dv pid h0 h1

let device_p_no_removal_implies_only_changed_peers_or_counters #idc dvp h0 h1 = ()

let device_p_removed_peer_implies_only_changed_peers_or_counters #idc dvp pid h0 h1 = ()

let device_p_frame_invariant #idc l dvp h0 h1 =
  let dv = B.deref h0 dvp.dvp in
  device_t_frame_invariant l dv h0 h1

let device_p_or_null_frame_invariant #idc l dvp h0 h1 = ()

let device_p_only_changed_peers_or_counters_trans_lem #idc dvp h0 h1 h2 = ()

(***** Policy to verification state *)

/// Functor which transforms a policy function into a validation function (actually
/// not exactly a validation function, because validation functions apply on
/// devices - see the [apply_policy_stateful] functor down below).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let apply_policy_stateful (idc : idconfig) : St.stateful unit =
St.Stateful
  (* s *)
  (fun _ -> device_t idc)
  (* footprint *)
  (fun #_ s -> device_t_footprint s)
  (* freeable *)
  (fun #_ h s -> device_t_invariant h s)
  (* invariant *)
  (fun #_ h s -> device_t_invariant h s)
  (* t *)
  (fun _ -> device_s idc)
  (* v *)
  (fun _ h s -> device_t_v h s)
  (* frame invariant *)
  (fun l s h0 h1 -> device_t_frame_invariant l s h0 h1)
  (* frame freeable *)
  (fun l s h0 h1 -> device_t_frame_invariant l s h0 h1)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let stateful_validation_info (idc : idconfig) : stateful_peer_info =
  raw_stateful_validation_info (idc_get_pid idc) (idc_get_info idc).St.smficc_stateful

(**** Creation *)

#push-options "--ifuel 1"
/// We use regions to reason about disjointness, which means r should always be
/// a fresh region dedicated to the device (we don't provide a way to reason about
/// disjointness between the device and something else in the same region).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_t_create
  (#idc : idconfig)
  (r : HS.rid)
  (r_s : HS.rid)
  (r_new : HS.rid)
  (cstate : idc_get_cstate_s idc)
  (prlg_len : hashable_size_t (idc_get_nc idc))
  (prlg : lbuffer uint8 prlg_len)
  (info : info_input_t idc)
  // The serialization key and the static identity should already have been correctly allocated
  (sk : serialize_key_t idc)
  (spriv : private_key_t_or_unit (idc_get_nc idc) (idc_uses_s idc))
  (spub : public_key_t_or_unit (idc_get_nc idc) (idc_uses_s idc)) :
  ST (device_t idc)
  (requires (fun h0 ->
    ST.is_eternal_region r /\
    ST.is_eternal_region r_s /\
    ST.is_eternal_region r_new /\
    live h0 prlg /\
    info_input_invariant h0 info /\
    lbuffer_or_unit_live h0 sk /\
    lbuffer_or_unit_live h0 spriv /\ lbuffer_or_unit_live h0 spub /\
    lbuffer_or_unit_freeable sk /\
    lbuffer_or_unit_freeable spriv /\ lbuffer_or_unit_freeable spub /\
    B.all_disjoint [lbuffer_or_unit_to_loc sk;
                    lbuffer_or_unit_to_loc spriv;
                    lbuffer_or_unit_to_loc spub] /\
    region_includes r_s (lbuffer_or_unit_to_loc sk) /\
    region_includes r_s (lbuffer_or_unit_to_loc spriv) /\
    region_includes r_s (lbuffer_or_unit_to_loc spub) /\
    region_includes_region r r_s /\
    region_includes_region r r_new /\
    disjoint_regions r_s r_new /\
    begin
    let nc = idc_get_config idc in
    let spriv_v = lbuffer_or_unit_to_opt_lseq h0 spriv in
    let spub_v = lbuffer_or_unit_to_opt_lseq h0 spub in
    let opt_kp = Spec.Noise.Utils.keypair_from_opt_private #nc spriv_v in
    if Some? spriv_v then
      Some? opt_kp /\ Some?.v spub_v == (Some?.v opt_kp).pub
    else True
    end))
  (ensures (fun h0 dv h1 ->
    B.(modifies loc_none h0 h1) /\
    device_t_invariant h1 dv /\
    region_includes r (device_t_footprint dv) /\
    device_t_get_cstate dv == cstate /\
    begin
    let pattern = idc_get_pattern idc in
    let prlg_v = as_seq h0 prlg in
    let info_v = info_input_v h0 info in
    let sk_v = lbuffer_or_unit_to_opt_lseq h0 sk in
    let s_v = lbuffer_or_unit_to_opt_lseq h0 spriv in
    let opt_dv_v = Spec.create_device (idc_get_dc idc) (idc_get_pattern idc) prlg_v info_v sk_v s_v in
    Some? opt_dv_v /\
    device_t_v h1 dv == Some?.v opt_dv_v
    end))
#pop-options

#push-options "--fuel 1 --ifuel 1"
let mk_device_t_create #idc r r_s r_new cstate prlg_len prlg info sk spriv spub =
  (**) let h0 = ST.get () in
  (**) let r_prlg = ST.new_region r_new in
  (**) let r_info = ST.new_region r_new in
  (**) let r_peers = ST.new_region r_new in
  (**) assert(region_includes_region r_new r_prlg);
  (**) assert(region_includes_region r_new r_info);
  (**) assert(region_includes_region r_new r_peers);
  (**) assert(region_includes_region r r_prlg);
  (**) assert(region_includes_region r r_info);
  (**) assert(region_includes_region r r_peers);
  (**) assert(B.all_disjoint [region_to_loc r_s; region_to_loc r_prlg; region_to_loc r_info; region_to_loc r_peers]);
  let prlg' = lbuffer_malloc_copy_also_empty r_prlg (u8 0) prlg in
  let prlg' = { size = prlg_len; buffer = prlg' } in
  (**) assert(region_includes r_prlg (sized_buffer_to_loc prlg'));
  (**) assert(region_includes r_new (sized_buffer_to_loc prlg'));
  (**) assert(region_includes r (sized_buffer_to_loc prlg'));
  (**) let h_info0 = ST.get () in
  (**) info_input_frame_invariant B.loc_none info h0 h_info0;
  let info' = (idc_get_info idc).St.smficc_malloc_from_input () r_info info in
  (**) let h_info1 = ST.get () in
  (**) assert(region_includes r_info (info_footprint info'));
  (**) assert(region_includes r_new (info_footprint info'));
  (**) assert(region_includes r (info_footprint info'));
  let peers = LL.create_in #(idc_stateful_peer_p idc) r_peers in
  (**) assert(region_includes r_peers (LL.region_of peers));
  (**) assert(region_includes r_new (LL.region_of peers));
  (**) assert(region_includes r (LL.region_of peers));
  // Lemmas for the counters initialization
  (**) (idc_get_sid idc).id_zero_v_lem ();
  (**) (idc_get_pid idc).id_zero_v_lem ();
  [@inline_let]
  let dv =
  {
    dv_info = info';
    dv_sk = sk;
    dv_spriv = spriv;
    dv_spub = spub;
    dv_prologue = prlg';
    dv_states_counter = (idc_get_sid idc).id_zero;
    dv_peers = peers;
    dv_peers_counter = (idc_get_pid idc).id_zero;
    dv_cstate = cstate;
  } in
  (**) let h1 = ST.get () in
  (**) info_frame_invariant B.loc_none info' h_info1 h1;
  (**) info_frame_freeable B.loc_none info' h_info1 h1;
  (**) assert(device_t_invariant h1 dv);
  dv
#pop-options

let device_p_no_removal_trans_lem #idc dvp h0 h1 h2 =
  assert(device_p_only_changed_peers_or_counters dvp h0 h2);
  let peers_l0 = device_p_g_get_peers h0 dvp in
  let peers_l1 = device_p_g_get_peers h1 dvp in
  let peers_l2 = device_p_g_get_peers h2 dvp in
  M.list_in_listP_trans peers_l0 peers_l1 peers_l2;
  assert(M.list_in_listP peers_l0 peers_l2);
  assert(LL.gsame_elementsp peers_l0 h0 h1);
  assert(LL.gsame_elementsp peers_l1 h1 h2);
  LL.gsame_elementsp_list_in_listP_trans peers_l0 peers_l1 h0 h1 h2;
  assert(device_p_no_removal dvp h0 h2)

let peer_p_or_null_frame_invariant #idc l p dvp h0 h1 =
  assert(B.loc_includes (device_p_region_of dvp) (peer_p_or_null_footprint p));
  peer_p_frame_live l p h0 h1;
  if peer_p_g_is_null p then ()
  else
    begin
    peer_p_frame_invariant l p h0 h1;
    assert(device_p_owns_peer h1 dvp p)
    end

let peer_p_or_null_no_removal_frame_invariant #idc p dvp h0 h1 =
  if peer_p_g_is_null p then ()
  else
    begin
    let dv0 = B.deref h0 dvp.dvp in
    let dv1 = B.deref h1 dvp.dvp in
    let peers_l0 = device_p_g_get_peers h0 dvp in
    let peers_l1 = device_p_g_get_peers h1 dvp in
    // From the definition of device_p_no_removal
    assert(M.list_in_listP peers_l0 peers_l1);
    assert(LL.gsame_elementsp peers_l0 h0 h1);
    // Targets
    assert(device_p_invariant h1 dvp);
    assert(LL.list_owns_element h0 dv0.dv_peers p);
    M.memP_list_in_listP_implies_memP p peers_l0 peers_l1;
    assert(LL.list_owns_element h1 dv1.dv_peers p);
    // Using gsame_elementsp to show that the peer is left unchanged
    let unchanged = remove_peer_unchanged_pred_s idc h0 h1 in
    M.memP_gfor_allP unchanged p peers_l0;
    assert(peer_p_or_null_v h0 p == peer_p_or_null_v h1 p);
    // Proving: elems_invariants h1 peers_l1
    let peers = dv0.dv_peers in
    let sp = LL.stateful_get_prim (idc_stateful_peer_p idc) in
    assert(LL.list_owns_element h1 dv0.dv_peers p);
    LL.invariant_implies_elements_invariants h1 dv1.dv_peers;
    assert(LL.elems_invariants h1 peers_l1);
    // Proving peer_p_invariant by using the fact:
    // device_p_invariant ==> all peers' invariants stand ==> p's invariant stands
    let inv_free = LL.dt_inv_free h1 in
    assert(M.gfor_allP inv_free peers_l1);
    M.memP_gfor_allP inv_free p peers_l1;
    assert(peer_p_invariant h1 p);
    assert(device_p_owns_peer h1 dvp p);
    assert(peer_p_live h1 p) // given by the peer invariant
    end

let peer_p_or_null_removed_peer_frame_invariant #idc pid p dvp h0 h1 =
  if peer_p_g_is_null p then ()
  else
    begin
    let dv0 = B.deref h0 dvp.dvp in
    let dv1 = B.deref h1 dvp.dvp in
    let peers_l0 = device_p_g_get_peers h0 dvp in
    let peers_l1 = device_p_g_get_peers h1 dvp in
    // From the definition of device_p_removed_peer
    let pattern = idc_get_pattern idc in
    let peers_have_s = with_onorm(peers_have_s pattern) in
    let is_psk = with_onorm(check_hsk_is_psk pattern) in
    let nc = idc_get_nc idc in
    let pid_cl = idc_get_pid idc in
    let pinfo = (idc_get_info idc).St.smficc_stateful in
    // Same as for no_removal, but only on the peers which id is different from pid
    let dt = idc_stateful_peer_p idc in
    let filter_pred = remove_peer_filter_pred_s idc pid h0 in
    let filtered = M.gfilter_one filter_pred peers_l0 in
    let unchanged = remove_peer_unchanged_pred_s idc h0 h1 in
    assert(M.list_in_listP filtered peers_l1);
    assert(M.gfor_allP unchanged filtered);
    // Targets
    assert(device_p_invariant h1 dvp);
    // The peer is in the filtered list
    M.memP_gfilter_one filter_pred p peers_l0;
    assert(M.memP p filtered);
    // Retrieve the peer invariants for all the peers in peers_l0,
    // then show that p satisfies the invariant
    LL.invariant_implies_elements_invariants h1 dv1.dv_peers;
    assert(LL.elems_invariants h1 peers_l1);
    M.gfor_allP_list_in_listP (LL.dt_inv_free h1) filtered peers_l1;
    M.memP_list_in_listP_implies_memP p filtered peers_l1;
    M.memP_gfor_allP (LL.dt_inv_free h1) p peers_l1;
    assert(peer_p_invariant h1 p);
    assert(peer_p_live h1 p); // given by the peer invariant
    // Show that the peer is owned by the device in h1
    assert(LL.list_owns_element h1 dv1.dv_peers p);
    M.memP_gfor_allP unchanged p filtered;
    assert(peer_p_or_null_v h0 p == peer_p_or_null_v h1 p);
    // Proving: elems_invariants h1 peers_l1
    let peers = dv0.dv_peers in
    let sp = LL.stateful_get_prim (idc_stateful_peer_p idc) in
    assert(device_p_owns_peer h1 dvp p)
    end

let _ = ()

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_p_create_no_s
  (#idc : idconfig{not (idc_uses_s idc)})
  (csi:config_impls (idc_get_nc idc)) :
  device_p_create_st idc

let mk_device_p_create_no_s #idc csi r0 cstate prlg_len prlg info sk spriv =
  // We don't allocate directly in the region provided by the user.
  // This allows us to prove that the device footprint is always disjoint
  // from the stack later on. See [device_p_invariant] more more information.
  (**) let h0 = ST.get () in
  (**) let r = ST.new_region r0 in
  (**) let r_dv = ST.new_region r in
  (**) let r_s = ST.new_region r_dv in
  (**) let r_new = ST.new_region r_dv in
  (**) assert(region_includes_region r_dv r_s);
  (**) assert(region_includes_region r_dv r_new);
  (**) assert(region_includes_region r r_s);
  (**) assert(region_includes_region r r_new);
  (**) let r_ptr = ST.new_region r in
  let sk' = lbuffer_or_unit_malloc_copy r_s (u8 0) sk in
  (**) let h1 = ST.get () in
  (**) info_input_frame_invariant B.loc_none info h0 h1;
  let dv = mk_device_t_create #idc r_dv r_s r_new cstate prlg_len prlg info sk' () () in
  let dvp = B.malloc r_ptr dv 1ul in
  let dvp = {
    dvp = dvp;
    dvp_r = r;
  } in
  dvp

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_p_create_has_s
  (#idc : idconfig{idc_uses_s idc})
  (csi:config_impls (idc_get_nc idc)) :
  device_p_create_st idc

#restart-solver
#push-options "--z3rlimit 600"
let mk_device_p_create_has_s #idc csi r0 cstate prlg_len prlg info sk spriv =
  (**) let h0 = ST.get () in
  // We don't allocate directly in the region provided by the user.
  // This allows us to prove that the device footprint is always disjoint
  // from the stack later on. See [device_p_invariant] more more information.
  (**) let r = ST.new_region r0 in
  (**) let r_dv = ST.new_region r in
  (**) let r_s = ST.new_region r_dv in
  (**) let r_new = ST.new_region r_dv in
  (**) assert(region_includes_region r_dv r_s);
  (**) assert(region_includes_region r_dv r_new);
  (**) assert(region_includes_region r r_s);
  (**) assert(region_includes_region r r_new);
  (**) let r_ptr = ST.new_region r in
  let sk' = lbuffer_or_unit_malloc_copy r_s (u8 0) sk in
  let spriv' = lbuffer_or_unit_malloc_copy r_s (u8 0) spriv in
  let spub' : public_key_t_or_unit (idc_get_nc idc) (idc_uses_s idc) =
    lbuffer_or_unit_malloc r_s (u8 0) in  
  let res = idh_sp csi spub' spriv' in
  (**) let h1 = ST.get () in
  begin
  // There are no disjointness hypotheses, so we need to work a bit to make
  // framing succeed.
  (**) let l = B.loc_union (lbuffer_or_unit_to_loc spriv') (lbuffer_or_unit_to_loc spub') in
  (**) assert(B.modifies l h0 h1);
  (**) B.(modifies_only_not_unused_in l h0 h1);
  (**) assert(B.(modifies loc_none h0 h1));
  (**) info_input_frame_invariant B.loc_none info h0 h1
  end;
  match res with
  | CSuccess ->
    let dv = mk_device_t_create #idc r_dv r_s r_new cstate prlg_len prlg info sk' spriv' spub' in
    let dvp = B.malloc r_ptr dv 1ul in
    let dvp = {
      dvp = dvp;
      dvp_r = r;
    } in
    dvp
  | _ ->
    (**) assert(False); // TODO: secret_to_public can actually never fail. Update the signature
    { dvp = B.null; dvp_r = r; }
#pop-options

#restart-solver
#push-options "--z3rlimit 100"
let mk_device_p_create #idc csi r0 cstate prlg_len prlg info sk spriv =
  [@inline_let] let has_s = with_onorm #bool (idc_uses_s idc) in
  if has_s then
    mk_device_p_create_has_s #idc csi r0 cstate prlg_len prlg info sk spriv
  else
    mk_device_p_create_no_s #idc csi r0 cstate prlg_len prlg info sk spriv
#pop-options

val bytes_to_nonce (n8 : lbuffer uint8 (size aead_nonce_size)) :
  Stack aead_nonce_t
  (requires (fun h0 -> live h0 n8))
  (ensures (fun h0 n h1 ->
    h1 == h0 /\
    uint_v n = Spec.bytes_to_nonce (as_seq h0 n8)))

let bytes_to_nonce n8 =
  let nonce = Lib.ByteBuffer.uint_from_bytes_le #U64 n8 in
  Lib.RawIntTypes.u64_to_UInt64 nonce

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
val serialize_bytes
  (idc : idconfig{idc_get_serialize idc})
  (csi:config_impls (idc_get_nc idc))
  (sk : serialize_key_t idc)
  (name : info_input_t idc)
  (inlen : size_t{size_v inlen <= aead_max_input (idc_get_config idc)})    
  (input : lbuffer uint8 inlen)
  (c : buffer uint8{B.length c = size_v inlen + aead_tag_size + aead_nonce_size}) :
  Stack (rtype encrypt_return_type)
  (requires (fun h0 ->
    info_input_invariant h0 name /\
    lbuffer_or_unit_live h0 sk /\ live h0 input /\ B.live h0 c /\
    B.live h0 (entropy_p <: B.buffer (G.erased entropy)) /\
    get_aead_pre (idc_get_nc idc) /\
    B.all_disjoint [lbuffer_or_unit_to_loc sk;
                    info_input_footprint name;
                    loc input;
                    B.loc_buffer c;
                    Lib.Buffer.loc entropy_p]))
  (ensures (fun h0 res h1 ->
    B.modifies (B.loc_union (B.loc_buffer c) (Lib.Buffer.loc entropy_p)) h0 h1 /\
    begin
    let sk_v = lbuffer_or_unit_to_seq h0 sk in
    let name_v = info_input_v h0 name in
    let input_v = as_seq h0 input in
    let c_v = B.as_seq h1 c in
    let entr0 = B.deref h0 (entropy_p <: B.buffer (G.erased entropy)) in
    let c_v', entr1 = Spec.serialize_bytes (idc_get_dc idc) sk_v name_v input_v entr0 in
    c_v == c_v' /\
    G.reveal (B.deref h1 (entropy_p <: B.buffer (G.erased entropy))) == entr1
    end))

let serialize_bytes idc csi sk name inlen input c0 =
  (**) let h0 = ST.get () in
  let name_raw_len, name_raw = (idc_get_info idc).St.smficc_cast_input_to_bytes name in
  let n8 = B.sub c0 0ul (size aead_nonce_size) in
  let c = B.sub c0 (size aead_nonce_size) FStar.UInt32.(inlen +^ aead_tag_vs) in
  crypto_random n8 (size aead_nonce_size);
  let n = bytes_to_nonce n8 in
  (**) let h2 = ST.get () in
  iaead_encrypt #(idc_get_nc idc) csi sk n name_raw_len name_raw inlen input c;
  (**) let h3 = ST.get () in
  // This assertion triggers patterns
  (**) assert(Seq.equal (B.as_seq h3 c0) (Seq.append (B.as_seq h2 n8) (B.as_seq h3 c)))

[@@ noextract_to "Karamel"] inline_for_extraction noextract unfold
val deserialize_bytes
  (idc : idconfig{idc_get_serialize idc})
  (csi:config_impls (idc_get_nc idc))
  (sk : serialize_key_t idc)
  (name : info_input_t idc)
  (outlen : size_t{size_v outlen <= aead_max_input (idc_get_config idc)})
  (out : lbuffer uint8 outlen)
  (c : buffer uint8{B.length c = size_v outlen + aead_tag_size + aead_nonce_size}) :
  Stack (rtype decrypt_return_type)
  (requires (fun h0 ->
    info_input_invariant h0 name /\
    lbuffer_or_unit_live h0 sk /\ live h0 out /\ B.live h0 c /\
    get_aead_pre (idc_get_nc idc) /\
    B.all_disjoint [lbuffer_or_unit_to_loc sk;
                    info_input_footprint name;
                    loc out;
                    B.loc_buffer c]))
  (ensures (fun h0 res h1 ->
    B.modifies (loc out) h0 h1 /\
    begin
    let sk_v = lbuffer_or_unit_to_seq h0 sk in
    let name_v = info_input_v h0 name in
    let c_v = B.as_seq h0 c in
    let out_v = as_seq h1 out in
    match Spec.deserialize_bytes (idc_get_dc idc) sk_v name_v c_v with
    | Some p -> is_success res /\ out_v == p
    | None -> not (is_success res)
    end))

let deserialize_bytes idc csi sk name outlen out c0 =
  (**) let h0 = ST.get () in
  let name_raw_len, name_raw = (idc_get_info idc).St.smficc_cast_input_to_bytes name in
  (**) let h1 = ST.get () in
  let n8 = B.sub c0 0ul (size aead_nonce_size) in
  let c = B.sub c0 (size aead_nonce_size) FStar.UInt32.(outlen +^ aead_tag_vs) in
  let n = bytes_to_nonce n8 in
  iaead_decrypt #(idc_get_nc idc) csi sk n name_raw_len name_raw outlen out c

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_p_create_from_secret_has_s
  (#idc : idconfig{idc_get_serialize idc /\ idc_uses_s idc})
  (csi:config_impls (idc_get_nc idc)) :
  device_p_create_from_secret_st idc

#restart-solver
#push-options "--z3rlimit 600"
let mk_device_p_create_from_secret_has_s #idc csi r0 cstate prlg_len prlg info sk spriv =
  (**) let h0 = ST.get () in
  // We don't allocate directly in the region provided by the user.
  // This allows us to prove that the device footprint is always disjoint
  // from the stack later on. See [device_p_invariant] more more information.
  (**) let r = ST.new_region r0 in
  (**) let r_dv = ST.new_region r in
  (**) let r_s = ST.new_region r_dv in
  (**) let r_new = ST.new_region r_dv in
  (**) assert(region_includes_region r_dv r_s);
  (**) assert(region_includes_region r_dv r_new);
  (**) assert(region_includes_region r r_s);
  (**) assert(region_includes_region r r_new);
  (**) let r_ptr = ST.new_region r in
  let spriv' : private_key_t_or_unit (idc_get_nc idc) (idc_uses_s idc) =
    lbuffer_or_unit_malloc r_s (u8 0) in
  (**) let h1 = ST.get () in
  (**) info_input_frame_invariant B.loc_none info h0 h1;
  // Needed to trigger patterns
  (**) assert(region_includes r0 (lbuffer_or_unit_to_loc spriv'));
  let res0 = deserialize_bytes idc csi sk info (private_key_vs (idc_get_nc idc)) spriv' spriv in
  if not (is_success res0) then
    begin
    lbuffer_or_unit_free spriv';
    { dvp = B.null; dvp_r = r; }
    end
  else
    begin
    let sk' = lbuffer_or_unit_malloc_copy r_s (u8 0) sk in
    let spub' : public_key_t_or_unit (idc_get_nc idc) (idc_uses_s idc) =
      lbuffer_or_unit_malloc r_s (u8 0) in  
    let res1 = idh_sp csi spub' spriv' in
    (**) let h2 = ST.get () in
    (**) begin
    (**) let l = B.loc_union (lbuffer_or_unit_to_loc spriv') (lbuffer_or_unit_to_loc spub') in
    (**) assert(B.modifies l h0 h2);
    (**) B.(modifies_only_not_unused_in l h0 h2);
    (**) assert(B.(modifies loc_none h0 h2));
    (**) info_input_frame_invariant B.loc_none info h0 h2;
    (**) assert(res1 == CSuccess)
    (**) end;
    let dv = mk_device_t_create #idc r_dv r_s r_new cstate prlg_len prlg info sk' spriv' spub' in
    let dvp = B.malloc r_ptr dv 1ul in
    let dvp = {
      dvp = dvp;
      dvp_r = r;
    } in
    dvp
    end
#pop-options

#restart-solver
#push-options "--z3rlimit 100"
let mk_device_p_create_from_secret #idc csi r0 cstate prlg_len prlg info sk spriv =
  [@inline_let] let has_s = with_onorm #bool (idc_uses_s idc) in
  if has_s then
    mk_device_p_create_from_secret_has_s #idc csi r0 cstate prlg_len prlg info sk spriv
  else
    mk_device_p_create_no_s #idc csi r0 cstate prlg_len prlg info sk spriv
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_t_free (#idc : idconfig) (dv : device_t idc) :
  ST unit
  (requires (fun h0 ->
    device_t_invariant h0 dv))
  (ensures (fun h0 _ h1 ->
    B.(modifies (device_t_footprint dv) h0 h1)))

#restart-solver
let mk_device_t_free #idc dv =
  (idc_get_info idc).St.smficc_free () dv.dv_info;
  LL.free dv.dv_peers;
  lbuffer_or_unit_free dv.dv_spriv;
  lbuffer_or_unit_free dv.dv_spub;
  if not (is_null dv.dv_prologue.buffer) then B.free (dv.dv_prologue.buffer <: buffer uint8)

let mk_device_p_free #idc dvp =
  let dv = B.index dvp.dvp 0ul in
  mk_device_t_free dv;
  B.free dvp.dvp

(**** Peer lookup *)
#push-options "--ifuel 1"
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val peer_has_id :
     #idc:idconfig
  -> dv:device_t idc
  -> id:peer_id_t idc ->
  LL.pred_st #(idc_stateful_peer_p idc) dv.dv_peers B.loc_none (fun _ -> True) (fun _ _ -> ())
             (Spec.peer_has_id #(idc_get_dc idc) (peer_id_v id))
#pop-options

let peer_has_id #idc dv id =
  fun (xp : peer_p idc) ->
  let x = B.index xp.pp 0ul in
  (**) (idc_get_pid idc).id_v_injective_lem x.p_id id;
  x.p_id = id

/// Same as [peer_p_or_null_invariant], but with a [device_t]
let peer_p_or_null_device_t_invariant
  (#idc : idconfig) (h : mem) (p : peer_p_or_null idc)
  (dv : device_t idc) :
  GTot Type0 =
  peer_p_live h p /\
  device_t_invariant h dv /\
  begin
  if peer_p_g_is_null p then True
  else
    begin
    peer_p_invariant h p /\
    device_t_owns_peer h dv (Some p)
    end
  end

/// Lookup by using the id
/// Note that we don't use [peer_id_t] on purpose: the end user, not
/// working in F*, might give 0 as input.
#push-options "--ifuel 1"
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_t_lookup_peer_by_id :
     #idc:idconfig
  -> dv:device_t idc
  -> id:(idc_get_pid idc).id_t ->
  Stack (peer_p_or_null idc)
  (requires (fun h0 ->
    device_t_invariant h0 dv))
  (ensures (fun h0 p h1 ->
    B.(modifies loc_none h0 h1) /\
    peer_p_or_null_device_t_invariant h1 p dv /\
    device_t_invariant h1 dv /\  // Not necessary, but helps the proofs
    device_t_v h1 dv == device_t_v h0 dv /\ // Not necessary, but helps the proofs
    begin
    let id_v = peer_id_opt_v id in
    if None? id_v then peer_p_g_is_null p else
    let r_v = Spec.lookup_peer_by_id (device_t_v h0 dv) (peer_id_v id) in
    if peer_p_g_is_null p then r_v == None
    else
      Some? r_v /\ peer_p_v h1 p == Some?.v r_v /\
      peer_p_g_get_id h1 p == peer_id_v #idc id
    end))
#pop-options

#push-options "--ifuel 1"
let mk_device_t_lookup_peer_by_id #idc dv id =
  (**) let h0 = ST.get () in
  [@inline_let]
  let return_type : LL.find_return_type (idc_stateful_peer_p idc) =
    let open Impl.Noise.LinkedList in {
    f_rty = peer_p_or_null idc;
    f_g_get_elem = (fun p -> if B.g_is_null p.pp then None else Some p);
    f_from_elem = (fun p -> p);
    f_no_elem = { pp = B.null; pp_r = root; };
  } in

  if id = (idc_get_pid idc).id_none then { pp = B.null; pp_r = root; }
  else
    begin
    begin
    (**) let dv_v = device_t_v h0 dv in
    (**) match peer_id_opt_v id with
    (**) | None -> ()
    (**) | Some id_v -> lookup_peer_by_id_same_id dv_v id_v
    end;
    LL.find
      #(idc_stateful_peer_p idc) dv.dv_peers
      #(fun _ -> True) #(fun _ _ -> ())
      #(Spec.peer_has_id #(idc_get_dc idc) (peer_id_v id))
      return_type
      (peer_has_id #idc dv id)
    end
#pop-options

let mk_device_p_lookup_peer_by_id #idc dvp id =
  let dv = B.index dvp.dvp 0ul in
  mk_device_t_lookup_peer_by_id dv id

/// Lookup by using the static key
#push-options "--ifuel 1"
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_t_lookup_peer_by_static :
     #idc:idconfig{idc_peers_have_s idc}
  -> dv:device_t idc
  -> s:public_key_t (idc_get_nc idc) ->
  Stack (peer_p_or_null idc)
  (requires (fun h0 ->
    device_t_invariant h0 dv /\
    live h0 s))
  (ensures (fun h0 p h1 ->
    B.(modifies loc_none h0 h1) /\
    peer_p_or_null_device_t_invariant h1 p dv /\
    device_t_invariant h1 dv /\  // Not necessary, but helps the proofs
    device_t_v h1 dv == device_t_v h0 dv /\ // Not necessary, but helps the proofs
    begin
    let r_v = Spec.lookup_peer_by_static (device_t_v h0 dv) (as_seq h0 s) in
    if peer_p_g_is_null p then r_v == None
    else
      Some? r_v /\ peer_p_v h1 p == Some?.v r_v
    end))
#pop-options

#push-options "--ifuel 1"
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val peer_has_s :
     #idc:idconfig{idc_peers_have_s idc}
  -> h0:mem
  -> dv:device_t idc
  -> s:public_key_t (idc_get_nc idc) ->
  LL.pred_st #(idc_stateful_peer_p idc) dv.dv_peers B.loc_none
             (fun h1 -> live h0 s /\ live h1 s /\ as_seq h0 s == as_seq h1 s)
             (fun _ _ -> ()) (Spec.peer_has_s #(idc_get_dc idc) (as_seq h0 s))
#pop-options

#push-options "--ifuel 1"
let peer_has_s #idc h00 dv s =
  fun (xp : peer_p idc) ->
  (**) let h0 = ST.get () in
  [@inline_let] let peer_st = LL.stateful_get_prim (idc_stateful_peer_p idc) in
  let x : peer_t idc = B.index xp.pp 0ul in
  [@inline_let]
  let x_p_s = x.p_s in
  (**) let h1 = ST.get () in
  (**) peer_st.St.frame_invariant B.loc_none xp h0 h1;
  (**) assert(peer_st.St.v () h0 xp == peer_st.St.v () h1 xp);
  (**) assert(as_seq h00 s == as_seq h1 s);
  begin
  (**) let peer_v : peer (idc_get_dc idc) = peer_st.St.v () h0 xp in
  (**) let s_v = as_seq h00 s in
  (**) assert(Spec.peer_has_s #(idc_get_dc idc) s_v peer_v <==> peer_v.Spec.p_s == Some s_v)
  end;
  let b = lbytes_eq x_p_s s in
  (**) assert(b = Spec.peer_has_s #(idc_get_dc idc) (as_seq h00 s) (peer_st.St.v () h0 xp));
  b
#pop-options

#restart-solver
#push-options "--ifuel 1"
let mk_device_t_lookup_peer_by_static #idc dv s =
  (**) let h0 = ST.get () in
  [@inline_let]
  let return_type : LL.find_return_type (idc_stateful_peer_p idc) =
    let open Impl.Noise.LinkedList in {
    f_rty = peer_p_or_null idc;
    f_g_get_elem = (fun p -> if B.g_is_null p.pp then None else Some p);
    f_from_elem = (fun p -> p);
    f_no_elem = { pp = B.null; pp_r = root; };
  } in
  LL.find
    #(idc_stateful_peer_p idc)
    dv.dv_peers
    #(fun h1 -> live h0 s /\ live h1 s /\ as_seq h0 s == as_seq h1 s)
    #(fun _ _ -> ())
    #(Spec.peer_has_s #(idc_get_dc idc) (as_seq h0 s))
    return_type
    (peer_has_s #idc h0 dv s)
#pop-options

let mk_device_p_lookup_peer_by_static #idc dvp s =
  let dv = B.index dvp.dvp 0ul in
  mk_device_t_lookup_peer_by_static dv s


(**** Add peer *)

/// A small helper (again): add a peer under the assumption that its static key hasn't
/// been already registered and that the counter is not saturated. We thus don't
/// perform any checks and directly add the peer.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_p_add_peer_get_no_checks (#idc : valid_idc) :
     dvp:device_p idc
  // The device should already have been dereferenced, so we don't only
  // take the pointer, to prevent two dereferences
  -> dv:device_t idc
  -> pinfo:info_input_t idc
  -> rs:idc_rs_t idc
  -> psk:idc_psk_t idc ->
  ST (peer_p_or_null idc)
  (requires (fun h0 ->
    device_p_add_peer_get_st_pre dvp pinfo rs psk h0 /\
    dv == B.deref h0 dvp.dvp /\
    // The counter is not saturated
    dv.dv_peers_counter <> (idc_get_pid idc).id_max /\
    // No other peers has the key
    begin
    let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
    let dvp_v = device_p_v h0 dvp in
    match rs_v with
    | None -> True
    | Some rs_v -> None? (Spec.lookup_peer_by_static dvp_v rs_v)
    end))
  (ensures (fun h0 p h1 ->
    device_p_add_peer_get_st_post dvp pinfo rs psk h0 p h1))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let mk_device_p_add_peer_get_no_checks #idc dvp dv pinfo rs psk =
  (**) let h0 = ST.get () in
  [@inline_let]
  let Mkdevice_t_raw info sk spriv spub prologue scounter peers pcounter cstate = dv in
  [@inline_let] let pid = pcounter in
  [@inline_let] let peer_p_st = LL.stateful_get_prim (idc_stateful_peer_p idc) in
  [@inline_let]
  let p = { p_id = pid; p_info = pinfo; p_s = rs; p_psk = psk; } in
  let pp = LL.push peers p in
  (**) let h1 = ST.get () in
  (**) assert(LL.get_elems h1 peers == pp :: LL.get_elems h0 peers);

  begin
  (**) let peers_v0 = LL.v h0 peers in
  (**) let peers_v1 = LL.v h1 peers in
  (**) assert(peers_v1 == LL.elems_v h1 (LL.get_elems h1 peers));
  (**) assert(peers_v1 == LL.elems_v h1 (pp :: LL.get_elems h0 peers));
  // This one is non trivial, and is currently given by the spec of LL.push
  (**) assert(peers_v1 == peer_p_v #idc h1 pp :: peers_v0)
  end;
  [@inline_let]
  let pcounter' = (idc_get_pid idc).id_increment pcounter in
  [@inline_let]
  let dv1 = Mkdevice_t_raw info sk spriv spub prologue scounter peers pcounter' cstate in
  begin
  (**) let peers_l0 = device_p_g_get_peers h0 dvp in
  (**) let peers_l1 = device_p_g_get_peers h1 dvp in
  (**) assert(device_p_only_changed_peers_or_counters dvp h0 h1);
  (**) M.list_in_listP_refl peers_l0;
  (**) M.list_in_listP_append peers_l0 peers_l0 pp;
  (**) assert(M.list_in_listP peers_l0 peers_l1);
  // Comes from the post-condition of push
  (**) assert(LL.gsame_elementsp peers_l0 h0 h1);
  (**) let pinfo_v = info_input_v h0 pinfo in
  (**) let rs_v = lbuffer_or_unit_to_opt_lseq h0 rs in
  (**) let psk_v = lbuffer_or_unit_to_opt_lseq h0 psk in
  (**) let dv_v1 = device_t_v h0 dv in
  (**) add_peer_get_invariant_preservation_lem dv_v1 pinfo_v rs_v psk_v;
  (**) let res = add_peer_get dv_v1 pinfo_v rs_v psk_v in
  (**) assert(Some? res);
  (**) let Some (pp_v, dv'_v) = res in
  (**) assert(dv_peers_counter_invariant dv'_v);
  // This assert requires some fuel because of the peer list
  (**) let dv0_v = device_t_v h0 dv in
  (**) let dv1_v = device_t_v h1 dv1 in
  (**) assert(dv'_v.Spec.dv_peers == dv1_v.Spec.dv_peers);
  (**) assert(dv'_v.Spec.dv_peers_counter == dv1_v.Spec.dv_peers_counter);
  (**) assert(dv'_v == dv1_v);
  (**) assert(device_t_invariant h1 dv1)
  end;
  B.upd dvp.dvp 0ul dv1;
  (**) let h2 = ST.get () in
  begin
  (**) peer_p_st.St.frame_invariant (B.loc_buffer dvp.dvp) pp h1 h2;
  (**) assert(device_p_only_changed_peers_or_counters dvp h1 h2);
  (**) assert(peers_counter_invariant #idc (peer_id_v pcounter') (LL.v h1 peers));
  (**) device_t_frame_invariant (B.loc_buffer dvp.dvp) dv1 h1 h2;
  (**) assert(device_p_invariant h2 dvp);
  // We can't prove [device_p_no_removal h1 h2] because dvp doesn't
  // satisfy the device invariant in h1. We can however prove the important
  // sub-assertions of this predicate.
  (**) let peers_l0 = device_p_g_get_peers h0 dvp in
  (**) let peers_l1 = device_p_g_get_peers h1 dvp in
  (**) let peers_l2 = device_p_g_get_peers h2 dvp in
  (**) assert(M.list_in_listP peers_l1 peers_l2);
  (**) assert(LL.gsame_elementsp peers_l1 h1 h2);
  // This assert requires some fuel
  (**) assert(LL.list_owns_element h2 dv.dv_peers pp);
  (**) assert(device_p_owns_peer h2 dvp pp);
  (**) assert(peer_p_v h2 pp == peer_p_v #idc h1 pp);
  (**) LL.frame_invariant peers (B.loc_buffer dvp.dvp) h1 h2;
  (**) assert(M.list_in_listP peers_l0 peers_l2);
  (**) LL.gsame_elementsp_trans peers_l0 h0 h1 h2;
  (**) assert(LL.gsame_elementsp peers_l0 h0 h2);
  (**) assert(device_p_no_removal dvp h0 h2)
  end;
  pp
#pop-options

let mk_device_p_add_peer_get #idc dvp pinfo rs psk =
  (**) let h0 = ST.get () in
  let dv = B.index dvp.dvp 0ul in
  [@inline_let]
  let Mkdevice_t_raw info sk spriv spub prologue scounter peers pcounter cstate = dv in
  [@inline_let] let pid = pcounter in
  [@inline_let] let pinfo_st = (idc_get_info idc).St.smficc_input in
  (* Check if the counter is saturated *)
  let b1 = (pid = with_onorm (peer_id_max idc)) in
  (* Check if there is already a peer with the same static key *)
  let b2 =
    if idc_peers_have_s idc
    then not (peer_p_is_null (mk_device_t_lookup_peer_by_static dv rs))
    else false in
  (**) let h1 = ST.get () in
  // We don't need to call the frame invariant to frame the invariant, but to
  // get device_p_no_removal
  (**) device_p_frame_invariant B.loc_none dvp h0 h1;
  (**) assert(device_p_no_removal dvp h0 h1);
  (**) assert(device_t_invariant h1 dv);
  if b1 || b2 then
    (* Do nothing *)
    { pp = null #MUT #_; pp_r = HS.get_tip h0; } // the region is dummy
  else
    begin
    begin
    (**) assert(B.(modifies loc_none h0 h1));
    (**) pinfo_st.St.frame_invariant B.loc_none pinfo h0 h1
    end;
    let pp = mk_device_p_add_peer_get_no_checks dvp dv pinfo rs psk in
    (**) let h2 = ST.get () in
    begin
    (**) device_p_no_removal_trans_lem dvp h0 h1 h2;
    (**) assert(device_p_no_removal dvp h0 h2)
    end;
    pp
    end

let mk_device_p_add_peer #idc dvp pinfo rs psk =
  let p = mk_device_p_add_peer_get dvp pinfo rs psk in
  if peer_p_is_null p then peer_id_none idc
  else
    mk_peer_p_get_id p

(**** Remove peer *)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val mk_device_t_remove_peer :
     #idc:idconfig
  -> dv:device_t idc
  // We take a non-0 id: it is tested in mk_device_p_remove_peer
  -> pid:peer_id_t idc ->
  ST unit
  (requires (fun h0 ->    
    device_t_invariant h0 dv))
  (ensures (fun h0 b h1 ->
    B.(modifies (device_t_footprint dv) h0 h1) /\
    device_t_invariant h1 dv /\
    device_t_removed_peer dv (peer_id_v pid) h0 h1 /\
    begin
    let dv0_v = device_t_v h0 dv in
    let dv1_v = device_t_v h1 dv in
    dv1_v == remove_peer dv0_v (peer_id_v pid)
    end))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val peer_has_not_id :
     #idc:idconfig
  -> dv:device_t idc
  -> pid:peer_id_t idc ->
  LL.pred_st #(idc_stateful_peer_p idc) dv.dv_peers (LL.region_of dv.dv_peers)
             (fun _ -> True)
             (fun _ _ -> ()) (Spec.peer_has_not_id #(idc_get_dc idc) (peer_id_v pid))

let peer_has_not_id #idc dv pid =
  fun (xp : peer_p idc) ->
  let x = B.index xp.pp 0ul in
  (**) (idc_get_pid idc).id_v_injective_lem x.p_id pid;
  x.p_id <> pid

/// Small helper lemma

val mk_device_t_remove_peer_fspec_lem
  (#idc : idconfig) (pid : peer_id) (h0 h1 : mem)
  (ll0 : list (peer_p idc)) :
  Lemma
  (requires (
    let dt = idc_stateful_peer_p idc in
    let fspec = Spec.peer_has_not_id #(idc_get_dc idc) pid in
    let filtered = LL.gfilter_one_element #dt fspec h0 ll0 in
    LL.gsame_elementsp #dt filtered h0 h1))
  (ensures (
    let dt = idc_stateful_peer_p idc in
    let filter_pred = remove_peer_filter_pred_s idc pid h0 in
    let fspec = Spec.peer_has_not_id #(idc_get_dc idc) pid in
    let filtered0 = LL.gfilter_one_element #dt fspec h0 ll0 in
    let filtered1 = M.gfilter_one filter_pred ll0 in
    let unchanged_pred = remove_peer_unchanged_pred_s idc h0 h1 in
    filtered1 == filtered0 /\
    M.gfor_allP unchanged_pred filtered1))

/// The small helper lemma has a cute little brother
val gsame_elementsp_implies_remove_peer_unchanged_pred_s
  (#idc : idconfig) (h0 h1 : mem) (ll : list (peer_p idc)) :
  Lemma (requires (
    let dt = idc_stateful_peer_p idc in
    LL.gsame_elementsp #dt ll h0 h1))
  (ensures (M.gfor_allP (remove_peer_unchanged_pred_s idc h0 h1) ll))

#push-options "--fuel 1 --ifuel 1"
let rec gsame_elementsp_implies_remove_peer_unchanged_pred_s #idc h0 h1 ll =
  let dt = idc_stateful_peer_p idc in
  match ll with
  | [] -> ()
  | x :: ll' -> gsame_elementsp_implies_remove_peer_unchanged_pred_s #idc h0 h1 ll'
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec mk_device_t_remove_peer_fspec_lem #idc pid h0 h1 ll0 =
  match ll0 with
  | [] -> ()
  | x :: ll0' ->
    let dt = idc_stateful_peer_p idc in
    let fspec = Spec.peer_has_not_id #(idc_get_dc idc) pid in
    let filtered = LL.gfilter_one_element #dt fspec h0 ll0 in
    // Can it be more annoying?...
    assert_norm(LL.filter_pred #dt fspec h0 x = G.reveal fspec (LL.dt_v #dt h0 x));
    if fspec (LL.dt_v #dt h0 x) then
      begin
      mk_device_t_remove_peer_fspec_lem pid h0 h1 ll0'
      end
    else
      begin
      let unchanged_pred = remove_peer_unchanged_pred_s idc h0 h1 in
      gsame_elementsp_implies_remove_peer_unchanged_pred_s #idc h0 h1 filtered;
      assert(M.gfor_allP unchanged_pred filtered)
      end
#pop-options

let mk_device_t_remove_peer #idc dv pid =
  (**) let h0 = ST.get () in
  [@inline_let]
  let Mkdevice_t_raw info sk spriv spub prologue scounter peers pcounter cstate = dv in

  LL.filter_one dv.dv_peers (peer_has_not_id #idc dv pid);
  (**) let h1 = ST.get () in
  // This assertion comes from the post of [filter_one] "as is", but at some point
  // caused trouble because of the SMT encoding. See the comments for
  // [Impl.Noise.LinkedList.filter_one_st_post] for more details.
  (**) assert(LL.v h1 peers == M.filter_one (Spec.peer_has_not_id #(idc_get_dc idc) (peer_id_v pid)) (LL.v h0 peers));

  (**) mk_device_t_remove_peer_fspec_lem #idc (peer_id_v pid) h0 h1 (LL.get_elems h0 peers);
  (**) remove_peer_invariant_lem (device_t_v h0 dv) (peer_id_v pid);

  (**) assert(peers_counter_invariant #idc (peer_id_v pcounter) (LL.v h1 peers));
  (**) assert(peers_pairwise_distinct_ids #idc (LL.v h1 peers));
  (**) assert(peers_pairwise_distinct_statics #idc (LL.v h1 peers));
  (**) assert(device_t_invariant h1 dv);
  begin
  (**) let dv0_v = device_t_v h0 dv in
  (**) let dv1_v = device_t_v h1 dv in
  (**) let dv1'_v = remove_peer dv0_v (peer_id_v pid) in
  (**) (* We need to trigger sequence patterns *)
  (**) assert(Seq.equal dv1_v.Spec.dv_prologue dv0_v.Spec.dv_prologue);
  (**) assert(dv1_v.Spec.dv_prologue == dv1'_v.Spec.dv_prologue);
  (**) (* Proving device_t_removed_peer *)
  (**) let pid = peer_id_v pid in
  (**) let fspec = Spec.peer_has_not_id #(idc_get_dc idc) pid in
  (**) let dt = idc_stateful_peer_p idc in
  (**) let filter_pred = remove_peer_filter_pred_s idc pid h0 in
  (**) let filtered = M.gfilter_one filter_pred (device_t_g_get_peers h0 dv) in
  (**) let unchanged_pred = remove_peer_unchanged_pred_s idc h0 h1 in
  (**) assert(filtered == LL.gfilter_one_element fspec h0 (LL.get_elems h0 dv.dv_peers));
  (**) assert(filtered == device_t_g_get_peers h1 dv);
  (**) M.list_in_listP_refl filtered;
  (**) assert(M.list_in_listP filtered (device_t_g_get_peers h1 dv));
  (**) assert(M.gfor_allP unchanged_pred filtered);
  (**) assert(device_t_only_changed_peers_or_counters dv h0 h1);
  (**) assert(device_t_invariant h0 dv);
  (**) assert(device_t_invariant h1 dv);
  (**) assert(device_t_removed_peer dv pid h0 h1)
  end

let mk_device_p_remove_peer #idc dvp pid =
  (**) let h0 = ST.get () in
  if pid = with_onorm ((idc_get_pid idc).id_none)
  then
    // The frame invariant gives us that there are no removal...
    device_p_frame_invariant B.loc_none dvp h0 h0
  else
    begin
    let dv = B.index dvp.dvp 0ul in
    mk_device_t_remove_peer dv pid;
    (**) let h2 = ST.get () in
    begin
    (**) let pid_v = peer_id_v #idc pid in
    (**) assert(device_p_removed_peer dvp pid_v h0 h2)
    end
    end

(*** Serialization/deserialization *)

let mk_device_p_serialize_device_secret #idc csi r outlen out dvp =
  (**) let h0 = ST.get () in
  let dv = B.index dvp.dvp 0ul in
  [@inline_let] let len = enc_private_key_with_nonce_vs (idc_get_nc idc) in
  (**) assert(size_v len > 0);
  let outb = B.malloc r (u8 0) len in
  (**) assert(region_includes r (B.loc_addr_of_buffer outb));
  let name = (idc_get_info idc).St.smficc_input_from_output () dv.dv_info in
  serialize_bytes idc csi dv.dv_sk name (private_key_vs (idc_get_nc idc)) dv.dv_spriv outb;
  B.upd out 0ul outb;
  B.upd outlen 0ul len;
  (**) let h1 = ST.get () in
  (**) begin
  (**) let l = B.(loc_union (loc_union (loc_buffer outlen) (loc_buffer out))
                            (Lib.Buffer.loc entropy_p)) in
  (**) B.modifies_only_not_unused_in l h0 h1;
  (**) assert(B.modifies l h0 h1)
  (**) end

#restart-solver
#push-options "--z3rlimit 800"
let mk_device_p_serialize_peer_secret #idc csi r outlen out dvp peer =
  (**) let h0 = ST.get () in
  if peer_p_is_null peer then
    begin
    B.upd outlen 0ul 0ul;
    B.upd out 0ul B.null
    end
  else
    begin
    let dv = B.index dvp.dvp 0ul in
    let p = B.index peer.pp 0ul in
    [@inline_let] let keys_length0 = if idc_peers_have_s idc then public_key_vsv (idc_get_nc idc) else 0 in
    [@inline_let] let keys_length = if idc_is_psk idc then keys_length0 + preshared_key_vsv else keys_length0 in
    [@inline_let] let length = keys_length + aead_tag_vsv + aead_nonce_size in
    [@inline_let] let keys_len = size keys_length in
    [@inline_let] let len = size length in
    // TODO: this should be allocated on the stack
    let concat_keys = B.malloc r (u8 0) keys_len in
    let outb = B.malloc r (u8 0) len in
    if idc_peers_have_s idc then
      B.blit (lbuffer_or_unit_to_buffer p.p_s) 0ul concat_keys 0ul (public_key_vs (idc_get_nc idc));
    if idc_is_psk idc then
      B.blit (lbuffer_or_unit_to_buffer p.p_psk) 0ul concat_keys (size keys_length0) preshared_key_vs;
    (**) let h1 = ST.get () in
    // This assertion triggers patternsg
    (**) begin
    (**) let spriv_v = lbuffer_or_unit_to_seq h0 p.p_s in
    (**) let psk_v = lbuffer_or_unit_to_seq h0 p.p_psk in
    (**) assert(Seq.equal (B.as_seq h1 concat_keys) (Seq.append spriv_v psk_v));
    (**) assert(region_includes r (B.loc_addr_of_buffer concat_keys));
    (**) assert(region_includes r (B.loc_addr_of_buffer outb))
    (**) end;
    let name = (idc_get_info idc).St.smficc_input_from_output () p.p_info in
    serialize_bytes idc csi dv.dv_sk name keys_len concat_keys outb;
    B.upd out 0ul outb;
    B.upd outlen 0ul len;
    B.free concat_keys;
    (**) let h2 = ST.get () in
    (**) begin
    (**) let l = B.(loc_union (loc_union (loc_buffer outlen) (loc_buffer out))
                              (Lib.Buffer.loc entropy_p)) in
    (**) B.modifies_only_not_unused_in l h0 h2;
    (**) assert(B.modifies l h0 h2)
    (**) end
    end
#pop-options

#restart-solver
#push-options "--z3rlimit 400"
let mk_device_p_deserialize_peer_secret #idc csi r dvp peer_name inlen enc_keys =
  (**) let h0 = ST.get () in
  let dv = B.index dvp.dvp 0ul in
  [@inline_let] let keys_length0 = if idc_peers_have_s idc then public_key_vsv (idc_get_nc idc) else 0 in
  [@inline_let] let keys_length = if idc_is_psk idc then keys_length0 + preshared_key_vsv else keys_length0 in
  [@inline_let] let length = keys_length + aead_tag_vsv + aead_nonce_size in
  [@inline_let] let keys_len = size keys_length in
  [@inline_let] let len = size length in
  (**) let h1 = ST.get () in
  // The frame invariant gives us device_p_no_removal
  (**) device_p_frame_invariant B.loc_none dvp h0 h1;
  if len <> inlen then peer_p_null idc
  else
  begin
  // TODO: morally, this should be allocated on the stack. But we need to prove
  // it is disjoint from the input peer name. We could add an assumption.
  let concat_keys : B.buffer uint8 = B.malloc r (u8 0) keys_len in
  (**) assert(size_v keys_len <= aead_max_input (idc_get_config idc));
  (**) assert(B.length concat_keys == size_v keys_len);
  (**) let h2 = ST.get () in
  (**) info_input_frame_invariant B.loc_none peer_name h0 h2;
  (**) assert(region_includes r (B.loc_addr_of_buffer concat_keys));
  let res = deserialize_bytes idc csi dv.dv_sk peer_name keys_len concat_keys enc_keys in
  (**) let h3 = ST.get () in
  if is_success res then
    begin
    // Get the keys
    let p_s = // : public_key_t_or_unit (idc_get_nc idc) (idc_peers_have_s idc) =
      sub_or_unit (idc_peers_have_s idc) concat_keys 0ul (public_key_vs (idc_get_nc idc)) in
    let p_psk =
      sub_or_unit (idc_is_psk idc) concat_keys (size keys_length0) preshared_key_vs in
    // This assertion triggers patternsg
    (**) begin
    (**) let s_v = lbuffer_or_unit_to_seq h3 p_s in
    (**) let psk_v = lbuffer_or_unit_to_seq h3 p_psk in
    (**) assert(Seq.equal (B.as_seq h3 concat_keys) (Seq.append s_v psk_v));
    (**) assert(region_includes r (lbuffer_or_unit_to_loc p_s));
    (**) assert(region_includes r (lbuffer_or_unit_to_loc p_psk))
    (**) end;
    (**) B.(modifies_only_not_unused_in loc_none h0 h3);
    (**) info_input_frame_invariant B.loc_none peer_name h0 h3;
    let peer = mk_device_p_add_peer_get dvp peer_name p_s p_psk in
    (**) let h4 = ST.get () in
    B.free concat_keys;
    (**) let h5 = ST.get () in
    (**) B.(modifies_only_not_unused_in (device_p_region_of dvp) h0 h5);
    (**) device_p_no_removal_trans_lem dvp h0 h3 h4;
    (**) device_p_no_removal_trans_lem dvp h0 h4 h5;
    peer
    end
  else
    begin
    B.free concat_keys;
    (**) let h4 = ST.get () in
    (**) B.(modifies_only_not_unused_in loc_none h0 h4);
    peer_p_null idc
    end
  end
#pop-options
