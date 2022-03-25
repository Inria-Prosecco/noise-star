module Impl.Noise.LinkedList

/// A Low*, stateful linked list containing stateful data

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module ST = FStar.HyperStack.ST

module LL2 = LowStar.Lib.LinkedList2
module LL1 = LowStar.Lib.LinkedList

open FStar.HyperStack.ST
open LowStar.BufferOps
open Impl.Noise.Stateful
open Spec.Noise.Map

#set-options "--z3rlimit 25 --fuel 0 --ifuel 0"

/// Types, invariants
/// -----------------

val _align_beg : unit

inline_for_extraction noextract
let stateful = stateful_malloc_from_input

inline_for_extraction noextract
let stateful_get_prim (st : stateful unit) =
  st.smfi_stateful

inline_for_extraction noextract
let dt_s (dt : stateful unit) : Type0 = dt.smfi_stateful.s ()

inline_for_extraction noextract
let dt_t (dt : stateful unit) : Type0 = dt.smfi_stateful.t ()

inline_for_extraction noextract
let dt_v (#dt : stateful unit) : HS.mem -> x:dt_s dt -> GTot (dt_t dt) =
  dt.smfi_stateful.v ()

inline_for_extraction noextract
let dt_footprint (#dt : stateful unit) : x:dt_s dt -> GTot B.loc =
  dt.smfi_stateful.footprint

inline_for_extraction noextract
let dt_invariant (#dt : stateful unit) : HS.mem -> x:dt_s dt -> GTot Type0 =
  dt.smfi_stateful.invariant

inline_for_extraction noextract
let dt_freeable (#dt : stateful unit) : HS.mem -> x:dt_s dt -> GTot Type0 =
  dt.smfi_stateful.freeable

let dt_frame_invariant (#dt : stateful unit) (l : B.loc) (x:dt_s dt) =
  dt.smfi_stateful.frame_invariant l x

let dt_frame_freeable (#dt : stateful unit) (l : B.loc) (x:dt_s dt) =
  dt.smfi_stateful.frame_freeable l x

inline_for_extraction noextract
let dt_malloc #dt = dt.smfi_malloc ()

inline_for_extraction noextract
let dt_free #dt = dt.smfi_free ()

inline_for_extraction noextract
val t: stateful unit -> Type0

let elems_v: #dt:stateful unit -> h:HS.mem -> ll:list (dt_s dt) -> GTot (list (dt_t dt)) =
  fun #dt h ll ->
  gmap (fun x -> dt_v h x) ll

/// Getting the list of stateful elements stored in the list
val get_elems: #dt:stateful unit -> h:HS.mem -> ll:t dt -> GTot (list (dt_s dt))

/// Reflecting a stateful, imperative list as a functional one in a given heap.
let v: #dt:stateful unit -> h:HS.mem -> ll:t dt -> GTot (list (dt_t dt)) =
  fun #dt h ll ->
  elems_v h (get_elems h ll)

/// Whenever we use a function like [gfor_allP], it is better to introduce
/// an auxiliary predicate (otherwise, there are typing problems).
let dt_inv_free (#dt : stateful unit) (h : HS.mem) (x : dt_s dt) : GTot Type0 =
  dt_invariant #dt h x /\
  dt_freeable #dt h x

let elems_invariants: #dt:stateful unit -> h:HS.mem -> elems:list (dt_s dt) -> GTot Type0 =
  fun #dt h elems ->
  gfor_allP (dt_inv_free h) elems

noextract
val invariant: #dt:stateful unit -> h:HS.mem -> ll:t dt -> Type0

val region_of: #dt:stateful unit -> ll:t dt -> GTot B.loc

/// Various predicates
/// ------------------

let gsame_elementp (#dt: stateful unit) (h0 h1: HS.mem) :
  dt_s dt -> GTot Type0 =
  fun x -> dt_v h1 x == dt_v h0 x

let gsame_elementsp (#dt: stateful unit) (ll : list (dt_s dt)) (h0 h1: HS.mem) : GTot Type0 =
  gfor_allP (gsame_elementp h0 h1) ll

val gsame_elementsp_refl
  (#dt : stateful unit) (ll : list (dt_s dt)) (h0 : HS.mem) :
  Lemma
  (requires (elems_invariants h0 ll))
  (ensures (gsame_elementsp ll h0 h0))

val gsame_elementsp_trans (#dt: stateful unit) (ll : list (dt_s dt)) (h0 h1 h2: HS.mem) :
  Lemma
  (requires (gsame_elementsp ll h0 h1 /\ gsame_elementsp ll h1 h2))
  (ensures (gsame_elementsp ll h0 h2))

val gsame_elementsp_list_in_listP_trans
  (#dt: stateful unit) (ll0 ll1 : list (dt_s dt)) (h0 h1 h2: HS.mem) :
  Lemma
  (requires (
    gsame_elementsp ll0 h0 h1 /\
    gsame_elementsp ll1 h1 h2 /\
    list_in_listP ll0 ll1))
  (ensures (gsame_elementsp ll0 h0 h2))

val gsame_elementsp_elems_v_lem (#dt: stateful unit) (ll : list (dt_s dt)) (h0 h1: HS.mem) :
  Lemma
  (requires (gsame_elementsp ll h0 h1))
  (ensures (elems_v h1 ll == elems_v h0 ll))

/// The element [e] is an element in list [ll].
let list_owns_element (#dt: stateful unit) (h: HS.mem) (ll: t dt) (e: dt_s dt) : GTot Type0 =
  memP e (get_elems h ll)

/// Frame invariant
/// ---------------
val frame_invariant: #dt:stateful unit -> ll:t dt -> l:B.loc -> h0:HS.mem -> h1: HS.mem -> Lemma
  (requires
    invariant h0 ll /\
    B.loc_disjoint l (region_of ll) /\
    B.modifies l h0 h1)
  (ensures
    invariant h1 ll /\
    // The list of elements is the same
    get_elems h1 ll == get_elems h0 ll /\
    // The elmements themselves are left unchanged
    gsame_elementsp (get_elems h0 ll) h0 h1 /\
    // The following comes from the two preceding facts, but it is
    // more convenient if it is directly derived here
    v h1 ll == v h0 ll)
  [ SMTPatOr [
      [ SMTPat (invariant h0 ll); SMTPat (B.modifies l h0 h1) ];
    ]]

/// Elements lemmas and predicates
/// -----------------------------

val invariant_implies_elements_invariants :
     #dt:stateful unit
  -> h:HS.mem
  -> ll:t dt ->
  Lemma (requires invariant h ll)
  (ensures elems_invariants h (get_elems h ll))

/// Creating an imperative list
/// ---------------------------

inline_for_extraction noextract
val create_in: #dt:stateful unit -> r:HS.rid -> ST (t dt)
  (requires fun h0 ->
    ST.is_eternal_region r)
  (ensures fun h0 ll h1 ->
    invariant h1 ll /\
    B.(modifies loc_none h0 h1) /\
    v h1 ll == [] /\
    B.(loc_includes (loc_all_regions_from false r) (region_of ll)))

/// Find
/// ----

inline_for_extraction noextract
type fspec_ty (dt : stateful unit) = dt_t dt -> Tot bool

/// Type of a predicate function, used by [find] and [filter].
inline_for_extraction noextract
let pred_st (#dt: stateful unit) (ll: t dt)
            (l : Ghost.erased B.loc)
            (inv : HS.mem -> G.erased Type0)
            (inv_lem : (h0:HS.mem -> h1:HS.mem ->
                        Lemma
                        // Note that we allow the linked list to be modified between
                        // two calls: it is because we use [pred_st] both for [find]
                        // and [filter]
                        (requires (inv h0 /\ B.(modifies l h0 h1) /\ B.(equal_stack_domains h0 h1)))
                        (ensures (inv h1))))
            (spec: G.erased (fspec_ty dt)) =
  x:dt_s dt ->
  Stack bool
  (requires (fun h0 ->
    inv h0 /\
    dt_invariant h0 x /\
    B.loc_includes (region_of ll) (dt_footprint x)))
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\ // This causes trouble because we use while loops
    inv h1 /\
    b = (G.reveal spec) (dt_v h0 x)))

/// The code of the find function can be customized a bit. By default, it is
/// convenient to return an option. However, the elements contained in the
/// list are often pointers, in which case we can simply return NULL if we
/// don't find a peer.

inline_for_extraction noextract
noeq type find_return_type (dt : stateful unit) = {
  // The return type
  f_rty : Type0;
  // Test if an element was found - for writing the specification only
  f_g_get_elem : (r:f_rty -> GTot (option (dt_s dt)));
  // Return an element
  f_from_elem : (e: dt_s dt -> r:f_rty{f_g_get_elem r == Some e});
  // No element found
  f_no_elem : r:f_rty{f_g_get_elem r == None};
}

inline_for_extraction noextract
let find_return_type_option dt =
{
  f_rty = option (dt_s dt);
  f_g_get_elem = (fun r -> r);
  f_from_elem = (fun x -> Some x);
  f_no_elem = None;  
}

/// Small helpers - without those, the code is not normalized correctly
inline_for_extraction noextract
let f_rty (#dt : stateful unit) (rtype : find_return_type dt) =
  match rtype with
  | Mkfind_return_type rty get_elem from_elem no_elem -> rty

inline_for_extraction noextract
let f_get_elem (#dt : stateful unit) (#rtype : find_return_type dt) :
  r:f_rty rtype -> GTot (option (dt_s dt)) =
  match rtype with
  | Mkfind_return_type rty get_elem from_elem no_elem -> get_elem

inline_for_extraction noextract
let f_from_elem (#dt : stateful unit) (#rtype : find_return_type dt) :
  e: dt_s dt -> r:f_rty rtype{rtype.f_g_get_elem r == Some e} =
  match rtype with
  | Mkfind_return_type rty get_elem from_elem no_elem -> from_elem

inline_for_extraction noextract
let f_no_elem (#dt : stateful unit) (#rtype : find_return_type dt) :
  r:f_rty rtype{rtype.f_g_get_elem r == None} =
  match rtype with
  | Mkfind_return_type rty get_elem from_elem no_elem -> no_elem

inline_for_extraction noextract
val find (#dt: stateful unit) (ll: t dt)
         (#inv : HS.mem -> G.erased Type0)
         (#inv_lem : (h0:HS.mem -> h1:HS.mem ->
                      Lemma (requires (inv h0 /\ B.(modifies B.loc_none h0 h1)))
                      (ensures (inv h1))))
         (#fspec : G.erased (fspec_ty dt))
         (rtype : find_return_type dt)
         (f : pred_st ll B.loc_none inv inv_lem fspec) :
  Stack (f_rty rtype)
    (requires fun h0 ->    
      invariant h0 ll /\
      inv h0)
    (ensures fun h0 r h1 ->
      let r_v = L.tryFind fspec (v h0 ll) in
      B.(modifies loc_none h0 h1) /\
      inv h1 /\
      begin match f_get_elem r with
      | None -> r_v == None
      | Some x ->
        r_v == Some (dt_v h1 x) /\
        dt_invariant h1 x /\
        B.loc_includes (region_of ll) (dt_footprint x) /\
        list_owns_element h1 ll x
      end)

/// Adding elements
/// ---------------

inline_for_extraction noextract
val push (#dt: stateful unit) (ll: t dt) (x: dt.smfi_input.s ()) :
  ST (dt_s dt)
    (requires fun h0 ->
      dt.smfi_input.invariant h0 x /\
      invariant h0 ll)
    (ensures fun h0 y h1 ->
      B.(modifies (region_of ll) h0 h1) /\
      dt_invariant h1 y /\
      invariant h1 ll /\
      B.loc_includes (region_of ll) (dt.smfi_stateful.footprint y) /\
      begin
      let x_v = dt.smfi_input.v () h0 x in
      let y_v = dt_v h1 y in
      y_v == x_v /\
      get_elems h1 ll == y :: get_elems h0 ll /\
      gsame_elementsp (get_elems h0 ll) h0 h1 /\
      // This assertion is a consequence of the two previous ones, but is
      // not completely trivial to get and convenient to have
      v h1 ll == y_v :: v h0 ll
      end)

/// Removing elements
/// -----------------

/// [pop] should return the popped element, however dealing with aliasing
/// without copying the element is very difficult.
inline_for_extraction noextract
val pop (#dt: stateful unit) (ll: t dt) :
  ST unit
    (requires fun h0 ->
      invariant h0 ll /\
      Cons? (get_elems h0 ll))
    (ensures fun h0 _ h1 ->
      let tl_elems = L.tl (get_elems h0 ll) in
      B.modifies (region_of ll) h0 h1 /\
      invariant h1 ll /\
      get_elems h1 ll == tl_elems /\
      gsame_elementsp tl_elems h0 h1 /\
      // Consequence of the two previous assertions
      Cons? (v h0 ll) /\
      v h1 ll == L.tl (v h0 ll))

/// Some utilities for filter and filter_one

let filter_pred (#dt: stateful unit) (fspec : G.erased (fspec_ty dt)) (h : HS.mem) :
  dt_s dt -> GTot bool =
  fun x -> G.reveal fspec (dt_v h x)

let gfilter_elements
  (#dt: stateful unit) (fspec : G.erased (fspec_ty dt))
  (h : HS.mem) (ls : list (dt_s dt)) :
  GTot (list (dt_s dt)) =
  gfilter (filter_pred fspec h) ls

let gfilter_one_element
  (#dt: stateful unit) (fspec : G.erased (fspec_ty dt))
  (h : HS.mem) (ls : list (dt_s dt)) :
  GTot (list (dt_s dt)) =
  gfilter_one (filter_pred fspec h) ls

inline_for_extraction noextract
type filter_st =
     #dt: stateful unit
  -> ll: t dt
  -> #inv : (HS.mem -> G.erased Type0)
  -> #inv_lem : (h0:HS.mem -> h1:HS.mem ->
                 Lemma (requires (inv h0 /\ B.(modifies (region_of ll) h0 h1)))
                 (ensures (inv h1)))
  -> #fspec : (G.erased (fspec_ty dt))
  -> f : pred_st ll (region_of ll) inv inv_lem fspec ->
  ST unit
    (requires fun h0 ->
      inv h0 /\
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      let filtered = gfilter_elements fspec h0 (get_elems h0 ll) in
      B.modifies (region_of ll) h0 h1 /\
      invariant h1 ll /\
      get_elems h1 ll == filtered /\
      gsame_elementsp filtered h0 h1 /\
      // The following is a consequence from the preceding assertions,
      // but not a trivial derivation and more convenient in most situations
      v h1 ll == L.filter fspec (v h0 ll))

inline_for_extraction noextract
val filter : filter_st

noextract unfold
let filter_one_st_pre :
     #dt: stateful unit
  -> ll: t dt
  -> inv : (HS.mem -> G.erased Type0)
  -> fspec : (G.erased (fspec_ty dt))
  -> h0 : HS.mem ->
  GTot Type0 =
  fun #dt ll inv fspec h0 ->
  inv h0 /\
  invariant h0 ll

/// Weird things happen if this definition is not [unfold]. It seems that F* messes
/// up the encoding of [v h1 ll == filter_one fspec (v h0 ll)], probably because
/// [fspec] is ghost (in Impl.Noise.API.Device, there is thus a [Ghost.hide] which is inserted). 
/// The only way to retrieve it if there is no [unfold] is then to do [assert (filter_one_st_post ...)]
/// after the call to [filter_one], then [norm_spec [delta_only [`%filter_one_st_post]] (filter_one_st_post ...)].
/// It would be worth investigating what happens.
noextract unfold
let filter_one_st_post :
     #dt: stateful unit
  -> ll: t dt
  -> inv : (HS.mem -> G.erased Type0)
  -> fspec : (G.erased (fspec_ty dt))
  -> h0 : HS.mem
  -> h1 : HS.mem ->
  GTot Type0 =
  fun #dt ll inv fspec h0 h1 ->
  let filtered = gfilter_one_element fspec h0 (get_elems h0 ll) in
  B.modifies (region_of ll) h0 h1 /\
  invariant h1 ll /\
  get_elems h1 ll == filtered /\
  gsame_elementsp filtered h0 h1 /\
  // The following is a consequence from the preceding assertions,
  // but not a trivial derivation and more convenient in most situations
  v h1 ll == filter_one fspec (v h0 ll)

inline_for_extraction noextract
let filter_one_st =
     #dt: stateful unit
  -> ll: t dt
  -> #inv : (HS.mem -> G.erased Type0)
  -> #inv_lem : (h0:HS.mem -> h1:HS.mem ->
               Lemma (requires (inv h0 /\ B.(modifies (region_of ll) h0 h1)))
               (ensures (inv h1)))
  -> #fspec : (G.erased (fspec_ty dt))
  -> f : pred_st ll (region_of ll) inv inv_lem fspec ->
  ST unit
    (requires fun h0 -> filter_one_st_pre ll inv fspec h0)
    (ensures fun h0 _ h1 -> filter_one_st_post ll inv fspec h0 h1)

inline_for_extraction noextract
val filter_one : filter_one_st

/// Clearing (resetting)
/// --------------------

inline_for_extraction noextract
val clear (#dt: stateful unit) (ll: t dt) :
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (region_of ll) h0 h1 /\
      invariant h1 ll /\
      get_elems h1 ll == [])

/// Freeing the resource
/// --------------------

inline_for_extraction noextract
val free (#dt: stateful unit) (ll: t dt) :
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (region_of ll) h0 h1)
