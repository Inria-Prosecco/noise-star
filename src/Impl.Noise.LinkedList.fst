module Impl.Noise.LinkedList

/// A Low*, stateful linked list containing stateful data.
///
/// Two functions were a bit hard to implement: [filter] and [filter_one].
/// For those, we implement different flavours:
/// - a recursive, non tail-call version
/// - a recursive, tail-call version (only for [filter_one])
/// - a non recursive version using a loop (only for [filter_one])
///
/// The recursive versions don't extract, because they have non-extractable
/// meta parameters in their signature, unless you ask Karamel to turn tail-call
/// recursion to loops at extraction time.
///
/// It shouldn't be difficult to implement the tail-call version of
/// [filter], put aside the fact that we need to make sure that the
/// head of the list is valid (i.e.: the head element satisfies the
/// filtering predicate) before working on the rest of the list. This
/// didn't cause much trouble for [filter_one], because if it is not
/// the case we just have to pop the head. Also, it should be possible
/// to factorize several signatures between [filter] and [filter_one],
/// a bit like what we did for the non tail-call version.
/// 
/// If implemented for [filter], the loop versions of [filter] and [filter_one]
/// are, in a sense, strictly better than the recursive ones, because they
/// are the ones we want to extract. However, it is probably a good idea
/// to preserve the tail-call versions, because they were very useful to
/// figure out the structure of the proofs, as well as a big part of the
/// collection of lemmas we need throughout this file. For instance, trying
/// to implement the loop version of [filter] without having implemented
/// its tail-call equivalent before would be a very bad idea. Finally,
/// when working on [filter], it should be possible to generalize and reuse
/// some of the definitions used in [filter_one], leading to easier proofs
/// and better maintainability.

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
module M = Spec.Noise.Map

#set-options "--z3rlimit 25 --fuel 0 --ifuel 0"

let _align_beg = ()

[@CAbstractStruct]
noeq
type t_ (t1: Type0): Type0 = {
  ptr: B.pointer (LL1.t t1);
  // Relies on a new pointer-to-unit elimination phase in KaRaMeL
  // LL1 requires the client to keep track of a high-level ghost list
  // of the low-level elements in the low-level linked lidt. We can
  // then convert them to a list of high-level elements
  elems: B.pointer (G.erased (list t1));
  // For separation; all erased.
  r: HS.rid; // The region containing the whole list
  r_new : B.pointer HS.rid; // A sub-region in which to perform allocations
  r_spine : HS.rid;
}

inline_for_extraction noextract
let t (dt: stateful unit) = t_ (dt_s dt)

let get_elems #dt h ll =
  B.deref h ll.elems

// We rewrite the signature for the two following lemmas in order to make sure
// they are framed correctly. Also, as they are only valid locally, we adopt a
// more aggressive forward style in the patterns
val dt_frame_invariant_forward :
  #dt:stateful unit -> l:B.loc -> s:dt_s dt -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    dt_invariant h0 s /\
    B.loc_disjoint l (dt_footprint s) /\
    B.modifies l h0 h1))
  (ensures (
    dt_invariant h1 s /\
    dt_v h0 s == dt_v h1 s))
  [ SMTPat (dt_invariant h0 s); SMTPat (B.modifies l h0 h1) ]

let dt_frame_invariant_forward #dt l s h0 h1 = dt_frame_invariant l s h0 h1

val dt_frame_freeable_forward :
  #dt:stateful unit -> l:B.loc -> s:dt_s dt -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    dt_invariant h0 s /\
    dt_freeable h0 s /\
    B.loc_disjoint l (dt_footprint s) /\
    B.modifies l h0 h1))
  (ensures (
    dt_freeable h1 s))
  [ SMTPat (dt_freeable h0 s); SMTPat (B.modifies l h0 h1) ]

let dt_frame_freeable_forward #dt l s h0 h1 = dt_frame_freeable l s h0 h1

#push-options "--ifuel 1"
val elems_footprint: #dt:stateful unit -> ls:list (dt_s dt) -> GTot B.loc
let rec elems_footprint #dt ls =
  match ls with
  | [] -> B.loc_none
  | x :: ls' -> B.loc_union (dt_footprint x) (elems_footprint ls')
#pop-options

val elems_disjoint: #dt:stateful unit -> x:dt_s dt -> y:dt_s dt -> GTot Type0
let elems_disjoint #dt x y =
  B.loc_disjoint (dt_footprint x) (dt_footprint y)

#push-options "--ifuel 1"
val elems_pairwise_disjoint: #dt:stateful unit -> ls:list (dt_s dt) -> GTot Type0
let elems_pairwise_disjoint #dt ls =
  pairwise_grelP (elems_disjoint #dt) ls
#pop-options

val gfor_allP_elems_disjoint_implies_disjoint_from_footprint :
     #dt:stateful unit
  -> x:dt_s dt
  -> ls:list (dt_s dt) ->
  Lemma
  (requires (gfor_allP (elems_disjoint x) ls))
  (ensures (
    B.loc_disjoint (dt_footprint x) (elems_footprint ls)))

#push-options "--fuel 1 --ifuel 1"
let rec gfor_allP_elems_disjoint_implies_disjoint_from_footprint #dt x ls =
  match ls with
  | [] -> ()
  | y :: ls' ->
    gfor_allP_elems_disjoint_implies_disjoint_from_footprint x ls'
#pop-options

val disjoint_from_footprint_implies_gfor_allP_elems_disjoint :
     #dt:stateful unit
  -> x:dt_s dt
  -> ls:list (dt_s dt) ->
  Lemma
  (requires (B.loc_disjoint (dt_footprint x) (elems_footprint ls)))
  (ensures (gfor_allP (elems_disjoint x) ls))

#push-options "--fuel 1 --ifuel 1"
let rec disjoint_from_footprint_implies_gfor_allP_elems_disjoint #dt x ls =
  match ls with
  | [] -> ()
  | y :: ls' ->
    disjoint_from_footprint_implies_gfor_allP_elems_disjoint x ls'
#pop-options

val elems_pairwise_disjoint_implies_disjoint_from_footprint :
     #dt:stateful unit
  -> x:dt_s dt
  -> ls:list (dt_s dt) ->
  Lemma
  (requires (elems_pairwise_disjoint (x :: ls)))
  (ensures (B.loc_disjoint (dt_footprint x) (elems_footprint ls)))

#push-options "--fuel 1 --ifuel 1"
let elems_pairwise_disjoint_implies_disjoint_from_footprint #dt x ls =
  gfor_allP_elems_disjoint_implies_disjoint_from_footprint x ls
#pop-options

val disjoint_from_footprint_implies_elems_pairwise_disjoint :
     #dt:stateful unit
  -> x:dt_s dt
  -> ls:list (dt_s dt) ->
  Lemma
  (requires (
    elems_pairwise_disjoint ls /\
    B.loc_disjoint (dt_footprint x) (elems_footprint ls)))
  (ensures (elems_pairwise_disjoint (x :: ls)))

#push-options "--fuel 1 --ifuel 1"
let disjoint_from_footprint_implies_elems_pairwise_disjoint #dt x ls =
  disjoint_from_footprint_implies_gfor_allP_elems_disjoint x ls
#pop-options

val elems_invariants_hd_lem:
  #dt:stateful unit -> h:HS.mem -> x:dt_s dt -> elems:list (dt_s dt) ->
  Lemma (requires (elems_invariants h (x :: elems)))
  (ensures (
    dt_invariant h x /\
    dt_freeable h x /\
    elems_invariants h elems))
#push-options "--fuel 1 --ifuel 1"
let elems_invariants_hd_lem #dt h x elems = ()
#pop-options

let invariant #dt h ll =
  let head = B.deref h ll.ptr in
  let elems = B.deref h ll.elems in
  let r_new = B.deref h ll.r_new in

  B.live h ll.ptr /\
  B.freeable ll.ptr /\
  B.live h ll.elems /\
  B.freeable ll.elems /\
  B.live h ll.r_new /\
  B.freeable ll.r_new /\
  LL1.well_formed h head elems /\
  LL1.invariant h head elems /\
  elems_invariants h elems /\

  // We use regions for separation only, not for any footprint reasoning:
  // - ptr_v_rid is a sub-region of r and contains ptr and v, disjoint from each other
  // - spine_rid is a sub-region of r, disjoint from ptr_v_rid, and contains the LL1.footprint
  ll.r =!= FStar.Monotonic.HyperHeap.root /\
  ST.is_eternal_region ll.r /\
  ST.is_eternal_region r_new /\
  ST.is_eternal_region ll.r_spine /\
  begin
  let r_loc = B.loc_all_regions_from false ll.r in
  let r_new_ptr_loc = B.loc_addr_of_buffer ll.r_new in
  let r_new_loc = B.loc_all_regions_from false r_new in
  let r_spine_loc = B.loc_region_only true ll.r_spine in
  let ptr_loc = B.loc_addr_of_buffer ll.ptr in
  let elems_ptr_loc = B.loc_addr_of_buffer ll.elems in
  let spine_loc = LL1.footprint h head elems in
  let elems_loc = elems_footprint elems in
  B.all_disjoint [r_new_ptr_loc; r_new_loc; r_spine_loc; ptr_loc; elems_ptr_loc; elems_loc] /\
  B.loc_includes r_loc r_new_ptr_loc /\
  B.loc_includes r_loc r_new_loc /\
  B.loc_includes r_loc r_spine_loc /\
  B.loc_includes r_loc ptr_loc /\
  B.loc_includes r_loc elems_ptr_loc /\
  B.loc_includes r_spine_loc spine_loc /\
  B.loc_includes r_loc elems_loc /\
  elems_pairwise_disjoint elems
  end

let region_of #dt ll = B.loc_all_regions_from false ll.r

/// Some utilities

val elems_frame_forall_disjoint :
     #dt:stateful unit
  -> e:dt_s dt
  -> elems:list (dt_s dt)
  -> l:B.loc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    gfor_allP (elems_disjoint e) elems /\
    B.loc_disjoint l (B.loc_union (dt_footprint e) (elems_footprint elems)) /\
    B.modifies l h0 h1))
  (ensures (
    gfor_allP (elems_disjoint e) elems))

#push-options "--fuel 2 --ifuel 2"
let rec elems_frame_forall_disjoint #dt e elems l h0 h1 =
  match elems with
  | [] -> ()
  | e' :: elems' ->
    elems_frame_forall_disjoint e elems' l h0 h1
#pop-options

val elems_frame_invariant :
     #dt:stateful unit
  -> elems:list (dt_s dt)
  -> l:B.loc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    elems_invariants h0 elems /\
    B.loc_disjoint l (elems_footprint elems) /\
    B.modifies l h0 h1))
  (ensures (
    elems_invariants h1 elems /\
    elems_footprint elems == elems_footprint elems /\
    // Two versions of the same property - one is used for the high-level
    // specification revealed to the user, the other is used to preserve
    // internal invariants
    gsame_elementsp elems h0 h1 /\
    elems_v h1 elems == elems_v h0 elems))
  [ SMTPat (elems_invariants h0 elems);
    SMTPat (B.modifies l h0 h1)]

#push-options "--fuel 1 --ifuel 1"
let rec elems_frame_invariant #dt elems l h0 h1 =
  match elems with
  | [] -> ()
  | e :: elems' ->
    assert(dt_invariant #dt h0 e);
    assert(dt_freeable #dt h0 e);
    dt_frame_invariant l e h0 h1;
    dt_frame_freeable l e h0 h1;
    elems_frame_invariant elems' l h0 h1
#pop-options

val elems_frame :
     #dt:stateful unit
  -> elems:list (dt_s dt)
  -> l:B.loc
  -> h0:HS.mem
  -> h1:HS.mem ->
  Lemma
  (requires (
    elems_invariants h0 elems /\
    elems_pairwise_disjoint elems /\
    B.loc_disjoint l (elems_footprint elems) /\
    B.modifies l h0 h1))
  (ensures (
    elems_invariants h1 elems /\
    elems_pairwise_disjoint elems /\
    elems_footprint elems == elems_footprint elems /\
    // Two versions of the same property - one is used for the high-level
    // specification revealed to the user, the other is used to preserve
    // internal invariants
    gsame_elementsp elems h0 h1 /\
    elems_v h0 elems == elems_v h1 elems))
  [ SMTPat (elems_invariants h0 elems);
    SMTPat (B.modifies l h0 h1)]

let elems_frame #dt elems l h0 h1 =
  elems_frame_invariant elems l h0 h1

#push-options "--fuel 1 --ifuel 1"
let rec gsame_elementsp_refl ll h0 =
  match ll with
  | [] -> ()
  | x :: ll' -> gsame_elementsp_refl ll' h0
#pop-options

/// Same as the above lemma, but with an SMT pattern to trigger locally
val gsame_elementsp_refl_smt
  (#dt : stateful unit) (ll : list (dt_s dt)) (h0 : HS.mem) :
  Lemma
  (requires (elems_invariants h0 ll))
  (ensures (gsame_elementsp ll h0 h0))
  [SMTPat (gsame_elementsp ll h0 h0)]

let gsame_elementsp_refl_smt #dt ll h0 =
  gsame_elementsp_refl #dt ll h0

let gsame_elementsp_trans #dt ll h0 h1 h2 =
  assert(gsame_elementsp ll h0 h1);
  assert(gsame_elementsp ll h1 h2);
  list_in_listP_refl ll;
  gfor_allP_list_in_listP_and
    (fun x -> dt_v h1 x == dt_v h0 x)
    (fun x -> dt_v h2 x == dt_v h1 x)
    (fun x -> dt_v h2 x == dt_v h0 x) (fun x -> ())
    ll ll

let gsame_elementsp_list_in_listP_trans #dt ll0 ll1 h0 h1 h2 =
  assert(gsame_elementsp ll0 h0 h1);
  assert(gsame_elementsp ll1 h1 h2);
  gfor_allP_list_in_listP (fun x -> dt_v h2 x == dt_v h1 x) ll0 ll1;
  assert(gsame_elementsp ll0 h1 h2);
  gsame_elementsp_trans #dt ll0 h0 h1 h2

#push-options "--fuel 1 --ifuel 1"
let rec gsame_elementsp_elems_v_lem #dt ll h0 h1 =
  match ll with
  | [] -> ()
  | x :: ll' -> gsame_elementsp_elems_v_lem ll' h0 h1
#pop-options

let frame_invariant #dt ll l h0 h1 =
  let ls = B.deref h0 ll.ptr in
  let elems = B.deref h0 ll.elems in
  elems_frame_invariant elems l h0 h1;
  LL1.frame ls elems l h0 h1

/// Creating an imperative list
/// ---------------------------

let glist_owns_element (#dt: stateful unit) (ll: list (dt_s dt)) (e: dt_s dt) : GTot Type0 =
  memP e ll

let invariant_implies_elements_invariants #dt h ll = ()

#push-options "--z3rlimit 50 --fuel 1"
let create_in #dt r =
  (**) let h0 = get () in
  let r' = ST.new_region r in
  (**) assert(B.(loc_includes (loc_all_regions_from false r) (loc_all_regions_from false r')));
  let r_new = ST.new_region r' in
  let r_misc = ST.new_region r' in
  let r_spine = ST.new_region r' in
  let ptr = B.malloc r_misc (B.null <: LL1.t (dt_s dt)) 1ul in
  let elems = B.malloc r_misc (G.hide ([] <: list (dt_s dt))) 1ul in
  let r_new_ptr = B.malloc r_misc r_new 1ul in
  { ptr = ptr; elems = elems; r = r'; r_spine = r_spine; r_new = r_new_ptr }
#pop-options

val elements_list_footprint :
  #dt:stateful unit ->
  h:HS.mem ->
  ll:LL1.t (dt_s dt) ->
  llv:Ghost.erased (list (dt_s dt)) ->
  Ghost B.loc (requires (LL1.well_formed h ll llv)) (ensures (fun _ -> True))

let elements_list_footprint #dt h ll llv =
  B.loc_union (LL1.footprint h ll llv) (elems_footprint llv)

val elements_list_invariant:
  #dt:stateful unit ->
  h:HS.mem ->
  ll:LL1.t (dt_s dt) ->
  llv:Ghost.erased (list (dt_s dt)) ->
  GTot Type0

let elements_list_invariant #dt h ll llv =
  LL1.well_formed h ll llv /\
  LL1.invariant h ll llv /\
  elems_invariants #dt h llv /\
  elems_pairwise_disjoint #dt llv /\
  B.loc_disjoint (LL1.footprint h ll llv) (elems_footprint llv)

val elements_list_frame_invariant :
  #dt:stateful unit ->
  ll:LL1.t (dt_s dt) ->
  llv:Ghost.erased (list (dt_s dt)) ->
  l:B.loc ->
  h0:HS.mem ->
  h1:HS.mem ->
  Lemma
  (requires (
    elements_list_invariant h0 ll llv /\
    B.modifies l h0 h1 /\
    B.loc_disjoint l (elements_list_footprint h0 ll llv)))
  (ensures (
    elements_list_invariant h1 ll llv /\
    gsame_elementsp llv h0 h1 /\
    elems_v h1 llv == elems_v h0 llv))
  [SMTPat (B.modifies l h0 h1); SMTPat (elements_list_invariant h0 ll llv)]

let elements_list_frame_invariant #dt ll llv l h0 h1 =
  elems_frame llv l h0 h1

let ll1_pred_inv_lem
  (#dt: stateful unit)
  (l_ref : B.loc)
  (inv : HS.mem -> G.erased Type0) =
  h0:HS.mem -> l:B.loc -> h1:HS.mem ->
  Lemma
  (requires (
    inv h0 /\
    B.modifies l h0 h1 /\
    ST.equal_stack_domains h0 h1 /\
    B.loc_includes l_ref l))
  (ensures (inv h1))
  [SMTPat (inv h0); SMTPat (B.modifies l h0 h1)]

/// This signature (and a lot others later) take [l_all] and [l_mod] locs as
/// parameters. In some situations, it would be possible to not take those
/// as parameters, but we still use them because otherwise adding terms
/// of the form [B.loc_union (elements_list_footprint ...) ...] everywhere
/// really clutters the code.
inline_for_extraction noextract
let ll1_pred_st
  (#dt: stateful unit)
  (l_all l_mod : B.loc)
  (inv : HS.mem -> G.erased Type0)
  (inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (spec: G.erased (fspec_ty dt)) =
  x:dt_s dt ->
  Stack bool
  (requires (fun h0 ->
    inv h0 /\
    dt_invariant h0 x /\
    B.loc_includes l_all (dt_footprint x)))
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    b = (G.reveal spec) (dt_v h0 x)))

// Below, we don't need to take [l_mod] as parameter,
// but it is more convenient and readable.
let find_loop_pre
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec) =
  (fun h0 ->
    let llt = B.deref h0 lltp in
    let llv = B.deref h0 llvp in
    B.live h0 lltp /\ B.live h0 llt /\ B.live h0 llvp /\
    elements_list_invariant h0 llt llv /\
    inv h0 /\
    begin
    let tp_loc = B.loc_addr_of_buffer lltp in
    let vp_loc = B.loc_addr_of_buffer llvp in
    let ll_loc = elements_list_footprint h0 llt llv in
    B.all_disjoint [tp_loc; vp_loc; ll_loc] /\
    G.reveal l_mod == B.(loc_buffer lltp `loc_union` loc_buffer llvp) /\
    B.loc_includes l_all ll_loc /\
    True
    end)

/// The main part of the [find] function, which contains the while loop
inline_for_extraction noextract
val find_loop
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec) :
  Stack unit
  (requires find_loop_pre #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f)

  (ensures (fun h0 unit h1 ->
    let llv0 = B.deref h0 llvp in
    let llv1 = B.deref h1 llvp in
    let llt1 = B.deref h1 lltp in
    B.(modifies l_mod h0 h1) /\
    B.live h1 lltp /\ B.live h1 llt1 /\ B.live h1 llvp /\
    elements_list_invariant h1 llt1 llv1 /\
    inv h1 /\
    begin
    let r_v = L.tryFind fspec (elems_v h0 llv0) in
    match not (B.g_is_null llt1) with
    | false -> r_v == None
    | true ->
      begin
      let x = (B.deref h1 llt1).LL1.data in
      r_v == Some (dt_v h1 x) /\
      dt_invariant #dt h1 x /\
      dt_freeable #dt h1 x /\
      B.loc_includes l_all (dt_footprint #dt x) /\
      glist_owns_element llv0 x /\
      True
      end
    end))

inline_for_extraction noextract
let find_loop_inv
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { find_loop_pre #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 })
=
  fun h0 ->
  let llt0 = B.deref h00 lltp in
  let llv0 = B.deref h00 llvp in
  let llt = B.deref h0 lltp in
  let llv = B.deref h0 llvp in
  B.live h0 lltp /\ B.live h0 llt /\ B.live h0 llvp /\
  elements_list_invariant h0 llt llv /\
  inv h0 /\
  begin
  let ll0_loc = elements_list_footprint h00 llt0 llv0 in
  let ll_loc = elements_list_footprint h0 llt llv in
  B.loc_includes ll0_loc ll_loc /\
  B.(modifies l_mod h00 h0) /\
  L.tryFind fspec (elems_v h00 llv0) == L.tryFind fspec (elems_v h0 llv) /\
  list_in_listP llv llv0 /\
  True
  end

inline_for_extraction noextract
let find_loop_guard
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { find_loop_pre #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 })
  (h0:HS.mem{find_loop_inv #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 h0}): GTot bool =
  let llt = B.deref h0 lltp in
  if B.g_is_null llt then false
  else
    let x = (B.deref h0 llt).LL1.data in
    not (Ghost.reveal fspec (dt_v h0 x))

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
let find_loop_test
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { find_loop_pre #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 })
  ():
  Stack bool (requires find_loop_inv #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00)
  (ensures  fun h0 b h1 -> b == find_loop_guard #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 h0 /\
            B.(modifies loc_none h0 h1)) =
  (**) let h0 = get () in
  let llt = B.index lltp 0ul in
  let llv = B.index llvp 0ul in
  if B.is_null llt then
    false
  else
    begin
    let c = B.index llt 0ul in
    (**) let h1 = get () in
    [@inline_let] let x = c.LL1.data in
    begin
    (**) inv_lem h0 B.loc_none h1;
    (**) dt_frame_invariant #dt B.loc_none x h0 h1;
    (**) dt_frame_freeable #dt B.loc_none x h0 h1;
    (**) LL1.frame llt llv B.loc_none h0 h1;
    (**) elems_frame_invariant #dt llv B.loc_none h0 h1
    end;
    let b = f x in
    (**) let h2 = get () in
    (**) inv_lem h1 B.loc_none h2;
    (**) dt_frame_invariant #dt B.loc_none x h1 h2;
    (**) dt_frame_freeable #dt B.loc_none x h1 h2;
    (**) LL1.frame llt llv B.loc_none h1 h2;
    (**) elems_frame_invariant #dt llv B.loc_none h1 h2;
    not b
    end

inline_for_extraction noextract
let find_loop_test_
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { find_loop_pre #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 })
  ():
  Stack bool (requires find_loop_inv #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00)
  (ensures  fun _ b h -> find_loop_inv #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 h /\
    b == find_loop_guard #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 h)
=
  (**) let h0 = get () in
  (**) assert(inv h0);
  let b = find_loop_test #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 () in
  (**) let h1 = get () in
  begin
  (**) let llt = B.deref h0 lltp in
  (**) let llv = B.deref h0 llvp in
  (**) elements_list_frame_invariant #dt llt llv B.loc_none h0 h1;
  (**) inv_lem h0 B.loc_none h1;
  (**) assert(inv h1)
  end;
  b

let find_loop #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f =
  (**) let h00 = get () in
  [@inline_let]
  let inv' : HS.mem -> Type0 = find_loop_inv #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 in

  [@inline_let]
  let guard = find_loop_guard #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00 in

  [@inline_let]
  let test: unit -> Stack bool
    (requires (fun h -> inv' h))
    (ensures  fun _ b h -> inv' h /\ b == guard h)
  =
    find_loop_test_ #dt l_all l_mod lltp llvp #inv #inv_lem #fspec f h00
  in

  [@inline_let]
  let body : (unit -> Stack unit
                    (requires fun h -> inv' h /\ guard h)
                    (ensures  fun _ _ h -> inv' h)) =
    fun () ->
    (**) let h0 = get () in
    let llt = B.index lltp 0ul in
    let llv = B.index llvp 0ul in
    let c = B.index llt 0ul in
    B.upd lltp 0ul c.LL1.next;
    B.upd llvp 0ul (L.tl llv);
    (**) let h1 = get () in
    begin
    (**) assert(B.modifies l_mod h0 h1);
    (**) inv_lem h0 l_mod h1;
    (**) LL1.frame llt llv l_mod h0 h1;
    (**) elems_frame_invariant llv l_mod h0 h1
    end
  in
  
  // The original list is included in itself
  (**) list_in_listP_refl (B.deref h00 llvp);
  (**) assert(inv' h00);

  C.Loops.while #(fun h -> inv' h) #(fun b h -> inv' h /\ b == guard h) test body
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let find #dt ll #inv #inv_lem #fspec rtype f =
  (**) let h0 = get () in
  let llt: LL1.t (dt_s dt) = !* ll.ptr in
  let llv = !* ll.elems in
  (**) let h1 = get () in
  (**) assert(invariant #dt h1 ll);
  push_frame ();
  let lltp: B.buffer (LL1.t (dt_s dt)) = B.alloca llt 1ul in
  let llvp = B.alloca llv 1ul in
  (**) let h2 = get () in
  ST.recall_region ll.r;
  (**) let tp_loc = Ghost.hide B.(loc_buffer lltp) in
  (**) let vp_loc = Ghost.hide B.(loc_buffer llvp) in
  (**) let l_mod = Ghost.hide B.(loc_union tp_loc vp_loc) in
  (**) let ll_loc = Ghost.hide (elements_list_footprint #dt h0 llt llv) in
  (**) let l_mod = Ghost.hide B.(loc_union tp_loc vp_loc) in
  (**) let l_all = Ghost.hide (region_of #dt ll) in
  (**) assert(B.(loc_disjoint (loc_all_regions_from false ll.r) tp_loc));
  (**) assert(B.(loc_disjoint (loc_all_regions_from false ll.r) vp_loc));
  [@inline_let]
  let inv' : HS.mem -> Ghost.erased Type0=
    fun h ->
    B.(modifies loc_none h1 h) /\
    B.live h lltp /\
    B.live h llvp /\
    B.(fresh_loc (loc_addr_of_buffer lltp)) h1 h /\
    B.(fresh_loc (loc_addr_of_buffer llvp)) h1 h /\
    B.(loc_includes (loc_region_only true (HS.get_tip h)) l_mod) /\
    inv h
  in
  [@inline_let]
  let inv_lem' : ll1_pred_inv_lem #dt l_mod inv' =
    fun h0' l h1' ->
    (**) B.(modifies_only_not_unused_in loc_none h1 h1');
    (**) assert(B.(modifies loc_none h1 h1'));
    (**) inv_lem h1 h1';
    (**) assert(B.(fresh_loc (loc_addr_of_buffer lltp)) h1 h1');
    (**) assert(B.(fresh_loc (loc_addr_of_buffer llvp)) h1 h1');
    (**) assert(B.(loc_includes (loc_region_only true (HS.get_tip h1')) l_mod))
  in
  [@inline_let]
  let f' : ll1_pred_st l_all l_mod inv' inv_lem' fspec =
    fun x -> f x
  in
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);
  (**) elements_list_frame_invariant #dt llt llv B.loc_none h1 h2;
  (**) assert(elements_list_invariant #dt h2 llt llv);
  (**) inv_lem h1 h2;
  find_loop #dt l_all l_mod lltp llvp #inv' #inv_lem' #fspec f';
  (**) let h3 = get () in
  (**) assert(B.modifies l_mod h2 h3);
  let llt = !* lltp in 
  let res: f_rty rtype =
    if B.is_null llt then f_no_elem
    else
      begin
      let c: LL1.cell (dt_s dt) = !* llt in
      [@inline_let] let x = c.LL1.data in
      f_from_elem x
      end
  in
  pop_frame ();
  (**) let h4 = get () in
  begin
  (**) let r_stack = FStar.Monotonic.HyperStack.get_tip h2 in
  (**) assert(B.modifies (B.loc_region_only false r_stack) h3 h4);
  (**) begin match f_get_elem res with
  (**) | None -> ()
  (**) | Some res -> dt_frame_invariant #dt (B.loc_region_only false r_stack) res h3 h4
  (**) end;
  (**) B.(modifies_only_not_unused_in loc_none h0 h4);
  (**) inv_lem h0 h4
  end;
  res
#pop-options

let _ = ()

/// Adding elements
/// ---------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let push #dt ll input =
  (**) let h0 = get () in
  let r_new = !* ll.r_new in
  let r_elem = ST.new_region r_new in
  let r_new' = ST.new_region r_new in
  (**) let h1 = get () in
  (**) dt.smfi_input.frame_invariant B.loc_none input h0 h1;
  (**) frame_invariant ll B.loc_none h0 h1;
  let x = dt_malloc #dt r_elem input in
  (**) let h2 = get () in
  (**) frame_invariant ll B.loc_none h1 h2;
  LL1.push ll.r_spine (!* ll.elems) ll.ptr x;
  (**) let h3 = get () in
  (**) assert(B.(modifies (loc_buffer ll.ptr) h2 h3));
  let elems = !* ll.elems in
  begin
  (**) let r_new_loc = B.loc_all_regions_from false r_new in
  (**) let r_elem_loc = B.loc_all_regions_from false r_elem in
  (**) let r_new'_loc = B.loc_all_regions_from false r_new' in
  (**) assert(B.loc_includes r_new_loc r_elem_loc);
  (**) assert(B.loc_includes r_new_loc r_new'_loc);
  (**) assert(B.loc_includes r_elem_loc (dt_footprint x));
  (**) assert(B.loc_includes r_new_loc (dt_footprint x)); // This one is necessary: otherwise, patterns won't trigger
  (**) assert(B.loc_disjoint (dt_footprint x) (elems_footprint elems));
  (**) disjoint_from_footprint_implies_elems_pairwise_disjoint x elems
  end;
  ll.elems *= G.hide (x :: elems);
  ll.r_new *= r_new';
  (**) let h5 = get () in
  begin
  (**) let ptr_loc = B.loc_buffer ll.ptr in
  (**) let elems_ptr_loc = B.loc_buffer ll.elems in
  (**) let r_new_loc = B.loc_buffer ll.r_new in
  (**) let l = B.(ptr_loc `loc_union` elems_ptr_loc `loc_union` r_new_loc) in
  (**) assert(B.modifies l h0 h5);
  (**) dt_frame_invariant l x h2 h5;
  (**) dt_frame_freeable l x h2 h5;
  (**) elems_frame (B.deref h0 ll.elems) l h0 h5;
  (**) assert(dt_invariant h5 x);
  (**) assert(elems_invariants h5 (B.deref h5 ll.elems));
  (**) assert(invariant h5 ll)
  end;
  begin
  (**) let elems0 = B.deref h0 ll.elems in
  (**) let elems1 = B.deref h5 ll.elems in
  (**) assert(Cons? elems1);
  (**) assert(Cons?.tl elems1 == G.reveal elems0);
  (**) assert(gsame_elementsp elems0 h0 h5)
  end;
  x
#pop-options

/// Removing elements
/// -----------------

#push-options "--fuel 1 --ifuel 1"
let pop #dt ll =
  (**) let h0 = get () in
  let elem1 = LL1.pop ll.r_spine (!* ll.elems) ll.ptr in
  (**) let h1 = get () in
  begin
  (**) let elems = B.deref h0 ll.elems in
  (**) let l = B.(loc_buffer ll.ptr `loc_union` LL1.footprint h0 (B.deref h0 ll.ptr) elems) in
  (**) assert(B.(modifies l h0 h1));
  (**) assert(B.loc_disjoint l (dt_footprint elem1));
  (**) dt_frame_invariant l elem1 h0 h1;
  (**) dt_frame_freeable l elem1 h0 h1;
  (**) assert(dt_invariant h1 elem1);
  (**) assert(dt_freeable h1 elem1)
  end;
  dt_free #dt elem1;
  let elems = !* ll.elems in
  (**) let h2 = get () in
  ll.elems *= G.hide (L.tl elems);
  (**) let h3 = get () in
  begin
  (**) let elems_ptr_loc = B.loc_addr_of_buffer ll.elems in
  (**) let elem1_loc = dt_footprint elem1 in
  (**) let ll_loc = LL1.footprint h0 (B.deref h0 ll.ptr) elems in
  (**) let ll_ptr_loc = B.loc_buffer ll.ptr in
  (**) let l = B.(elems_ptr_loc `loc_union` elem1_loc `loc_union` ll_loc `loc_union` ll_ptr_loc) in
  (**) assert(B.(modifies l h0 h3));
  (**) let elems' = L.tl elems in
  (**) let elems'_loc = elems_footprint elems' in
  (**) assert(B.loc_disjoint elems_ptr_loc elems'_loc);
  (**) elems_pairwise_disjoint_implies_disjoint_from_footprint #dt elem1 elems';
  (**) assert(B.loc_disjoint elem1_loc elems'_loc);
  (**) assert(B.loc_disjoint ll_loc elems'_loc);
  (**) assert(B.loc_disjoint ll_ptr_loc elems'_loc);
  (**) assert(B.loc_disjoint l elems'_loc);
  (**) elems_frame elems' l h0 h3
  end
#pop-options


/// Filter/filter_one implementation non tail-call implementations:
/// We write one function which takes a meta parameter, used to switch
/// between filter and filter_one. This allows us to factorize the proofs.

let gfilter_gen (filter : bool) :
  #a: Type -> f:(a -> GTot bool) -> l: list a -> GTot (list a) =
  if filter then gfilter else gfilter_one

val gfilter_elements_same_lem
  (#dt: stateful unit)
  (ll: list (dt_s dt))
  (fspec : G.erased (fspec_ty dt))
  (h0 h1: HS.mem) :
  Lemma
  (requires (gsame_elementsp ll h0 h1))
  (ensures (
    gfilter_elements fspec h1 ll == gfilter_elements fspec h0 ll))
  [SMTPat (gsame_elementsp ll h0 h1);
   SMTPat (gfilter_elements fspec h0 ll)]

#push-options "--fuel 1 --ifuel 1"
let rec gfilter_elements_same_lem #dt ll fspec h0 h1 =
  match ll with
  | [] -> ()
  | x :: ll' -> gfilter_elements_same_lem ll' fspec h0 h1
#pop-options

val gfilter_one_element_same_lem
  (#dt: stateful unit)
  (ll: list (dt_s dt))
  (fspec : G.erased (fspec_ty dt))
  (h0 h1: HS.mem) :
  Lemma
  (requires (gsame_elementsp ll h0 h1))
  (ensures (
    gfilter_one_element fspec h1 ll == gfilter_one_element fspec h0 ll))
  [SMTPat (gsame_elementsp ll h0 h1);
   SMTPat (gfilter_one_element fspec h0 ll)]

#push-options "--fuel 1 --ifuel 1"
let rec gfilter_one_element_same_lem #dt ll fspec h0 h1 =
  match ll with
  | [] -> ()
  | x :: ll' -> gfilter_one_element_same_lem ll' fspec h0 h1
#pop-options

val frame_gsame_elementsp1
  (#dt : stateful unit) (ll : list (dt_s dt)) (l : B.loc)
  (h0 h1 h2 : HS.mem) :
  Lemma
  (requires (
    B.loc_disjoint l (elems_footprint ll) /\
    B.modifies l h1 h2 /\
    elems_invariants h1 ll /\
    gsame_elementsp ll h0 h1))
  (ensures (gsame_elementsp ll h0 h2))
  [SMTPat (B.modifies l h1 h2);
   SMTPat (gsame_elementsp ll h0 h1)]

// We could do the proofs in a smarter manner, but doing them by recursion is
// actually so simple...
#push-options "--fuel 1 --ifuel 1"
let rec frame_gsame_elementsp1 #dt ll l h0 h1 h2 =
  match ll with
  | [] -> ()
  | x :: ll' ->
    dt_frame_invariant l x h1 h2;
    frame_gsame_elementsp1 ll' l h0 h1 h2

val gfilter_elements_invariants_lem
  (#dt : stateful unit) (ll : list (dt_s dt))
  (fspec : G.erased (fspec_ty dt))
  (h : HS.mem) :
  Lemma (requires (elems_invariants h ll))
  (ensures (
    elems_invariants h (gfilter_elements fspec h ll)))

val frame_gsame_elementsp2
  (#dt : stateful unit) (ll : list (dt_s dt)) (l : B.loc)
  (h0 h1 h2 : HS.mem) :
  Lemma
  (requires (
    B.loc_disjoint l (elems_footprint ll) /\
    B.modifies l h0 h1 /\
    elems_invariants h0 ll /\
    gsame_elementsp ll h1 h2))
  (ensures (gsame_elementsp ll h0 h2))
  [SMTPat (B.modifies l h0 h1);
   SMTPat (gsame_elementsp ll h1 h2)]

let rec frame_gsame_elementsp2 #dt ll l h0 h1 h2 =
  match ll with
  | [] -> ()
  | x :: ll' ->
    dt_frame_invariant l x h0 h1;
    frame_gsame_elementsp2 ll' l h0 h1 h2

#push-options "--fuel 1 --ifuel 1"
let rec gfilter_elements_invariants_lem #dt ll fspec h =
  match ll with
  | [] -> ()
  | x :: ll' -> gfilter_elements_invariants_lem ll' fspec h
#pop-options

val gfilter_one_element_invariants_lem
  (#dt : stateful unit) (ll : list (dt_s dt))
  (fspec : G.erased (fspec_ty dt))
  (h : HS.mem) :
  Lemma (requires (elems_invariants h ll))
  (ensures (
    elems_invariants h (gfilter_one_element fspec h ll)))
  [SMTPat (elems_invariants h (gfilter_one_element fspec h ll))]

#push-options "--fuel 1 --ifuel 1"
let rec gfilter_one_element_invariants_lem #dt ll fspec h =
  match ll with
  | [] -> ()
  | x :: ll' -> gfilter_one_element_invariants_lem ll' fspec h
#pop-options

val gfilter_one_element_cons_elems_pairwise_disjoint
  (#dt : stateful unit) (x : dt_s dt) (ll : list (dt_s dt))
  (fspec : G.erased (fspec_ty dt))
  (h : HS.mem) :
  Lemma (requires (
//    elems_invariants h (x :: ll) /\
    elems_pairwise_disjoint (x :: ll)))
  (ensures (
    elems_pairwise_disjoint (x :: gfilter_one_element fspec h ll)))
  (decreases ll)
  [SMTPat (elems_pairwise_disjoint (x :: gfilter_one_element fspec h ll))]

#push-options "--fuel 2 --ifuel 2"
let rec gfilter_one_element_cons_elems_pairwise_disjoint #dt x ll fspec h =
  match ll with
  | [] -> ()
  | x' :: ll' ->
    if filter_pred fspec h x' then
      begin
      gfilter_one_element_cons_elems_pairwise_disjoint #dt x ll' fspec h;
      gfilter_one_element_cons_elems_pairwise_disjoint #dt x' ll' fspec h
      end
    else
      begin
      assert(gfilter_one_element fspec h ll == ll')
      end
#pop-options

val gsame_elementsp_modifies (#dt: stateful unit) (ll : list (dt_s dt)) (l : B.loc) (h0 h1: HS.mem) :
  Lemma
  (requires (
    B.(modifies l h0 h1) /\
    elems_invariants h0 ll /\
    B.loc_disjoint l (elems_footprint #dt ll)))
  (ensures (gsame_elementsp ll h0 h1))
  [SMTPat (B.(modifies l h0 h1));
   SMTPat (elems_invariants h0 ll)]

#push-options "--ifuel 1 --fuel 1"
let rec gsame_elementsp_modifies #dt ll l h0 h1 =
  match ll with
  | [] -> ()
  | x :: ll' -> gsame_elementsp_modifies ll' l h0 h1
#pop-options
#pop-options

val gsame_elementsp_modifies_lem
  (#dt : stateful unit) (ll : list (dt_s dt)) (l : B.loc) (h0 h1 : HS.mem) :
  Lemma
  (requires (
    elems_invariants h0 ll /\
    B.(modifies l h0 h1) /\
    B.(loc_disjoint (elems_footprint ll) l)))
  (ensures (
    gsame_elementsp ll h0 h1))
  [SMTPat (gsame_elementsp ll h0 h1);
   SMTPat (elems_invariants h0 ll);
   SMTPat (B.(modifies l h0 h1))]

let gsame_elementsp_modifies_lem #dt ll l h0 h1 =
  gsame_elementsp_refl ll h0

val gfilter_one_element_eq_lem
  (#dt: stateful unit) (fspec : G.erased (fspec_ty dt))
  (ll : list (dt_s dt)) (l : B.loc) (h0 h1 : HS.mem) :
  Lemma
  (requires (
    B.(modifies l h0 h1) /\
    elems_invariants h0 ll /\
    B.loc_disjoint l (elems_footprint #dt ll)))
  (ensures (
    gfilter_one_element fspec h0 ll == gfilter_one_element fspec h1 ll))
  [SMTPat (B.(modifies l h0 h1));
   SMTPat (B.loc_disjoint l (elems_footprint #dt ll));
   SMTPat (gfilter_one_element fspec h1 ll)]

#push-options "--ifuel 1 --fuel 1"
let rec gfilter_one_element_eq_lem #dt fspec ll l h0 h1 =
  match ll with
  | [] -> ()
  | x :: ll' -> gfilter_one_element_eq_lem #dt fspec ll' l h0 h1
#pop-options

val gsame_elementsp_gfilter_one_element_eq_lem
  (#dt: stateful unit) (fspec : G.erased (fspec_ty dt))
  (ll : list (dt_s dt)) (h0 h1 : HS.mem) :
  Lemma
  (requires (
    gsame_elementsp ll h0 h1))
  (ensures (
    gfilter_one_element fspec h0 ll == gfilter_one_element fspec h1 ll))
  [SMTPat (gsame_elementsp ll h0 h1);
   SMTPat (gfilter_one_element fspec h1 ll)]

#push-options "--ifuel 1 --fuel 1"
let rec gsame_elementsp_gfilter_one_element_eq_lem #dt fspec ll h0 h1 =
  match ll with
  | [] -> ()
  | x :: ll' -> gsame_elementsp_gfilter_one_element_eq_lem #dt fspec ll' h0 h1
#pop-options

val filtered_footprint_invariants_lem
  (#dt : stateful unit) (filter_all : bool) (fspec : dt_s dt -> GTot bool)
  (ll : list (dt_s dt)) (h0 : HS.mem) :
  Lemma
  (requires (elems_invariants h0 ll))
  (ensures (
    let filtered = gfilter_gen filter_all fspec ll in
    elems_invariants h0 filtered /\
    B.loc_includes (elems_footprint ll) (elems_footprint filtered)))

#push-options "--fuel 1 --ifuel 1"
let rec filtered_footprint_invariants_lem #dt filter_all fspec ll h0 =
  match ll with
  | [] -> ()
  | x :: ll' -> filtered_footprint_invariants_lem #dt filter_all fspec ll' h0
#pop-options

(** Non-tail call recursive versions of filter and filter_one *)
    
/// A generic signature which is used both for filter and filter_one
inline_for_extraction noextract
let ll1_filter_ntc_gen_st (filter_all : bool) // if true: filter, if false: filter_one
  =
     #dt: stateful unit
  -> l_ref : Ghost.erased B.loc
  -> #inv : (HS.mem -> G.erased Type0)
  -> #inv_lem : ll1_pred_inv_lem #dt l_ref inv
  -> #fspec : G.erased (fspec_ty dt)
  -> f : ll1_pred_st l_ref l_ref inv inv_lem fspec
  -> ll: LL1.t (dt_s dt)
  -> llv : Ghost.erased (list (dt_s dt)) ->
  ST (LL1.t (dt_s dt) & Ghost.erased (list (dt_s dt)))
  (requires fun h0 ->
    inv h0 /\
    B.live h0 ll /\
    elements_list_invariant h0 ll llv /\
    B.loc_includes l_ref (elements_list_footprint h0 ll llv))
  (ensures fun h0 (ll', llv') h1 ->
    B.(modifies (elements_list_footprint h0 ll llv) h0 h1) /\
    elements_list_invariant h1 ll' llv' /\
    B.live h1 ll' /\
    B.loc_includes (LL1.footprint h0 ll llv) (LL1.footprint h1 ll' llv') /\
    B.loc_includes (elems_footprint llv) (elems_footprint llv') /\
    begin
    let filtered = gfilter_gen filter_all (fun x -> G.reveal fspec (dt_v h0 x)) llv in
    G.reveal llv' == filtered /\
    gsame_elementsp filtered h0 h1
    end)

inline_for_extraction noextract
val ll1_filter_ntc : ll1_filter_ntc_gen_st true

inline_for_extraction noextract
val ll1_filter_one_ntc : ll1_filter_ntc_gen_st false

#push-options "--fuel 1 --ifuel 1"
let rec ll1_filter_ntc #dt l_ref #inv #inv_lem #fspec f ll llv =
  (**) let h0 = get () in
  if B.is_null ll then (ll, llv)
  else
    begin
    let c = B.index ll 0ul in
    [@inline_let] let x = c.LL1.data in
    [@inline_let] let next = c.LL1.next in
    (**) let h1 = get () in
    (**) inv_lem h0 B.loc_none h1;
    let (ll', llv') = ll1_filter_ntc #dt l_ref #inv #inv_lem #fspec f next (L.tl llv) in
    (**) let h2 = get () in
    begin
    (**) let llv' = L.tl llv in
    (**) let l = elements_list_footprint h1 next llv' in
    (**) assert(B.modifies l h1 h2);
    (**) elems_pairwise_disjoint_implies_disjoint_from_footprint x llv';
    (**) dt_frame_invariant l x h1 h2;
    (**) dt_frame_freeable l x h1 h2;
    (**) inv_lem h1 l h2
    end;
    let b = f x in
    (**) let h3 = get () in
    (**) inv_lem h2 B.loc_none h3;
    (**) dt_frame_invariant B.loc_none x h2 h3;
    (**) dt_frame_freeable B.loc_none x h2 h3;
    (**) elements_list_frame_invariant ll' llv' B.loc_none h2 h3;
    if b then
      begin
      B.upd ll 0ul ({LL1.data = x; LL1.next = ll'});
      (**) let h4 = get () in
      begin
      (**) let l = B.loc_buffer ll in
      (**) dt_frame_invariant l x h3 h4;
      (**) dt_frame_freeable l x h3 h4;
      (**) elements_list_frame_invariant ll' llv' l h3 h4
      end;
      [@inline_let] let r = (ll, Ghost.hide (x :: Ghost.reveal llv')) in
      begin
      (**) let ll'', llv'' = r in
      (**) disjoint_from_footprint_implies_elems_pairwise_disjoint x llv';
      (**) assert(elements_list_invariant h4 ll'' llv'')
      end;
      r
      end
    else
      begin
      // Free the cell
      dt_free #dt x;
      B.free ll;
      (**) let h4 = get () in
      begin
      (**) let l = B.loc_union (dt_footprint #dt x) (B.loc_addr_of_buffer ll) in
      (**) assert(B.modifies l h2 h3);
      (**) elements_list_frame_invariant ll' llv' l h3 h4
      end;
      (ll', llv')
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec ll1_filter_one_ntc #dt l_ref #inv #inv_lem #fspec f ll llv =
  (**) let h0 = get () in
  if B.is_null ll then (ll, llv)
  else
    begin
    let c = B.index ll 0ul in
    [@inline_let] let x = c.LL1.data in
    [@inline_let] let next = c.LL1.next in
    (**) let h1 = get () in
    (**) inv_lem h0 B.loc_none h1;
    let b = f x in
    (**) let h2 = get () in
    begin
    (**) let ll' = next in
    (**) let llv' = L.tl llv in
    (**) inv_lem h1 B.loc_none h2;
    (**) dt_frame_invariant B.loc_none x h1 h2;
    (**) dt_frame_freeable B.loc_none x h1 h2;
    (**) elements_list_frame_invariant ll' llv' B.loc_none h1 h2;
    (**) elems_pairwise_disjoint_implies_disjoint_from_footprint x (L.tl llv)
    end;
    if b then
      begin
      let (ll', llv') = ll1_filter_one_ntc #dt l_ref #inv #inv_lem #fspec f next (L.tl llv) in
      (**) let h3 = get () in
      begin
      (**) let l = elements_list_footprint h0 next (L.tl llv) in
      (**) inv_lem h2 l h3;
      (**) dt_frame_invariant l x h2 h3;
      (**) dt_frame_freeable l x h2 h3;
      (**) assert(gsame_elementsp (L.tl llv) h0 h2);
      (**) assert(
      (**)   G.reveal llv' ==
      (**)   gfilter_one (fun x -> G.reveal fspec (dt_v h2 x)) (L.tl llv));
      (**) gfilter_one_element_same_lem (L.tl llv) fspec h0 h2;
      (**) assert(
      (**)   G.reveal llv' ==
      (**)   gfilter_one (fun x -> G.reveal fspec (dt_v h0 x)) (L.tl llv))
      end;
      B.upd ll 0ul ({LL1.data = x; LL1.next = ll'});
      (**) let h4 = get () in
      begin
      (**) let l = B.loc_buffer ll in
      (**) dt_frame_invariant l x h3 h4;
      (**) dt_frame_freeable l x h3 h4;
      (**) elements_list_frame_invariant ll' llv' l h3 h4
      end;
      [@inline_let] let r = (ll, Ghost.hide (x :: Ghost.reveal llv')) in
      begin
      (**) let ll'', llv'' = r in
      (**) disjoint_from_footprint_implies_elems_pairwise_disjoint x llv';
      (**) assert(elements_list_invariant h4 ll'' llv'');
      (**) let filtered = gfilter_gen false (fun x -> G.reveal fspec (dt_v h0 x)) llv in
      (**) assert(G.reveal llv'' == filtered);
      (**) filtered_footprint_invariants_lem #dt false (fun x -> G.reveal fspec (dt_v h0 x)) llv h0;
      (**) assert(elems_invariants h0 filtered);
      (**) assert(B.loc_includes (elems_footprint llv) (elems_footprint filtered));
      (**) assert(gsame_elementsp filtered h0 h4)
      end;
      r
      end
    else
      // Free the cell
      begin
      dt_free #dt x;
      B.free ll;
      (**) let h3 = get () in
      begin
      (**) let l = B.loc_union (dt_footprint #dt x) (B.loc_addr_of_buffer ll) in
      (**) assert(B.modifies l h2 h3);
      (**) elements_list_frame_invariant next (L.tl llv) l h2 h3
      end;
      (next, G.hide (L.tl llv))
      end
    end
#pop-options

/// Some lemmas to retrieve the high-level specifications for filter/filter_one
val filter_get_elems_lem
  (#dt: stateful unit) (fspec : G.erased (fspec_ty dt))
  (h0 h1 : HS.mem) (ll : t dt) :
  Lemma
  (requires (
    gsame_elementsp (gfilter_elements fspec h0 (get_elems h0 ll)) h0 h1))
  (ensures (
    elems_v h1 (gfilter_elements fspec h0 (get_elems h0 ll)) ==
    L.filter fspec (v h0 ll)))

val filter_one_get_elems_lem
  (#dt: stateful unit) (fspec : G.erased (fspec_ty dt))
  (h0 h1 : HS.mem) (ll : t dt) :
  Lemma
  (requires (
    gsame_elementsp (gfilter_one_element fspec h0 (get_elems h0 ll)) h0 h1))
  (ensures (
    elems_v h1 (gfilter_one_element fspec h0 (get_elems h0 ll)) ==
    filter_one fspec (v h0 ll)))

val filter_get_elems_aux_lem
  (#dt: stateful unit) (fspec : G.erased (fspec_ty dt))
  (h0 h1 : HS.mem) (ll : list (dt_s dt)) :
  Lemma
  (requires (
    gsame_elementsp (gfilter_elements fspec h0 ll) h0 h1))
  (ensures (
    elems_v h1 (gfilter_elements fspec h0 ll) ==
    L.filter fspec (elems_v h0 ll)))

#push-options "--fuel 1 --ifuel 1"
let rec filter_get_elems_aux_lem #dt fspec h0 h1 ll =
  match ll with
  | [] -> ()
  | x :: ll' ->
    let ll1 = elems_v h1 (gfilter_elements fspec h0 ll) in
    let ll1' = elems_v h1 (gfilter_elements fspec h0 ll') in
    // This is strange: we need those assert_norm here
    assert_norm(ll1 == gmap (fun x -> dt_v h1 x) (gfilter (fun x -> Ghost.reveal fspec (dt_v h0 x)) ll));
    assert_norm(ll1' == gmap (fun x -> dt_v h1 x) (gfilter (fun x -> Ghost.reveal fspec (dt_v h0 x)) ll'));
    assert(
      ll1 ==
      gmap (fun x -> dt_v h1 x) (gfilter (fun x -> Ghost.reveal fspec (dt_v h0 x)) (x :: ll')));
    assert(
      ll1 ==
      gmap (fun x -> dt_v h1 x)
           (let ll' = gfilter (fun x -> Ghost.reveal fspec (dt_v h0 x)) ll' in
            if G.reveal fspec (dt_v h0 x) then x :: ll' else ll'));
    filter_get_elems_aux_lem fspec h0 h1 ll'
#pop-options

let filter_get_elems_lem #dt fspec h0 h1 ll =
  let ll = B.deref h0 ll.elems in
  filter_get_elems_aux_lem #dt fspec h0 h1 ll

val filter_one_get_elems_aux_lem
  (#dt: stateful unit) (fspec : G.erased (fspec_ty dt))
  (h0 h1 : HS.mem) (ll : list (dt_s dt)) :
  Lemma
  (requires (
    gsame_elementsp (gfilter_one_element fspec h0 ll) h0 h1))
  (ensures (
    elems_v h1 (gfilter_one_element fspec h0 ll) ==
    filter_one fspec (elems_v h0 ll)))

#push-options "--fuel 1 --ifuel 1"
let rec filter_one_get_elems_aux_lem #dt fspec h0 h1 ll =
  match ll with
  | [] -> ()
  | x :: ll' ->
    let ll1 = elems_v h1 (gfilter_one_element fspec h0 ll) in
    let ll1' = elems_v h1 (gfilter_one_element fspec h0 ll') in
    // This is strange: we need those assert_norm here
    assert_norm(ll1 == gmap (fun x -> dt_v h1 x) (gfilter_one (fun x -> Ghost.reveal fspec (dt_v h0 x)) ll));
    assert_norm(ll1' == gmap (fun x -> dt_v h1 x) (gfilter_one (fun x -> Ghost.reveal fspec (dt_v h0 x)) ll'));

    let filtered1 = gfilter_one_element fspec h0 ll in
    assert(filtered1 == gfilter_one_element fspec h0 (x::ll'));
    assert(filtered1 == gfilter_one (filter_pred fspec h0) (x::ll'));
    assert(filtered1 ==
      (if filter_pred fspec h0 x then x :: gfilter_one (filter_pred fspec h0) ll' else ll'));
    // And this one!!!
    assert_norm(filter_pred fspec h0 x = G.reveal fspec (dt_v h0 x));
    if filter_pred fspec h0 x then
      begin
      filter_one_get_elems_aux_lem fspec h0 h1 ll';
      assert(
        elems_v h1 (gfilter_one_element fspec h0 ll') ==
        filter_one fspec (elems_v h0 ll'));
      assert(
        elems_v h1 (gfilter_one_element fspec h0 ll) ==
        dt_v h1 x :: elems_v h1 (gfilter_one_element fspec h0 ll'))
      end
    else
      gsame_elementsp_elems_v_lem ll' h0 h1
#pop-options

let filter_one_get_elems_lem #dt fspec h0 h1 ll =
  let ll = B.deref h0 ll.elems in
  filter_one_get_elems_aux_lem #dt fspec h0 h1 ll

val filter_ntc : filter_st

#push-options "--fuel 1 --ifuel 1"
let filter_ntc #dt ll #inv #inv_lem #fspec f =
  (**) let h0 = get () in
  let llt = !* ll.ptr in
  let llv = !* ll.elems in
  (**) let h1 = get () in
  (**) assert(invariant h1 ll);
  let llt', llv' = ll1_filter_ntc #dt (region_of ll) #inv #(fun h0 _ h1 -> inv_lem h0 h1) #fspec f llt llv in
  (**) let h1 = get () in
  B.upd ll.ptr 0ul llt';
  B.upd ll.elems 0ul llv';
  (**) let h2 = get () in
  begin
  (**) let l = B.(loc_union (loc_buffer ll.ptr) (loc_buffer ll.elems)) in
  (**) elements_list_frame_invariant llt' llv' l h1 h2;
  (**) let filtered = gfilter_elements fspec h0 (get_elems h0 ll) in
  (**) filter_get_elems_lem fspec h0 h2 ll;
  (**) assert(gsame_elementsp filtered h0 h2);
  (**) assert(get_elems h2 ll == filtered);
  (**) assert(v h2 ll == L.filter fspec (v h0 ll))
  end
#pop-options

/// For now, the filter implementation is recursive and non tail-call.
/// TODO: implement a tail-call version.
let filter = filter_ntc

val filter_one_ntc : filter_one_st

#push-options "--fuel 1 --ifuel 1"
let filter_one_ntc #dt ll #inv #inv_lem #fspec f =
  (**) let h0 = get () in
  let llt = !* ll.ptr in
  let llv = !* ll.elems in
  (**) let h1 = get () in
  (**) assert(invariant h1 ll);
  let llt', llv' = ll1_filter_one_ntc #dt (region_of ll) #inv #(fun h0 _ h1 -> inv_lem h0 h1) #fspec f llt llv in
  (**) let h1 = get () in
  B.upd ll.ptr 0ul llt';
  B.upd ll.elems 0ul llv';
  (**) let h2 = get () in
  begin
  (**) let l = B.(loc_union (loc_buffer ll.ptr) (loc_buffer ll.elems)) in
  (**) elements_list_frame_invariant llt' llv' l h1 h2;
  (**) let filtered = gfilter_one_element fspec h0 (get_elems h0 ll) in
  (**) filter_one_get_elems_lem fspec h0 h2 ll;
  (**) assert(gsame_elementsp filtered h0 h2);
  (**) assert(get_elems h2 ll == filtered);
  (**) assert(v h2 ll == filter_one fspec (v h0 ll))
  end
#pop-options

(** Tail-call version of filter_one *)
    
/// A generic signature which is used both for filter and filter_one
inline_for_extraction noextract
let ll1_filter_one_tc_st =
     #dt: stateful unit
  -> l_ref : Ghost.erased B.loc
  -> #inv : (HS.mem -> G.erased Type0)
  -> #inv_lem : ll1_pred_inv_lem #dt l_ref inv
  -> #fspec : G.erased (fspec_ty dt)
  -> f : ll1_pred_st l_ref l_ref inv inv_lem fspec
  -> ll: LL1.t (dt_s dt)
  -> llv : Ghost.erased (list (dt_s dt)) ->
  ST unit
  (requires fun h0 ->
    inv h0 /\
    B.live h0 ll /\
    elements_list_invariant h0 ll llv /\
    B.loc_includes l_ref (elements_list_footprint h0 ll llv) /\
    // The head of the list must always be valid (with regards to the
    // filtering predicate: we always test and filter the next element
    not (B.g_is_null ll) /\
    Ghost.reveal fspec (dt_v h0 (B.deref h0 ll).LL1.data))
  (ensures (fun h0 _ h1 ->
    let filtered = gfilter_one_element fspec h0 llv in
    B.(modifies (elements_list_footprint h0 ll llv) h0 h1) /\
    B.live h1 ll /\ // TODO: useful?
    elements_list_invariant h1 ll filtered /\
    B.loc_includes (LL1.footprint h0 ll llv) (LL1.footprint h1 ll filtered) /\
    B.loc_includes (elems_footprint llv) (elems_footprint filtered) /\
    gsame_elementsp filtered h0 h1))

inline_for_extraction noextract
val ll1_filter_one_tc : ll1_filter_one_tc_st

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let rec ll1_filter_one_tc #dt l_ref #inv #inv_lem #fspec f ll llv =
  (**) let h0 = get () in
  let c0 : LL1.cell (dt_s dt) = B.index ll 0ul in
  [@inline_let] let x0 = c0.LL1.data in
  [@inline_let] let next0 = c0.LL1.next in  
  if B.is_null next0 then ()
  else
    begin
    let c1 : LL1.cell (dt_s dt) = B.index next0 0ul in
    [@inline_let] let x1 = c1.LL1.data in
    [@inline_let] let next1 = c1.LL1.next in
    let b = f x1 in
    (**) let h2 = get () in
    begin
    (**) let ll' = next0 in
    (**) let llv' = L.tl llv in
    (**) inv_lem h0 B.loc_none h2;
    (**) dt_frame_invariant B.loc_none x1 h0 h2;
    (**) dt_frame_freeable B.loc_none x1 h0 h2;
    (**) elements_list_frame_invariant ll' llv' B.loc_none h0 h2;
    (**) elems_pairwise_disjoint_implies_disjoint_from_footprint x0 llv'
    end;
    if b then
      begin
      ll1_filter_one_tc #dt l_ref #inv #inv_lem #fspec f next0 (L.tl llv);
      (**) let h3 = get () in
      begin
      (**) let l = elements_list_footprint h0 next0 (L.tl llv) in
      (**) inv_lem h2 l h3;
      (**) dt_frame_invariant l x0 h2 h3;
      (**) dt_frame_freeable l x0 h2 h3;
      (**) assert(gsame_elementsp (L.tl llv) h0 h2)
      end;
      begin
      (**) let filtered_end0 = gfilter_one_element fspec h0 (L.tl llv) in
      (**) let filtered_end2 = gfilter_one_element fspec h2 (L.tl llv) in
      (**) let filtered = gfilter_one_element fspec h0 llv in
      (**) let x0 :: filtered_end0' = filtered in
      (**) gfilter_one_element_same_lem (L.tl llv) fspec h0 h2;
      (**) assert(filtered_end0 == filtered_end2);
      (**) assert(filtered_end0 == filtered_end0');
      (**) assert(elems_pairwise_disjoint #dt filtered_end0);
      (**) gfilter_one_element_cons_elems_pairwise_disjoint x0 (L.tl llv) fspec h0;
      (**) assert(elems_pairwise_disjoint #dt filtered);
      (**) assert(elements_list_invariant h3 ll filtered)
      end
      end
    else
      // Free the cell
      begin
      begin
      (**) let x0 :: x1 :: llv_end = G.reveal llv in
      (**) assert(elements_list_invariant h2 next1 llv_end)
      end;
      B.upd ll 0ul (LL1.Mkcell next1 x0);
      (**) let h3 = get () in
      dt_free #dt x1;
      B.free next0;
      (**) let h5 = get () in
      begin
      (**) let filtered = gfilter_one_element fspec h0 llv in
      (**) let x0 :: x1 :: llv_end = G.reveal llv in
      (**) let l1 = B.loc_buffer ll in
      (**) let l2 = B.(loc_union (dt_footprint x1) (loc_addr_of_buffer next0)) in
      (**) let l3 = B.loc_union l1 l2 in
      (**) assert(B.(modifies l1 h2 h3));
      (**) assert(B.(modifies l2 h3 h5));
      (**) assert(filtered == x0 :: llv_end);
      (**) dt_frame_invariant l3 x0 h2 h5;
      (**) dt_frame_freeable l3 x0 h2 h5;
      (**) elems_pairwise_disjoint_implies_disjoint_from_footprint x1 llv_end;
      (**) assert(B.loc_disjoint l3 (elements_list_footprint h2 next1 llv_end));
      (**) elements_list_frame_invariant next1 llv_end l3 h2 h5;
      (**) assert(elements_list_invariant h5 next1 llv_end);
      (**) assert(elements_list_invariant h5 ll filtered)
      end
      end
    end
#pop-options

// Filter one if the head is a valid element with regards to the filtering predicate
val filter_one_tc_valid_head :
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
       filter_one_st_pre ll inv fspec h0 /\
       Cons? (get_elems h0 ll) /\
       G.reveal fspec (dt_v h0 (Cons?.hd (get_elems h0 ll))))
    (ensures fun h0 _ h1 -> filter_one_st_post ll inv fspec h0 h1)

#push-options "--fuel 1 --ifuel 1"
let filter_one_tc_valid_head #dt ll #inv #inv_lem #fspec f =
  (**) let h0 = get () in
  let llt = !* ll.ptr in
  let llv = !* ll.elems in
  (**) let h1 = get () in
  (**) assert(invariant h1 ll);
  ll1_filter_one_tc #dt (region_of ll) #inv #(fun h0 _ h1 -> inv_lem h0 h1) #fspec f llt llv;
  (**) let h1 = get () in
  B.upd ll.elems 0ul (gfilter_one_element fspec h0 (get_elems h0 ll));
  (**) let h2 = get () in
  begin
  (**) let l = B.(loc_buffer ll.elems) in
  (**) let filtered = gfilter_one_element fspec h0 (get_elems h0 ll) in
  (**) elements_list_frame_invariant llt filtered l h1 h2;
  (**) filter_one_get_elems_lem fspec h0 h2 ll;
  (**) assert(gsame_elementsp filtered h0 h2);
  (**) assert(get_elems h2 ll == filtered);
  (**) assert(v h2 ll == filter_one fspec (v h0 ll))
  end
#pop-options

val filter_one_tc : filter_one_st

#push-options "--fuel 2 --ifuel 2"
let filter_one_tc #dt ll #inv #inv_lem #fspec f =
  let llt = !* ll.ptr in
  if B.is_null llt then ()
  else
    begin
    let c0 = !* llt in
    [@inline_let] let x0 = c0.LL1.data in
    if f x0 then 
      filter_one_tc_valid_head ll f
    else
      pop ll
    end
#pop-options

(** Loop version of filter_one *)
/// In order to keep the proofs for the loop versions as close as possible to
/// the proofs for the recursive versions, we use the following strategy:
/// - we remark that in the tail-call version, after the recursive call, the
///   post-condition of the recursive function gives us that the end of the list
///   has been modified in some proper way, following which we prove
///   that the whole list has been modified in the proper way (i.e.: filtered).
/// - for the loop version, we thus decided to keep in the invariant the fact that
///   it is enough to modify the end of the list in a some specific way, in order
///   to get that the whole list has been properly filtered.
/// - of course, it is a bit more subtle than for the recursive version, because
///   in the loop version, we locally work at an arbitrary position in the list,
///   while in the recursive version, the end of the list is simply the current
///   list minus its head. The ideas behind the proofs still remain the same.
/// - this approach is equivalent to using a magic-wand in separation logic,
///   which is why we often refer to the aformentionned property (it is enough
///   to correctly modify the end of the loop) as the magic-wand property.
/// In practice, once again, having implemented the recursive tail-call version
/// proved very useful: going back to the recursive version was a good way to find
/// out why Z3 could not prove some proof obligations, or which lemmas to call, etc.

/// We need to split between two cases:
/// - either the head of the list must be filtered, in which case we simply
///   call pop
/// - or the head of the list is valid, in which case we do a recursive traversal
///   of the list (with a loop)
/// The reason is that, in order to be able to correctly update the list, we need
/// to keep a pointer to the element before the one we filter (because we then update
/// this element so that its [next] component points to the element after next).
/// For the recursive traversal, we start by implementing a [filter_one_find_loop]
/// function, which traverses the list looking for an element to filter by updating
/// a pointer [lltp] at each iteration. After the call to [filter_one_find_loop],
/// it leaves [lltp] in a position such that:
/// - either the next element is null because we reached the end of the list, in which
///   case there is nothing to do
/// - or the next element is not null, in which case it does not satisfy the filtering
///   predicate and needs to be removed
/// Of course, the [filter_one_find_loop] function contains the magic wand property
/// in its postcondition, to prove that once the proper element is removed (if needs
/// be), the whole list has been filtered.

let filter_one_find_loop_magic_wand_pre
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h0 : HS.mem) : GTot Type0 =
  let llt = B.deref h0 lltp in
  let llv = B.deref h0 llvp in
  inv h0 /\
  B.live h0 llt /\
  elements_list_invariant h0 llt llv /\
  B.loc_disjoint l_mod (elements_list_footprint h0 llt llv) /\
  not (B.g_is_null llt) /\
  Cons? llv

#push-options "--ifuel 1 --fuel 1"
let filter_one_find_loop_magic_wand_post
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h0 h1 : HS.mem) :
  Ghost Type0
  (requires (filter_one_find_loop_magic_wand_pre l_all l_mod lltp llvp f h0))
  (ensures (fun _ -> True)) =
  let llt = B.deref h0 lltp in
  let llv = B.deref h0 llvp in
  let llt' = llt in
  let filtered = gfilter_one_element fspec h0 llv in
  B.(modifies (B.loc_union l_mod (elements_list_footprint h0 llt llv)) h0 h1) /\
  elements_list_invariant h1 llt' filtered /\
  B.live h1 llt' /\
  B.loc_includes (LL1.footprint h0 llt llv) (LL1.footprint h1 llt' filtered) /\
  B.loc_includes (elems_footprint llv) (elems_footprint filtered) /\
  gsame_elementsp filtered h0 h1
#pop-options

let filter_one_find_loop_magic_wand
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  // Pointer to the beginning of the list
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  // Pointer to the current list element - we need to test the next one
  (lltp : B.pointer (LL1.t (dt_s dt)))
  // The current list of elements
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00 h0 h1 : HS.mem) : GTot Type0 =
  filter_one_find_loop_magic_wand_pre l_all l_mod lltp00 llvp f h00 /\
  B.(loc_disjoint l_mod (loc_addr_of_buffer lltp00)) /\
  B.(modifies l_mod h00 h0) /\
  ST.equal_stack_domains h00 h0 /\
  (begin
   filter_one_find_loop_magic_wand_pre l_all l_mod lltp llvp f h0 /\
   filter_one_find_loop_magic_wand_post l_all l_mod lltp llvp f h0 h1
   end ==>
   filter_one_find_loop_magic_wand_post l_all l_mod lltp00 llvp f h00 h1)

let filter_one_find_loop_pre
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt))) // Points to the beginning of the list
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec) =
  (fun h0 ->
    let llt00 = B.deref h0 lltp00 in
    let llt = B.deref h0 lltp in
    let llv = B.deref h0 llvp in
    B.live h0 lltp00 /\ B.deref h0 lltp00 == llt /\ // TODO: this duplicates filter_one_find_inv_aux
    B.live h0 lltp /\ B.live h0 llt /\ B.live h0 llvp /\
    elements_list_invariant h0 llt llv /\
    inv h0 /\
    // The element pointed to by lltp is not null, and satisfies fspec
    not (B.g_is_null llt) /\
    begin
    let c = B.deref h0 llt in
    Ghost.reveal fspec (dt_v h0 c.LL1.data)
    end /\
    // Aliasing
    begin
    let tp00_loc = B.loc_addr_of_buffer lltp00 in
    let tp_loc = B.loc_addr_of_buffer lltp in
    let vp_loc = B.loc_addr_of_buffer llvp in
    let ll_loc = elements_list_footprint h0 llt llv in
    B.all_disjoint [tp00_loc; tp_loc; vp_loc; ll_loc] /\
    G.reveal l_mod == B.(loc_buffer lltp `loc_union` loc_buffer llvp) /\
    B.loc_includes l_all ll_loc
    end)

let filter_one_find_loop_post
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt))) // Points to the beginning of the list
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h0 : HS.mem) () (h1 : HS.mem) :
  Ghost Type0
  (requires (filter_one_find_loop_pre l_all l_mod lltp00 lltp llvp f h0))
  (ensures (fun _ -> True)) =
  let llv0 = B.deref h0 llvp in
  let llv1 = B.deref h1 llvp in
  let llt0 = B.deref h0 lltp in
  let llt1 = B.deref h1 lltp in
  B.(modifies l_mod h0 h1) /\
  B.live h1 lltp /\ B.live h1 llt1 /\ B.live h1 llvp /\
  elements_list_invariant h1 llt1 llv1 /\
  inv h1 /\
  // The magic wand and the below match give us that if we filter (if needs be)
  // the element next to the one pointed to by lltp after the call to
  // [filter_one_find_loop], we get that the whole list has been filtered.
  (forall h2. filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h0 h1 h2) /\
  not (B.g_is_null llt1) /\
  Ghost.reveal fspec (dt_v h1 (B.deref h1 llt1).LL1.data) /\
  B.(loc_includes (LL1.footprint h0 llt0 llv0) (LL1.footprint h1 llt1 llv1)) /\
  B.(loc_includes (elems_footprint llv0) (elems_footprint llv1)) /\
  begin
  let next1 = (B.deref h1 llt1).LL1.next in
  match not (B.g_is_null next1) with
  | false -> True // nothing special
  | true ->
    let c = B.deref h1 next1 in
    not (Ghost.reveal fspec (dt_v h1 c.LL1.data))
  end

/// The main part of the [find] function, which contains the while loop
inline_for_extraction noextract
val filter_one_find_loop
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt))) // Points to the beginning of the list
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec) :
  Stack unit
  (requires filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f)
  (ensures (fun h0 () h1 ->
    filter_one_find_loop_post #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h0 () h1))

inline_for_extraction noextract
let filter_one_find_loop_inv_aux
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt))) // Points to the beginning of the list
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
=
  fun h0 ->
  let llt0 = B.deref h00 lltp in
  let llv0 = B.deref h00 llvp in
  let llt = B.deref h0 lltp in
  let llv = B.deref h0 llvp in
  B.live h00 lltp00 /\ B.deref h00 lltp00 == llt0 /\
  B.live h0 lltp /\ B.live h0 llt /\ B.live h0 llvp /\
  elements_list_invariant h0 llt llv /\
  gsame_elementsp #dt llv h00 h0 /\
  inv h0 /\
  // The element pointed to by lltp is not null, and satisfies fspec
  not (B.g_is_null llt) /\
  begin
  let c = B.deref h0 llt in
  Ghost.reveal fspec (dt_v h0 c.LL1.data)
  end /\
  // Aliasing
  begin
  let spine0_loc = LL1.footprint h00 llt0 llv0 in
  let spine_loc = LL1.footprint h0 llt llv in
  let elems0_loc = elems_footprint llv0 in
  let elems_loc = elems_footprint llv in
  B.loc_includes spine0_loc spine_loc /\
  B.loc_includes elems0_loc elems_loc /\
  B.(modifies (loc_union (loc_buffer lltp) (loc_buffer llvp)) h00 h0) /\
  list_in_listP llv llv0 /\
  B.(all_disjoint [
    loc_addr_of_buffer lltp00;
    loc_addr_of_buffer lltp;
    loc_addr_of_buffer llvp;
    spine0_loc;
    elems0_loc]) /\
  G.reveal l_mod == B.(loc_union (loc_buffer lltp) (loc_buffer llvp))
  end

inline_for_extraction noextract
let filter_one_find_loop_inv
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt))) // Points to the beginning of the list
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
=
  fun h0 ->
  filter_one_find_loop_inv_aux l_all l_mod lltp00 lltp llvp f h00 h0 /\
  (forall h1. filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h1)

// This lemma is not applied in many situations, but is very useful as a sanity
// check.
let filter_one_find_loop_magic_wand_frame_lem1
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
  (h0 h0' h1 : HS.mem) :
  Lemma
  (requires (
    filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h1 /\
    filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h0' /\
    B.(modifies loc_none h0 h0') /\
    ST.equal_stack_domains h0 h0'))
  (ensures (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0' h1))
  [SMTPat (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h1);
   SMTPat (B.(modifies loc_none h0 h0'))] =
  ()

#push-options "--ifuel 1 --fuel 1"
let filter_one_find_loop_magic_wand_frame_lem2
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
  (h0 h1 h2 : HS.mem) :
  Lemma
  (requires (
    filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h2 /\
    filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h0 /\
    B.(modifies loc_none h0 h1) /\
    ST.equal_stack_domains h0 h1))
  (ensures (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h1 h2))
  [SMTPat (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h2);
   SMTPat (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h1 h2);
   SMTPat (B.(modifies loc_none h0 h1))] =
  assert(filter_one_find_loop_magic_wand_pre l_all l_mod lltp00 llvp f h00);
  if IndefiniteDescription.strong_excluded_middle
    (filter_one_find_loop_magic_wand_pre l_all l_mod lltp llvp f h1 /\
     filter_one_find_loop_magic_wand_post l_all l_mod lltp llvp f h1 h2) then
    begin
    let llt = B.deref h0 lltp in
    let llv = B.deref h0 llvp in
    let llt' = B.deref h2 lltp in
    let filtered = gfilter_one_element fspec h0 llv in
    assert(gsame_elementsp filtered h0 h2);
    assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp llvp f h0 h2);
    assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp00 llvp f h00 h2)
    end
#pop-options

// Same as above lemma: we use this one in only one place, but define this lemma
// anyway because: it is easier to work on it in an independant, small context,
// and because it allows us to check for sanity.
#push-options "--ifuel 1 --fuel 1"
let filter_one_find_loop_magic_wand_init_lem_
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem {
    filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
  (h1 : HS.mem) :
  Lemma
  (requires (
    filter_one_find_loop_inv_aux #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h00 ))
  (ensures (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h00 h1))
  =
  assert(filter_one_find_loop_magic_wand_pre l_all l_mod lltp00 llvp f h00);
  if FStar.IndefiniteDescription.strong_excluded_middle
    (filter_one_find_loop_magic_wand_pre l_all l_mod lltp llvp f h00 /\
     filter_one_find_loop_magic_wand_post l_all l_mod lltp llvp f h00 h1)
  then
    begin
    let llt = B.deref h00 lltp00 in
    let llv = B.deref h00 llvp in
    let llt' = B.deref h1 lltp00 in
    let filtered = gfilter_one_element fspec h00 llv in
    assert(elements_list_invariant h1 llt' filtered);
    assert(B.live h1 llt');
    assert(B.loc_includes (LL1.footprint h00 llt llv) (LL1.footprint h1 llt' filtered));
    assert(
      B.loc_includes (elems_footprint llv) (elems_footprint filtered) /\
      gsame_elementsp filtered h00 h1);
    assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp00 llvp f h00 h1)
    end
  else ()
#pop-options

#push-options "--ifuel 1 --fuel 1"
let filter_one_find_loop_magic_wand_init_lem
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem {
    filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 }) :
  Lemma
  (requires (
    filter_one_find_loop_inv_aux #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h00 ))
  (ensures (forall (h1 : HS.mem). filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h00 h1))
  =
  // Classical.forall_intro doesn't work
  let lem (h1 : HS.mem) :
    Lemma (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h00 h1)
    [SMTPat (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h00 h1)] =
    filter_one_find_loop_magic_wand_init_lem_ l_all l_mod lltp00 lltp llvp f h00 h1
  in
  ()
#pop-options

inline_for_extraction noextract
let filter_one_find_loop_guard
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
  (h0:HS.mem{filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h0}): GTot bool =
  let llt = B.deref h0 lltp in
  let next = (B.deref h0 llt).LL1.next in
  if B.g_is_null next then false
  else
    let x = (B.deref h0 next).LL1.data in
    Ghost.reveal fspec (dt_v h0 x)

#push-options "--fuel 2 --ifuel 2"
inline_for_extraction noextract
let filter_one_find_loop_test
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
  ():
  Stack bool (requires filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00)
  (ensures  fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    b == filter_one_find_loop_guard #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h0) =
  (**) let h0 = get () in
  let llt = B.index lltp 0ul in
  let next = (B.index llt 0ul).LL1.next in
  let llv = B.index llvp 0ul in
  if B.is_null next then
    false
  else
    begin
    let c = B.index next 0ul in
    (**) let h1 = get () in
    [@inline_let] let x = c.LL1.data in
    begin
    (**) inv_lem h0 B.loc_none h1;
    (**) dt_frame_invariant #dt B.loc_none x h0 h1;
    (**) dt_frame_freeable #dt B.loc_none x h0 h1;
    (**) LL1.frame llt llv B.loc_none h0 h1;
    (**) elems_frame_invariant #dt llv B.loc_none h0 h1
    end;
    let b = f x in
    (**) let h2 = get () in
    (**) inv_lem h1 B.loc_none h2;
    (**) dt_frame_invariant #dt B.loc_none x h1 h2;
    (**) dt_frame_freeable #dt B.loc_none x h1 h2;
    (**) LL1.frame llt llv B.loc_none h1 h2;
    (**) elems_frame_invariant #dt llv B.loc_none h1 h2;
    b
    end
#pop-options

// Because there is an indirection (we test the "next" element, not the current
// one), we need fuel and ifuel 2.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
inline_for_extraction noextract
let filter_one_find_loop_test_
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
  ():
  Stack bool (requires
    filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00)
  (ensures  fun _ b h ->
    filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h /\
    b == filter_one_find_loop_guard #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h)
=
  (**) let h0 = get () in
  (**) assert(inv h0);
  let b = filter_one_find_loop_test #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 () in
  (**) let h1 = get () in
  begin
  (**) let llt = B.deref h0 lltp in
  (**) let llv = B.deref h0 llvp in
  (**) elements_list_frame_invariant #dt llt llv B.loc_none h0 h1;
  (**) inv_lem h0 B.loc_none h1;
  (**) assert(inv h1);
  (**) assert(filter_one_find_loop_inv_aux l_all l_mod lltp00 lltp llvp f h00 h1);
  (**) assert(filter_one_find_loop_magic_wand_pre l_all l_mod lltp00 llvp f h00);
  (**) assert(forall h2. filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h1 h2);
  (**) assert(filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h1)
  end;
  b
#pop-options

let _ = ()

inline_for_extraction noextract
val filter_one_find_loop_body
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (lltp00 : B.pointer (LL1.t (dt_s dt))) // Points to the beginning of the list
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00: HS.mem { filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 })
  :
  unit -> Stack unit
  (requires (fun h0 ->
    filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h0 /\
    filter_one_find_loop_guard #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h0))
  (ensures  (fun _ _ h1 ->
    filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h1))

#push-options "--z3rlimit 300 --fuel 2 --ifuel 2"
let filter_one_find_loop_body #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 () =
  (**) let h0 = get () in
  let llt = B.index lltp 0ul in
  let llv = B.index llvp 0ul in
  (**) assert(elements_list_invariant h0 llt llv);
  let c = B.index llt 0ul in
  B.upd lltp 0ul c.LL1.next;
  B.upd llvp 0ul (L.tl llv);
  (**) let h1 = get () in
  (**) assert(elements_list_invariant h1 (B.deref h1 lltp) (B.deref h1 llvp));
  (**) assert(B.(modifies l_mod h0 h1));
  begin
  (**) assert(B.modifies l_mod h0 h1);
  (**) inv_lem h0 l_mod h1;
  (**) LL1.frame llt llv l_mod h0 h1;
  (**) elems_frame_invariant llv l_mod h0 h1;

  (**) let magic_wand (h2 : HS.mem) :
  (**)   Lemma(filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h1 h2)
  (**)   [SMTPat (filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h1 h2)] =
  (**)   assert(filter_one_find_loop_magic_wand_pre l_all l_mod lltp00 llvp f h00);
  (**)   assert(B.(modifies l_mod h00 h1));
  (**)   assert(ST.equal_stack_domains h00 h1);
  (**)   if IndefiniteDescription.strong_excluded_middle
  (**)     (filter_one_find_loop_magic_wand_pre l_all l_mod lltp llvp f h1 /\
  (**)      filter_one_find_loop_magic_wand_post l_all l_mod lltp llvp f h1 h2)
  (**)   then
  (**)     begin
  (**)     // Apply the magic wand between h0 and h2 to get the property between h1 and h2
  (**)     assert(filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h2);
  (**)     assert(filter_one_find_loop_magic_wand_pre l_all l_mod lltp llvp f h0);

  (**)     let llt0 = B.deref h0 lltp in
  (**)     let llv0 = B.deref h0 llvp in
  (**)     let filtered0 = gfilter_one_element fspec h0 llv0 in
  (**)     let Cons x llv' = G.reveal llv0 in

  (**)     let llt1 = B.deref h1 lltp in
  (**)     let llv1 = B.deref h1 llvp in
  (**)     let filtered1 = gfilter_one_element fspec h1 llv1 in

  (**)     assert(filtered0 == x :: gfilter_one_element fspec h0 llv');
  (**)     gfilter_one_element_eq_lem fspec llv' l_mod h0 h1;
  (**)     assert(gfilter_one_element fspec h0 llv' == gfilter_one_element fspec h1 llv');
  (**)     assert(gfilter_one_element fspec h0 llv' == filtered1);

  (**)     assert(elements_list_invariant h2 llt1 filtered1);
  (**)     let next0 = (B.deref h0 llt0).LL1.next in
  (**)     assert(next0 == llt1);

  (**)     let Cons filtered0_hd filtered0_tl = filtered0 in
  (**)     let llt0_next = (B.deref h0 llt0).LL1.next in
  (**)     assert(filtered0_tl == filtered1);
  (**)     assert(llt0_next == llt1);

  (**)     assert(dt_invariant h1 filtered0_hd);
  (**)     let l12 = (B.loc_union l_mod (elements_list_footprint h1 llt1 llv1)) in
  (**)     assert(B.modifies l12 h1 h2);
  (**)     assert(B.loc_disjoint l_mod (dt_footprint filtered0_hd));
  (**)     
  (**)     elems_pairwise_disjoint_implies_disjoint_from_footprint filtered0_hd llv1;
  (**)     assert(B.loc_disjoint (elements_list_footprint h1 llt1 llv1) (dt_footprint filtered0_hd));
  (**)     assert(B.loc_disjoint l12 (dt_footprint filtered0_hd));
  (**)     assert(dt_invariant h2 filtered0_hd);

  (**)     assert(elements_list_invariant h2 llt0 filtered0);
  (**)     assert(B.live h2 llt0);
  (**)     assert(B.loc_includes (LL1.footprint h0 llt0 llv0) (LL1.footprint h2 llt0 filtered0));
  (**)     assert(B.loc_includes (elems_footprint llv0) (elems_footprint filtered0));
  (**)     assert(gsame_elementsp filtered0 h0 h2);      
  (**)     assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp llvp f h0 h2);

  (**)     assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp00 llvp f h00 h2)
  (**)     end
  (**) in
  (**) assert(forall h2. filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h1 h2);
  (**) let llt0 = B.deref h0 lltp in
  (**) let llt1 = B.deref h1 lltp in
  (**) let c0 = B.deref h0 llt0 in
  (**) let c1 = B.deref h1 llt1 in
  (**) assert(not (B.g_is_null c0.LL1.next));
  (**) let next0 = (B.deref h0 c0.LL1.next) in
  (**) assert(c1.LL1.data == next0.LL1.data);
  (**) assert(Ghost.reveal fspec (dt_v h0 next0.LL1.data));
  (**) let l = B.(loc_union (loc_buffer lltp) (loc_buffer llvp)) in
  (**) // We need fuel 2 here
  (**) dt_frame_invariant l next0.LL1.data h0 h1;
  (**) assert(Ghost.reveal fspec (dt_v h1 c1.LL1.data));
  (**) assert(filter_one_find_loop_inv_aux l_all l_mod lltp00 lltp llvp f h00 h1);

  (**) assert(forall h2. filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h1 h2);
  (**) assert(filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h1)
  end
#pop-options

let filter_one_find_loop #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f =
  (**) let h00 = get () in
  // The original list is included in itself - we need that for the invariant
  (**) list_in_listP_refl (B.deref h00 llvp);
  (**) assert(filter_one_find_loop_inv_aux #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h00);

  [@inline_let]
  let inv' : HS.mem -> Type0 =
    filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 in

  [@inline_let]
  let guard = filter_one_find_loop_guard #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 in

  [@inline_let]
  let test: unit -> Stack bool
    (requires (fun h -> inv' h))
    (ensures  fun _ b h -> inv' h /\ b == guard h)
  =
    filter_one_find_loop_test_ #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00
  in

  [@inline_let]
  let body : (unit -> Stack unit
                    (requires fun h -> inv' h /\ guard h)
                    (ensures  fun _ _ h -> inv' h)) =
    fun () ->
    filter_one_find_loop_body #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 ()
  in

  (**) filter_one_find_loop_magic_wand_init_lem l_all l_mod lltp00 lltp llvp f h00;
  (**) assert(forall h1. filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h00 h1);
  (**) assert(filter_one_find_loop_inv #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 h00);
  (**) assert(inv' h00);

  C.Loops.while #inv' #(fun b h -> inv' h /\ b == guard h) test body

/// Intermediate helper: filter a list whose head is valid (i.e.: the head
/// element satisfies the filtering predicate and thus shouldn't be filtered).
inline_for_extraction noextract
val filter_one_loop_valid_head
  (#dt: stateful unit) (ll: t dt)
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : (h0:HS.mem -> h1:HS.mem ->
               Lemma (requires (inv h0 /\ B.(modifies (region_of ll) h0 h1)))
               (ensures (inv h1))))
  (#fspec : G.erased (fspec_ty dt))
  (f : pred_st ll (region_of ll) inv inv_lem fspec) :
  ST unit
  (requires fun h0 ->
    filter_one_st_pre ll inv fspec h0 /\
    Cons? (get_elems h0 ll) /\
    G.reveal fspec (dt_v h0 (Cons?.hd (get_elems h0 ll))))
  (ensures fun h0 _ h1 ->
    filter_one_st_post ll inv fspec h0 h1)

/// Helper for [filter_one_loop_valid_head]: after the call to [filter_one_find_loop],
/// filter the next element (if we found an element to filter).
let filter_one_loop_valid_head_filter_pre
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (ll : t dt)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00 : HS.mem) // The memory snapshot before we call [filter_one_find_loop]
  (h0 : HS.mem) : GTot Type0 =
  invariant h00 ll /\
  lltp00 == ll.ptr /\
  B.deref h00 lltp00 == B.deref h00 lltp /\ // Useful?
  get_elems h00 ll == G.reveal (B.deref h00 llvp) /\
  get_elems h00 ll == get_elems h0 ll /\
  filter_one_find_loop_pre #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 /\
  filter_one_find_loop_post #dt l_all l_mod lltp00 lltp llvp #inv #inv_lem #fspec f h00 () h0 /\
  B.(modifies (loc_union (loc_buffer lltp) (loc_buffer llvp)) h00 h0) /\
  B.(equal_domains h00 h0) /\
  G.reveal l_mod == B.(loc_union (loc_buffer lltp) (loc_buffer llvp)) /\
  begin
  let llt00 = B.deref h00 lltp in
  let llv00 = B.deref h00 llvp in
  let llt0 = B.deref h0 lltp in
  let llv0 = B.deref h0 llvp in
  B.(loc_includes (LL1.footprint h00 llt00 llv00) (LL1.footprint h0 llt0 llv0)) /\
  B.(loc_includes (elems_footprint llv00) (elems_footprint llv0)) /\
  B.(all_disjoint [
    region_of ll;
    loc_addr_of_buffer lltp;
    loc_addr_of_buffer llvp;
  ])
  end

let filter_one_loop_valid_head_filter_post
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (ll : t dt)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00 : HS.mem) // The memory snapshot before we call [filter_one_find_loop]
  (h0 h1 : HS.mem) :
  Ghost Type0
  (requires (filter_one_loop_valid_head_filter_pre l_all l_mod ll lltp00 lltp llvp f h00 h0))
  (ensures (fun _ -> True)) =
  let filtered = gfilter_one_element fspec h00 (get_elems h00 ll) in
  B.(modifies (region_of ll) h0 h1) /\
  invariant h1 ll /\
  get_elems h1 ll == filtered /\
  gsame_elementsp filtered h00 h1 /\
  // The following is a consequence from the preceding assertions,
  // but not a trivial derivation and more convenient in most situations
  v h1 ll == M.filter_one fspec (v h00 ll)

inline_for_extraction noextract
val filter_one_loop_valid_head_filter
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (ll : t dt)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (Ghost.erased (list (dt_s dt))))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00 : HS.mem) // The memory snapshot before we call [filter_one_find_loop]
  :
  ST unit
  (requires (fun h0 ->
    filter_one_loop_valid_head_filter_pre l_all l_mod ll lltp00 lltp llvp f h00 h0))
  (ensures (fun h0 () h1 ->
    filter_one_loop_valid_head_filter_post l_all l_mod ll lltp00 lltp llvp f h00 h0 h1))

/// More intermediate helpers for [filter_one_loop_valid_head_filter].
/// We split between two cases:
/// - we reached the end of the list without finding any element to filter
/// - we found an element to filter

inline_for_extraction noextract
val filter_one_loop_valid_head_filter_no_element
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (ll : t dt)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (G.erased (list (dt_s dt))))
  (llt : LL1.t (dt_s dt))
  (llv : G.erased (list (dt_s dt)))
  (c0 : LL1.cell (dt_s dt))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00 : HS.mem) :
  ST unit
  (requires (fun h0 ->
    filter_one_loop_valid_head_filter_pre l_all l_mod ll lltp00 lltp llvp f h00 h0 /\
    llt == B.deref h0 lltp /\
    llv == B.deref h0 llvp /\
    c0 == B.deref h0 llt /\
    B.g_is_null c0.LL1.next))
  (ensures (fun h0 () h1 ->
    filter_one_loop_valid_head_filter_post l_all l_mod ll lltp00 lltp llvp f h00 h0 h1))

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let filter_one_loop_valid_head_filter_no_element
  #dt l_all l_mod ll lltp00 lltp llvp llt llv c0 #inv #inv_lem #fspec f h00 =
  (**) let h0 = get () in
  (**) assert(invariant h0 ll);
  begin
  (**) let h1 = h0 in
  (**) let filtered = gfilter_one_element fspec h0 llv in
  (**) let filtered_whole = gfilter_one_element fspec h00 (get_elems h00 ll) in
  (**) assert(match G.reveal llv with | [v] -> True | _ -> False);
  (**) let Cons x _ = G.reveal llv in
  (**) assert(G.reveal fspec (dt_v h0 x));
  (**) assert(filtered == G.reveal llv);
  (**) assert(LL1.well_formed h1 llt filtered);
  (**) assert(filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h1);
  (**) assert(filter_one_find_loop_magic_wand_pre l_all l_mod lltp llvp f h0);
  (**) assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp llvp f h0 h1);
  (**) assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp00 llvp f h00 h1);
  // What we get from the magic wand
  (**) let llt_whole0 = B.deref h00 lltp00 in
  (**) let llv_whole0 = B.deref h00 llvp in
  (**) let llt_whole1 = B.deref h1 lltp00 in
  (**) assert(B.(modifies (loc_union l_mod (elements_list_footprint h00 llt_whole0 llv_whole0)) h00 h1));
  (**) assert(elements_list_invariant h1 llt_whole1 filtered_whole);
  (**) assert(B.live h1 llt_whole1);
  (**) assert(B.loc_includes (LL1.footprint h00 llt_whole0 llv_whole0) (LL1.footprint h1 llt_whole1 filtered_whole));
  (**) assert(B.loc_includes (elems_footprint llv_whole0) (elems_footprint filtered_whole));
  (**) assert(gsame_elementsp filtered_whole h00 h1)
  end;
  (**) B.upd ll.elems 0ul (gfilter_one_element fspec h00 (get_elems h00 ll));
  (**) let h1 = get () in
  begin
  // The postcondition
  (**) let filtered_whole' = gfilter_one_element fspec h0 (get_elems h0 ll) in
  (**) let filtered_whole = gfilter_one_element fspec h00 (get_elems h00 ll) in
  (**) assert(filtered_whole' == filtered_whole);
  (**) assert(B.(modifies (region_of ll) h0 h1));
  (**) assert(get_elems h1 ll == filtered_whole);
  (**) assert(gsame_elementsp filtered_whole h00 h1);
  (**) filter_one_get_elems_lem fspec h00 h1 ll;
  (**) assert(v h1 ll == M.filter_one fspec (v h00 ll));

  (**) assert(invariant h1 ll)
  end
#pop-options

inline_for_extraction noextract
val filter_one_loop_valid_head_filter_one_element
  (#dt: stateful unit)
  (l_all l_mod : G.erased B.loc)
  (ll : t dt)
  (lltp00 : B.pointer (LL1.t (dt_s dt)))
  (lltp : B.pointer (LL1.t (dt_s dt)))
  (llvp : B.pointer (G.erased (list (dt_s dt))))
  (llt : LL1.t (dt_s dt))
  (llv : G.erased (list (dt_s dt)))
  (c0 : LL1.cell (dt_s dt))
  (#inv : HS.mem -> G.erased Type0)
  (#inv_lem : ll1_pred_inv_lem #dt l_mod inv)
  (#fspec : G.erased (fspec_ty dt))
  (f : ll1_pred_st l_all l_mod inv inv_lem fspec)
  (h00 : HS.mem) :
  ST unit
  (requires (fun h0 ->
    filter_one_loop_valid_head_filter_pre l_all l_mod ll lltp00 lltp llvp f h00 h0 /\
    llt == B.deref h0 lltp /\
    llv == B.deref h0 llvp /\
    c0 == B.deref h0 llt /\
    not (B.g_is_null c0.LL1.next)))
  (ensures (fun h0 () h1 ->
    filter_one_loop_valid_head_filter_post l_all l_mod ll lltp00 lltp llvp f h00 h0 h1))

#push-options "--z3rlimit 600 --fuel 2 --ifuel 2"
let filter_one_loop_valid_head_filter_one_element
  #dt l_all l_mod ll lltp00 lltp llvp llt llv c0 #inv #inv_lem #fspec f h00 =
  (**) let h0 = get () in
  
  let c1 = !* c0.LL1.next in
  B.upd llt 0ul (LL1.Mkcell c1.LL1.next c0.LL1.data);
  (**) let h1_0 = get () in
  [@inline_let]
  let x = c1.LL1.data in
  dt_free #dt x;
  (**) let h1_1 = get () in
  B.free c0.LL1.next;
  (**) let h1_2 = get () in
  begin
  (**) let h1 = h1_2 in
  (**) let filtered = gfilter_one_element fspec h0 llv in
  (**) let filtered_whole = gfilter_one_element fspec h00 (get_elems h00 ll) in
  (**) let spine_end_loc = LL1.footprint h0 llt llv in
  (**) let elems_end_loc = elems_footprint llv in
  (**) let list_end_loc = B.loc_union spine_end_loc elems_end_loc in
  (**) assert(B.(modifies spine_end_loc h0 h1_0));
  (**) assert(B.(modifies elems_end_loc h1_0 h1_1));
  (**) assert(B.(modifies spine_end_loc h1_1 h1_2));
  (**) assert(match G.reveal llv with | x0::x1::_ -> True | _ -> False);
  (**) let Cons x0 (Cons x1 llv_end) = G.reveal llv in
  (**) assert(G.reveal fspec (dt_v h0 x0));
  (**) assert(not (G.reveal fspec (dt_v h0 x1)));
  (**) assert(filtered == x0 :: llv_end);
  (**) assert(LL1.well_formed h1_0 llt filtered);
  (**) assert(LL1.well_formed h1_2 llt filtered);
  (**) assert(filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h1_2);
  (**) assert(filter_one_find_loop_magic_wand l_all l_mod lltp00 lltp llvp f h00 h0 h1);
  (**) assert(filter_one_find_loop_magic_wand_pre l_all l_mod lltp llvp f h0);

  (**) elems_pairwise_disjoint_implies_disjoint_from_footprint x1 llv_end;
  (**) assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp llvp f h0 h1);

  (**) assert(filter_one_find_loop_magic_wand_post l_all l_mod lltp00 llvp f h00 h1);
  // What we get from the magic wand
  (**) let llt_whole0 = B.deref h00 lltp00 in
  (**) let llv_whole0 = B.deref h00 llvp in
  (**) let llt_whole1 = B.deref h1 lltp00 in
  (**) assert(elements_list_invariant h1 llt_whole1 filtered_whole);
  (**) assert(B.live h1 llt_whole1);
  (**) assert(B.loc_includes (LL1.footprint h00 llt_whole0 llv_whole0) (LL1.footprint h1 llt_whole1 filtered_whole));
  (**) assert(B.loc_includes (elems_footprint llv_whole0) (elems_footprint filtered_whole));
  (**) assert(gsame_elementsp filtered_whole h00 h1)
  end;

  (**) B.upd ll.elems 0ul (gfilter_one_element fspec h00 (get_elems h00 ll));
  (**) let h1 = get () in
  begin
  // The postcondition
  (**) let filtered_whole' = gfilter_one_element fspec h0 (get_elems h0 ll) in
  (**) let filtered_whole = gfilter_one_element fspec h00 (get_elems h00 ll) in
  (**) assert(filtered_whole' == filtered_whole);
  (**) assert(B.(modifies (region_of ll) h0 h1));
  (**) assert(get_elems h1 ll == filtered_whole);
  (**) assert(gsame_elementsp filtered_whole h00 h1);
  (**) filter_one_get_elems_lem fspec h00 h1 ll;
  (**) assert(v h1 ll == M.filter_one fspec (v h00 ll));

  (**) assert(invariant h1 ll)
  end
#pop-options

#push-options "--fuel 1 --ifuel 1"
let filter_one_loop_valid_head_filter
  #dt l_all l_mod ll lltp00 lltp llvp #inv #inv_lem #fspec f h00 =
  (**) let h0 = get () in
  let llt = !* lltp in
  let llv = !* llvp in
  let c0 = (!* llt) in

  if B.is_null c0.LL1.next then
    filter_one_loop_valid_head_filter_no_element
      #dt l_all l_mod ll lltp00 lltp llvp llt llv c0 #inv #inv_lem #fspec f h00
  else
    filter_one_loop_valid_head_filter_one_element
      #dt l_all l_mod ll lltp00 lltp llvp llt llv c0 #inv #inv_lem #fspec f h00
#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
let filter_one_loop_valid_head #dt ll #inv #inv_lem #fspec f =
  (**) let h0 = get () in
  [@inline_let]
  let lltp0 = ll.ptr in
  let llt: LL1.t (dt_s dt) = !* ll.ptr in
  let llv = !* ll.elems in
  (**) let h1 = get () in
  (**) assert(invariant #dt h1 ll);
  push_frame ();
  let lltp: B.buffer (LL1.t (dt_s dt)) = B.alloca llt 1ul in
  let llvp = B.alloca llv 1ul in
  (**) let h2 = get () in
  ST.recall_region ll.r;
  (**) let tp_loc = Ghost.hide B.(loc_buffer lltp) in
  (**) let vp_loc = Ghost.hide B.(loc_buffer llvp) in
  (**) let l_mod = Ghost.hide B.(loc_union tp_loc vp_loc) in
  (**) let ll_loc = Ghost.hide (elements_list_footprint #dt h0 llt llv) in
  (**) let l_all = Ghost.hide (region_of #dt ll) in
  (**) assert(B.(loc_disjoint (loc_all_regions_from false ll.r) tp_loc));
  (**) assert(B.(loc_disjoint (loc_all_regions_from false ll.r) vp_loc));
  [@inline_let]
  let inv' : HS.mem -> Ghost.erased Type0 =
    fun h ->
    B.(modifies loc_none h1 h) /\
    B.live h lltp /\
    B.live h llvp /\
    B.(fresh_loc (loc_addr_of_buffer lltp)) h1 h /\
    B.(fresh_loc (loc_addr_of_buffer llvp)) h1 h /\
    B.(loc_includes (loc_region_only true (HS.get_tip h)) l_mod) /\
    inv h
  in
  [@inline_let]
  let inv_lem' : ll1_pred_inv_lem #dt l_mod inv' =
    fun h0' l h1' ->
    (**) B.(modifies_only_not_unused_in loc_none h1 h1');
    (**) assert(B.(modifies loc_none h1 h1'));
    (**) inv_lem h1 h1';
    (**) assert(B.(fresh_loc (loc_addr_of_buffer lltp)) h1 h1');
    (**) assert(B.(fresh_loc (loc_addr_of_buffer llvp)) h1 h1');
    (**) assert(B.(loc_includes (loc_region_only true (HS.get_tip h1')) l_mod))
  in
  [@inline_let]
  let f' : ll1_pred_st l_all l_mod inv' inv_lem' fspec =
    fun x -> f x
  in
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);
  (**) elements_list_frame_invariant #dt llt llv B.loc_none h1 h2;
  (**) assert(elements_list_invariant #dt h2 llt llv);
  (**) inv_lem h1 h2;
  filter_one_find_loop #dt l_all l_mod lltp0 lltp llvp #inv' #inv_lem' #fspec f';
  (**) let h3 = get () in
  (**) assert(B.modifies l_mod h2 h3);

  filter_one_loop_valid_head_filter #dt l_all l_mod ll lltp0 lltp llvp f' h2;
  (**) let h5 = get () in
  begin
  (**) assert(B.modifies (region_of ll) h3 h5);
  (**) let filtered = gfilter_one_element fspec h0 (get_elems h0 ll) in
  (**) B.(modifies_only_not_unused_in loc_none h0 h3);
  (**) gfilter_one_element_invariants_lem (get_elems h0 ll) fspec h0;
  (**) assert(elems_invariants h0 filtered);
  (**) gsame_elementsp_refl filtered h0;
  (**) assert(gsame_elementsp filtered h0 h3) // TODO: useful?
  end;
  pop_frame ();
  (**) let h6 = get () in
  begin
  (**) let r_stack = FStar.Monotonic.HyperStack.get_tip h2 in
  (**) assert(B.modifies (region_of ll) h3 h5);
  (**) assert(B.modifies (B.loc_region_only false r_stack) h5 h6);
  (**) B.(modifies_only_not_unused_in (region_of ll) h0 h6);
  (**) inv_lem h0 h6;
  (**) let filtered = gfilter_one_element fspec h0 (get_elems h0 ll) in
  (**) assert(B.modifies (region_of ll) h0 h6);
  (**) assert(invariant h6 ll);
  (**) assert(get_elems h6 ll == filtered);
  (**) assert(gsame_elementsp filtered h5 h6);
  (**) gsame_elementsp_trans filtered h0 h5 h6;
  (**) assert(gsame_elementsp filtered h0 h6);
  (**) assert(v h6 ll == M.filter_one fspec (v h0 ll))
  end
#pop-options

inline_for_extraction noextract
val filter_one_loop : filter_one_st

#push-options "--ifuel 2 --fuel 2"
let filter_one_loop #dt ll #inv #inv_lem #fspec f =
  let llt = !* ll.ptr in
  if B.is_null llt then ()
  else
    begin
    let c0 = !* llt in
    [@inline_let] let x0 = c0.LL1.data in
    if f x0 then 
      filter_one_loop_valid_head ll f
    else
      pop ll
    end
#pop-options

let filter_one = filter_one_loop

/// Clearing (resetting)
/// --------------------

#push-options "--fuel 1"
let clear #dt ll =
  let v = !* ll.elems in
  LL1.free #_ #v ll.ptr; // [LL1.free] nullifies the pointer
  ll.elems *= G.hide []
#pop-options


/// Freeing the resource
/// --------------------

let free #dt ll =
  let elems = !* ll.elems in
  LL1.free #_ #elems ll.ptr;
  B.free ll.ptr;
  B.free ll.elems;
  B.free ll.r_new
