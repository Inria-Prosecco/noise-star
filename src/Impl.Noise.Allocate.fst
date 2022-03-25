/// We provide allocation helpers below, to help with the proofs.
/// Those helpers wrap the standard library helpers into functions
/// which have weaker signatures. In practice, those signatures are
/// what we need to implement Noise, and allow us to have proofs
/// which are a lot more lightweight.

module Impl.Noise.Allocate

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
module B = LowStar.Buffer

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(*** Utilities *)

[@@ noextract_to "Kremlin"] noextract unfold let region_to_loc = B.loc_all_regions_from false
[@@ noextract_to "Kremlin"] noextract unfold let disjoint_regions r1 r2 = B.loc_disjoint (region_to_loc r1) (region_to_loc r2)
[@@ noextract_to "Kremlin"] noextract unfold let region_includes r1 = B.loc_includes (region_to_loc r1)
[@@ noextract_to "Kremlin"] noextract unfold let region_includes_region r1 r2 = B.loc_includes (region_to_loc r1) (region_to_loc r2)
unfold let region_includes_buffer r (#a:Type0) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel) :
  GTot Type0 =
  if B.g_is_null b then region_includes r (B.loc_buffer b)
  else region_includes r (B.loc_addr_of_buffer b)


(*** Region allocation *)

/// Allocate several subregions at once. There are several flavours:
/// - either we allocate subregions directly in the region provided
///   by the user
/// - or we allocate a first subregion, then more subregions inside
///   this subregion. This allows to have a parent region <> root,
///   which is sometimes necessary to reason about disjointness
///   when there is a stack

let region_is_child (r_parent r_child : rid) : GTot Type0 =
  is_eternal_region r_child /\
  r_child <> root /\
  region_includes_region r_parent r_child

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_region : r0:rid ->
  ST rid
  (requires (fun _ -> is_eternal_region r0))
  (ensures (fun h0 r1 h1 ->
    B.modifies B.loc_none h0 h1 /\
    region_is_child r0 r1))

let create_region r0 =
  new_region r0

(**** First flavour *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions2 : r0:rid ->
  ST (rid & rid)
  (requires (fun _ -> is_eternal_region r0))
  (ensures (fun h0 res h1 ->
    let (r1, r2) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r0 r1 /\
    region_is_child r0 r2 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
    ]
    ))

let create_regions2 r0 =
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  (r1, r2)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions3 : r0:rid ->
  ST (rid & rid & rid)
  (requires (fun _ -> is_eternal_region r0))
  (ensures (fun h0 res h1 ->
    let (r1, r2, r3) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r0 r1 /\
    region_is_child r0 r2 /\
    region_is_child r0 r3 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
      region_to_loc r3;
    ]
    ))

let create_regions3 r0 =
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  let r3 = new_region r0 in
  (r1, r2, r3)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions4 : r0:rid ->
  ST (rid & rid & rid & rid)
  (requires (fun _ -> is_eternal_region r0))
  (ensures (fun h0 res h1 ->
    let (r1, r2, r3, r4) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r0 r1 /\
    region_is_child r0 r2 /\
    region_is_child r0 r3 /\
    region_is_child r0 r4 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
      region_to_loc r3;
      region_to_loc r4;
    ]
    ))

let create_regions4 r0 =
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  let r3 = new_region r0 in
  let r4 = new_region r0 in
  (r1, r2, r3, r4)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions5 : r0:rid ->
  ST (rid & rid & rid & rid & rid)
  (requires (fun _ -> is_eternal_region r0))
  (ensures (fun h0 res h1 ->
    let (r1, r2, r3, r4, r5) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r0 r1 /\
    region_is_child r0 r2 /\
    region_is_child r0 r3 /\
    region_is_child r0 r4 /\
    region_is_child r0 r5 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
      region_to_loc r3;
      region_to_loc r4;
      region_to_loc r5;
    ]
    ))

let create_regions5 r0 =
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  let r3 = new_region r0 in
  let r4 = new_region r0 in
  let r5 = new_region r0 in
  (r1, r2, r3, r4, r5)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions6 : r0:rid ->
  ST (rid & rid & rid & rid & rid & rid)
  (requires (fun _ -> is_eternal_region r0))
  (ensures (fun h0 res h1 ->
    let (r1, r2, r3, r4, r5, r6) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r0 r1 /\
    region_is_child r0 r2 /\
    region_is_child r0 r3 /\
    region_is_child r0 r4 /\
    region_is_child r0 r5 /\
    region_is_child r0 r6 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
      region_to_loc r3;
      region_to_loc r4;
      region_to_loc r5;
      region_to_loc r6;
    ]
    ))

let create_regions6 r0 =
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  let r3 = new_region r0 in
  let r4 = new_region r0 in
  let r5 = new_region r0 in
  let r6 = new_region r0 in
  (r1, r2, r3, r4, r5, r6)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions10 : r0:rid ->
  ST (rid & rid & rid & rid & rid & rid & rid & rid & rid & rid)
  (requires (fun _ -> is_eternal_region r0))
  (ensures (fun h0 res h1 ->
    let (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r0 r1 /\
    region_is_child r0 r2 /\
    region_is_child r0 r3 /\
    region_is_child r0 r4 /\
    region_is_child r0 r5 /\
    region_is_child r0 r6 /\
    region_is_child r0 r7 /\
    region_is_child r0 r8 /\
    region_is_child r0 r9 /\
    region_is_child r0 r10 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
      region_to_loc r3;
      region_to_loc r4;
      region_to_loc r5;
      region_to_loc r6;
      region_to_loc r7;
      region_to_loc r8;
      region_to_loc r9;
      region_to_loc r10;
    ]
    ))

let create_regions10 r0 =
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  let r3 = new_region r0 in
  let r4 = new_region r0 in
  let r5 = new_region r0 in
  let r6 = new_region r0 in
  let r7 = new_region r0 in
  let r8 = new_region r0 in
  let r9 = new_region r0 in
  let r10 = new_region r0 in
  (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions12 : r0:rid ->
  ST (rid & rid & rid & rid & rid & rid & rid & rid & rid & rid & rid & rid)
  (requires (fun _ -> is_eternal_region r0))
  (ensures (fun h0 res h1 ->
    let (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r0 r1 /\
    region_is_child r0 r2 /\
    region_is_child r0 r3 /\
    region_is_child r0 r4 /\
    region_is_child r0 r5 /\
    region_is_child r0 r6 /\
    region_is_child r0 r7 /\
    region_is_child r0 r8 /\
    region_is_child r0 r9 /\
    region_is_child r0 r10 /\
    region_is_child r0 r11 /\
    region_is_child r0 r12 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
      region_to_loc r3;
      region_to_loc r4;
      region_to_loc r5;
      region_to_loc r6;
      region_to_loc r7;
      region_to_loc r8;
      region_to_loc r9;
      region_to_loc r10;
      region_to_loc r11;
      region_to_loc r12;
    ]
    ))

let create_regions12 r0 =
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  let r3 = new_region r0 in
  let r4 = new_region r0 in
  let r5 = new_region r0 in
  let r6 = new_region r0 in
  let r7 = new_region r0 in
  let r8 = new_region r0 in
  let r9 = new_region r0 in
  let r10 = new_region r0 in
  let r11 = new_region r0 in
  let r12 = new_region r0 in
  (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12)

(**** Second flavour *)

let region_is_grandchild (r_parent r_child r_grandchild : rid) : GTot Type0 =
  region_is_child r_parent r_grandchild /\
  region_is_child r_child r_grandchild

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions_non_root_2 : r00:rid ->
  ST (rid & rid & rid)
  (requires (fun _ -> is_eternal_region r00))
  (ensures (fun h0 res h1 ->
    let (r0, r1, r2) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r00 r0 /\
    region_is_grandchild r00 r0 r1 /\
    region_is_grandchild r00 r0 r2 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
    ]
    ))

let create_regions_non_root_2 r00 =
  let r0 = new_region r00 in
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  (r0, r1, r2)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions_non_root_3 : r00:rid ->
  ST (rid & rid & rid & rid)
  (requires (fun _ -> is_eternal_region r00))
  (ensures (fun h0 res h1 ->
    let (r0, r1, r2, r3) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r00 r0 /\
    region_is_grandchild r00 r0 r1 /\
    region_is_grandchild r00 r0 r2 /\
    region_is_grandchild r00 r0 r3 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
      region_to_loc r3
    ]
    ))

let create_regions_non_root_3 r00 =
  let r0 = new_region r00 in
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  let r3 = new_region r0 in
  (r0, r1, r2, r3)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val create_regions_non_root_4 : r00:rid ->
  ST (rid & rid & rid & rid & rid)
  (requires (fun _ -> is_eternal_region r00))
  (ensures (fun h0 res h1 ->
    let (r0, r1, r2, r3, r4) = res in
    B.modifies B.loc_none h0 h1 /\
    region_is_child r00 r0 /\
    region_is_grandchild r00 r0 r1 /\
    region_is_grandchild r00 r0 r2 /\
    region_is_grandchild r00 r0 r3 /\
    region_is_grandchild r00 r0 r4 /\
    B.all_disjoint [
      region_to_loc r1;
      region_to_loc r2;
      region_to_loc r3;
      region_to_loc r4
    ]
    ))

let create_regions_non_root_4 r00 =
  let r0 = new_region r00 in
  let r1 = new_region r0 in
  let r2 = new_region r0 in
  let r3 = new_region r0 in
  let r4 = new_region r0 in
  (r0, r1, r2, r3, r4)

(*** Allocation *)

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val malloc_gen :
  #a:Type0 -> r: rid -> l:B.loc -> init: a -> len: UInt32.t ->
  ST (b:B.buffer a{B.length b == UInt32.v len /\ not (B.g_is_null b)})
  (requires (fun h0 ->
    is_eternal_region r /\
    B.loc_in l h0 /\
    UInt32.v len > 0))
  (ensures (fun h0 b h1 ->
    B.live h1 b /\ B.modifies B.loc_none h0 h1 /\ B.freeable b /\
    B.loc_in (B.loc_addr_of_buffer b) h1 /\
    region_includes r (B.loc_addr_of_buffer b) /\
    B.loc_disjoint l (B.loc_addr_of_buffer b) /\
    B.as_seq h1 b == Seq.Base.create (UInt32.v len) init))

let malloc_gen #a r l init len =
  B.malloc r init len

[@@ noextract_to "Kremlin"] inline_for_extraction noextract
val malloc1 :
  #a:Type0 -> r: rid -> init: a -> len: UInt32.t ->
  ST (b:B.buffer a{B.length b == UInt32.v len /\ not (B.g_is_null b)})
  (requires (fun h0 ->
    is_eternal_region r /\
    UInt32.v len > 0))
  (ensures (fun h0 b h1 ->
    B.live h1 b /\ B.modifies B.loc_none h0 h1 /\ B.freeable b /\
    region_includes r (B.loc_addr_of_buffer b) /\
    B.as_seq h1 b == Seq.Base.create (UInt32.v len) init))

let malloc1 #a r init len =
  B.malloc r init len
