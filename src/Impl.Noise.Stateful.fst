module Impl.Noise.Stateful
// TODO: move to HACL, F* or Kremlin

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

open Lib.Sequence
module S = Lib.Sequence
module L = FStar.List
module Seq = FStar.Seq
open Lib.ByteSequence

open Lib.Buffer
open LowStar.BufferOps

module LB = Lib.Buffer
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module G = FStar.Ghost
module U8 = FStar.UInt8

// For buffer_or_null_loc_addr, buffer_or_null_loc_freeable.
// TODO: move them to another files
open Impl.Noise.TypeOrUnit

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"

(*** Primitive typeclass *)
/// Stateful typeclass: the base typeclass, containing all the primitive operations
/// and predicates.
/// Note that the [footprint] is indenpendant of the memory snapshot.
/// It is the case when there are no memory indirections (if the type is actually
/// a record of buffers, for example). In other situations (a linked list for
/// example), this can be achieved by putting all the stateful data inside a region.
/// Note that making the footprint independant of the memory really makes reasoning
/// a lot easier.
/// Note that the [invariant] and the [freeable] predicate MAY NEED the memory
/// snapshot.
inline_for_extraction noeq
type stateful (index: Type0) =
| Stateful:
  // Low-level types
  s: (index -> Type0) ->

  // Abstract footprint.
  footprint: (#i:index -> s:s i -> GTot B.loc) ->
  freeable: (#i:index -> h:HS.mem -> p:s i -> Type) ->
  invariant: (#i:index -> h:HS.mem -> s:s i -> Type) ->

  // A pure representation of a s
  t: (index -> Type0) ->
  v: (i:index -> h:HS.mem -> s:s i -> GTot (t i)) ->

  // Adequate framing lemmas, relying on v.

  frame_invariant: (#i:index -> l:B.loc -> s:s i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      B.loc_disjoint l (footprint #i s) /\
      B.modifies l h0 h1))
    (ensures (
      invariant h1 s /\
      v i h0 s == v i h1 s))
    [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]) ->

  frame_freeable: (#i:index -> l:B.loc -> s:s i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      freeable h0 s /\
      B.loc_disjoint l (footprint #i s) /\
      B.modifies l h0 h1))
    (ensures (
      freeable h1 s))
    [ SMTPat (freeable h1 s); SMTPat (B.modifies l h0 h1) ]) ->

  stateful index

/// An instantiation of [stateful] as buffers of fixed length.
// This is a copy-paste from Hacl.Streaming.Interface
inline_for_extraction noextract
let stateful_buffer (a:Type0) (l: UInt32.t { UInt32.v l > 0 }) (zero: a) :
  stateful unit =
  Stateful
    (fun _ -> b:B.buffer a { B.len b == l })
    (fun #_ s -> B.loc_addr_of_buffer s)
    (fun #_ h s -> B.freeable s)
    (fun #_ h s -> B.live h s)
    (fun _ -> s:S.seq a { S.length s == UInt32.v l })
    (fun _ h s -> B.as_seq h s)
    (fun #_ l s h0 h1 -> ())
    (fun #_ l s h0 h1 -> ())

/// An instantiation of [stateful] as [unit]
// This is a copy paste from Hacl.streaming.Interface
inline_for_extraction noextract
let stateful_unused (t: Type0): stateful t =
  Stateful
    (fun _ -> unit)
    (fun #_ s -> B.loc_none)
    (fun #_ h s -> True)
    (fun #_ h s -> True)
    (fun _ -> unit)
    (fun _ h s -> ())
    (fun #_ l s h0 h1 -> ())
    (fun #_ l s h0 h1 -> ())

inline_for_extraction noextract
let stateful_input_unused (index: Type0) (s : Type0) (init : s) : stateful index =
  Stateful
    (fun _ -> unit)
    (fun #_ s -> B.loc_none)
    (fun #_ h s -> True)
    (fun #_ h s -> True)
    (fun _ -> s)
    (fun _ h s -> init)
    (fun #_ l s h0 h1 -> ())
    (fun #_ l s h0 h1 -> ())

inline_for_extraction noextract
type alloca_st (#index : Type0) (st : stateful index) =
  i:index -> StackInline (st.s i)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    st.invariant #i h1 s /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (st.footprint #i s) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (st.footprint #i s))))

inline_for_extraction noextract
type malloc_st (#index : Type0) (st : stateful index) =
  i:index ->
  r:HS.rid ->
  ST (st.s i)
  (requires (fun h0 ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    // Note that there is no freshness: the Noise policy is that if we
    // allocate on the heap, then the allocated data has its own region,
    // which can't be used for anythng else. Here, r will only be used
    // for the returned data.
    st.invariant #i h1 s /\
    B.(modifies loc_none h0 h1) /\
    B.(loc_includes (loc_all_regions_from false r) (st.footprint #i s)) /\
    st.freeable #i h1 s))

inline_for_extraction noextract
type clone_st (#index : Type0) (st : stateful index) =
  #i:index ->
  r:HS.rid ->
  x:st.s i ->
  ST (st.s i)
  (requires (fun h0 ->
    HyperStack.ST.is_eternal_region r /\
    st.invariant h0 x))
  (ensures (fun h0 p h1 ->
    st.invariant #i h1 p /\
    B.(modifies loc_none h0 h1) /\
    B.(loc_includes (loc_all_regions_from false r) (st.footprint #i p)) /\
    st.freeable h1 p /\
    st.v i h1 p == st.v i h0 x))

// The copy function was initially stack, but we decided to make it ST because
// in practice, in Noise, we mostly manipulate heap allocated data of variable
// size. Note this is a choice of design different from the Hacl streaming
// functor.
inline_for_extraction noextract
type copy_st (#index : Type0) (st : stateful index) =
  i:G.erased index -> (
  let i = G.reveal i in
  s_dst:st.s i ->
  s_src:st.s i ->
  ST unit
  (requires (fun h0 ->
    st.invariant #i h0 s_src /\
    st.invariant #i h0 s_dst /\
    B.(loc_disjoint (st.footprint #i s_src) (st.footprint #i s_dst))))
  (ensures fun h0 _ h1 ->
    B.(modifies (st.footprint #i s_dst) h0 h1) /\
    (st.freeable #i h0 s_dst ==> st.freeable #i h1 s_dst) /\
    st.invariant #i h1 s_dst /\
    st.v i h1 s_dst == st.v i h0 s_src))

// Note that this function may have to take care of erasing sensitive information
inline_for_extraction noextract
type free_st (#index : Type0) (st : stateful index) =
  i: G.erased index -> (
  let i = G.reveal i in
  s:st.s i ->
  ST unit
  (requires fun h0 ->
    st.invariant #i h0 s /\
    st.freeable h0 s)
  (ensures fun h0 _ h1 ->
    B.(modifies (st.footprint #i s)) h0 h1))

inline_for_extraction noextract
type malloc_from_input_st
  (#index : Type0)
  (st_in : stateful index)
  (st_out : stateful index{forall i. st_out.t i == st_in.t i}) =
  i:index ->
  r:HS.rid ->
  input:st_in.s i ->
  ST (st_out.s i)
  (requires (fun h0 ->
    HyperStack.ST.is_eternal_region r /\
    st_in.invariant h0 input))
  (ensures (fun h0 s h1 ->
    st_out.invariant #i h1 s /\
    st_out.v i h1 s == st_in.v i h0 input /\
    B.(modifies loc_none h0 h1) /\
    B.(loc_includes (loc_all_regions_from false r) (st_out.footprint #i s)) /\
    st_out.freeable #i h1 s))

inline_for_extraction noextract
type alloca_from_input_st
  (#index : Type0)
  (st_in : stateful index)
  (st_out : stateful index{forall i. st_out.t i == st_in.t i}) =
  i:index ->
  r:HS.rid ->
  input:st_in.s i ->
  ST (st_out.s i)
  (requires (fun h0 ->
    st_in.invariant h0 input))
  (ensures (fun h0 s h1 ->
    st_out.invariant #i h1 s /\
    st_out.v i h1 s == st_in.v i h0 input /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (st_out.footprint #i s) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (st_out.footprint #i s))))

// We use a different, simpler type for the input data we give to malloc/alloca
// (see their signatures). It might be necessary to generate such an input from
// an already allocated element.
// TODO: I don't like this one. We mostly need it because of the peer information
// stored in the device/dstate. It would probably be better in the future to
// have a null/none value for the stateful class, and to replace this value,
// rather than to copy inside an already allocated stateful instance.
inline_for_extraction noextract
type input_from_output_st
  (#index : Type0)
  (st_in : stateful index)
  (st_out : stateful index{forall i. st_out.t i == st_in.t i}) =
  i:index ->
  x:st_out.s i ->
  ST (st_in.s i)
  (requires (fun h0 ->
    st_out.invariant h0 x))
  (ensures (fun h0 y h1 ->
    st_in.invariant #i h1 y /\
    st_in.v i h1 y == st_out.v i h0 x /\
    B.(modifies loc_none h0 h1) /\
    B.loc_includes (st_out.footprint #i x) (st_in.footprint #i y)))

// If a stateful is not freeable, it must be included in the current memory snapshot
inline_for_extraction noextract
type invariant_loc_in_footprint
  (#index : Type0)
  (st : stateful index) =
  #i:index ->
  h: mem ->
  s: st.s i ->
  Lemma
  (requires (st.invariant h s))
  (ensures (
    // We don't put ``freeable`` in the requires clause
    // so that we can always call [invariant_loc_in_footprint]
    ~(st.freeable h s) ==> B.loc_in (st.footprint s) h))

// The footprint is actually given by a region
inline_for_extraction noextract
type footprint_rid
  (#index : Type0)
  (st : stateful index) =
  #i:index ->
  s: st.s i ->
  Tot (r:rid{st.footprint s == B.loc_all_regions_from false r})

// If a stateful is freeable, recall the fact that it is disjoint from the stack
inline_for_extraction noextract
type recall_footprint
  (#index : Type0)
  (st : stateful index)
  (footprint_rid : footprint_rid st) =
  #i:index ->
  s: st.s i ->
  Stack unit
  (requires (fun h0 ->
    is_stack_region (get_tip h0) /\
    st.invariant h0 s))
  (ensures (fun h0 _ h1 ->
    h0 == h1 /\
    // We don't put ``freeable`` in the requires clause
    // so that we can always call [recall_footprint]
    (st.freeable h0 s ==>
     (footprint_rid s `is_in` get_hmap h1 /\
      Monotonic.HyperHeap.disjoint (get_tip h1) (footprint_rid s)))))

// Recall the fact that it is disjoint from the stack
inline_for_extraction noextract
type recall_footprint_always
  (#index : Type0)
  (st : stateful index)
  (footprint_rid : footprint_rid st) =
  #i:index ->
  s: st.s i ->
  Stack unit
  (requires (fun h0 ->
    is_stack_region (get_tip h0) /\
    st.invariant h0 s))
  (ensures (fun h0 _ h1 ->
    h0 == h1 /\
    footprint_rid s `is_in` get_hmap h1 /\
    Monotonic.HyperHeap.disjoint (get_tip h1) (footprint_rid s)))

/// ===================
/// The below functions are used to convert stateful data to (and from) raw
/// bytes. They are used for serialization/deserialization.
/// They come in pairs: high-level specification function, low level implementation.
/// We use secret bytes rather than sequences of uint8 because it makes it
/// easier to interop with the rest of Hacl*. In particular, it allows us to
/// use the generated bytes with the crypto functions (for hashing, as
/// authentication data, etc.)

inline_for_extraction noextract
type to_bytes_seq_t (#index : Type0) (st : stateful index) =
  #i:index ->
  x:st.t i ->
  Tot (b:bytes{Seq.length b <= pow2 31}) // So that we can use it as an aead

inline_for_extraction noextract
type input_to_bytes_seq_t
  (#index : Type0)
  (st_in : stateful index)
  (#st_out : stateful index)
  (out_to_bytes : to_bytes_seq_t st_out{forall i. st_out.t i == st_in.t i}) =
  #i:index ->
  x:st_in.t i ->
  Tot (b:bytes{b == out_to_bytes #i x})

inline_for_extraction noextract
type to_bytes_st (#index : Type0) (#st : stateful index) (to_bs : to_bytes_seq_t st) =
  #i:index ->
  r:HS.rid ->
  out:B.pointer (B.buffer uint8) ->
  outlen:B.pointer size_t ->
  x:st.s i ->
  ST unit
  (requires (fun h0 ->
    HyperStack.ST.is_eternal_region r /\
    B.live h0 out /\ B.live h0 outlen /\
    st.invariant h0 x /\
    begin
    let lr = B.loc_all_regions_from false r in
    let l1 = B.loc_addr_of_buffer out in
    let l2 = B.loc_addr_of_buffer (B.deref h0 out) in
    let l3 = B.loc_addr_of_buffer out in
    let lx = st.footprint x in
    B.all_disjoint [lr; l1; l2; l3; lx]
    end))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_union (loc_buffer out) (loc_buffer outlen)) h0 h1) /\
    begin
    let out = B.deref h1 out in
    B.(loc_includes (loc_all_regions_from false r) (buffer_or_null_loc_addr out)) /\
    buffer_or_null_freeable out /\
    B.as_seq h1 out == to_bs (st.v i h0 x)
    end))

inline_for_extraction noextract
type from_bytes_seq_t (#index : Type0) (st : stateful index) =
  i:index ->
  s:bytes ->
  Tot (option (st.t i))

/// out should have been allocated with malloc.
/// In practice, this function will only be implementable if the stateful data has
/// a copy function.
inline_for_extraction noextract
type from_bytes_st (#index : Type0) (#st : stateful index) (from_bs : from_bytes_seq_t st) =
  #i:index ->
  out:st.s i ->
  inlen:size_t ->
  input:lbuffer uint8 inlen ->
  ST bool
  (requires (fun h0 ->
    live h0 input /\
    st.invariant h0 out /\
    begin
    let l1 = st.footprint out in
    let l2 = B.loc_addr_of_buffer (input <: buffer uint8) in
    B.all_disjoint [l1; l2]
    end))
  (ensures (fun h0 b h1 ->
    let opt_out_v = from_bs i (as_seq h0 input) in
    B.(modifies (st.footprint out) h0 h1) /\
    st.invariant h1 out /\
    begin match b with
    | true ->
      Some? opt_out_v /\
      st.v i h1 out == Some?.v opt_out_v
    | false -> None? opt_out_v
    end))

inline_for_extraction noextract
type from_to_bytes_seq_l
  (#index : Type0) (#st : stateful index)
  (from : from_bytes_seq_t st)
  (to : to_bytes_seq_t st) : Type0 =
  i:index ->
  x:st.t i ->
  Lemma (from i (to x) == Some x)
  [SMTPat (from i (to x))]

inline_for_extraction noextract
type to_from_bytes_seq_l
  (#index : Type0) (#st : stateful index)
  (from : from_bytes_seq_t st)
  (to : to_bytes_seq_t st) : Type0 =
  i:index ->
  s:Seq.seq uint8 ->
  Lemma (
    match from i s with
    | Some x -> to x == s
    | None -> True)

/// Convert to bytes by performing a cast (no allocation, no copy)
inline_for_extraction noextract
type cast_to_bytes_st (#index : Type0) (#st : stateful index) (to_bs : to_bytes_seq_t st) =
  #i:index ->
  x:st.s i ->
  Stack (size_t & B.buffer uint8)
  (requires (fun h0 ->
    st.invariant h0 x))
  (ensures (fun h0 (outlen, out) h1 ->    
    B.(modifies loc_none h0 h1) /\
    B.live h1 out /\
    B.(loc_includes (st.footprint x) (buffer_or_null_loc_addr out)) /\
    B.as_seq h1 out == to_bs (st.v i h0 x) /\
    B.length out == size_v outlen))

/// Check equality of stateful data
inline_for_extraction noextract
type is_eq_st (#index : Type0) (#st : stateful index) (from_bs : from_bytes_seq_t st) =
  #i:index ->
  x0:st.s i ->
  x1:st.s i ->
  ST bool
  (requires (fun h0 ->
    st.invariant h0 x0 /\ st.invariant h0 x1))
  (ensures (fun h0 b h1 ->
    let x0_v = st.v i h0 x0 in
    let x1_v = st.v i h0 x1 in
    B.(modifies loc_none h0 h1) /\
    (b <==> (x0_v == x1_v))))

(*** Derived typeclasses *)

inline_for_extraction noextract noeq
type stateful_clone (index : Type0) =
| Stateful_clone :
  sc_stateful: stateful index ->

  sc_clone: clone_st sc_stateful ->

  sc_free: free_st sc_stateful ->

  stateful_clone index

inline_for_extraction noeq
type stateful_malloc_from_input (index : Type0) =
| Stateful_malloc_from_input :
  smfi_input: stateful index ->

  smfi_stateful: stateful index{forall i. smfi_stateful.t i == smfi_input.t i} ->

  smfi_malloc: malloc_from_input_st smfi_input smfi_stateful ->

  smfi_free: free_st smfi_stateful ->

  stateful_malloc_from_input index

inline_for_extraction noeq
type stateful_clone_copy (index : Type0) =
| Stateful_clone_copy :

  scc_stateful: stateful index ->

  scc_malloc: malloc_st scc_stateful ->

  scc_clone: clone_st scc_stateful ->

  scc_free: free_st scc_stateful ->

  scc_copy: copy_st scc_stateful ->

  stateful_clone_copy index

// TODO: this is the type used in Noise for the peer names, and it has become
// super specific. Remove that or
// define it somewhere else (like the device implementation file - it is super ugly).
inline_for_extraction noeq
type stateful_malloc_from_input_clone_copy (index : Type0) =
| Stateful_malloc_from_input_clone_copy :

  smficc_input: stateful index ->

  smficc_stateful: stateful index{forall i. smficc_stateful.t i == smficc_input.t i} ->

  smficc_malloc: malloc_st smficc_stateful ->

  smficc_malloc_from_input: malloc_from_input_st smficc_input smficc_stateful ->

  smficc_clone: clone_st smficc_stateful ->

  smficc_free: free_st smficc_stateful ->

  smficc_copy: copy_st smficc_stateful ->

  smficc_input_from_output: input_from_output_st smficc_input smficc_stateful ->

  smficc_to_bytes_seq: to_bytes_seq_t smficc_stateful ->
  
  smficc_cast_to_bytes: cast_to_bytes_st smficc_to_bytes_seq ->

  smficc_input_to_bytes_seq: input_to_bytes_seq_t smficc_input smficc_to_bytes_seq ->

  smficc_cast_input_to_bytes: cast_to_bytes_st smficc_input_to_bytes_seq ->

  stateful_malloc_from_input_clone_copy index

inline_for_extraction noeq
type stateful_alloca_malloc_copy (index : Type0) =
| Stateful_alloca_malloc_copy :

  samc_stateful: stateful index ->
  
  samc_alloca: alloca_st samc_stateful ->

  samc_malloc: malloc_st samc_stateful ->

  samc_free: malloc_st samc_stateful ->

  samc_copy: copy_st samc_stateful ->

  stateful_alloca_malloc_copy index

(*** Helpers *)
val opt_frame_freeable (#index : Type0) (st : stateful index)
  (#i:index) (l:B.loc) (s:st.s i) (h0:HS.mem) (h1:HS.mem) :
  Lemma
  (requires (
    st.invariant h0 s /\
    B.loc_disjoint l (st.footprint #i s) /\
    B.modifies l h0 h1))
  (ensures (st.freeable h0 s ==> st.freeable h1 s))

let opt_frame_freeable #index st #i l s h0 h1 =
  let _ = st.frame_freeable #i in
  ()
