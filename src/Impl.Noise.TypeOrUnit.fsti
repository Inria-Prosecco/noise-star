module Impl.Noise.TypeOrUnit

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
open Impl.Noise.Types
open Spec.Noise

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// TODO: move and use more, especially in the API
let buffer_or_null_loc_addr (#a:Type0) (b:buffer a) : GTot B.loc =
  if B.g_is_null b then B.loc_buffer b // For some reason, we need to return loc_buffer b (and not loc_none)
  else B.loc_addr_of_buffer b

let buffer_or_null_freeable (#a:Type0) (b:buffer a) : GTot Type0 =
  if B.g_is_null b then True else B.freeable b

inline_for_extraction noextract
val lbuffer_malloc_also_empty (#a : Type0) (#len : size_t)
                              (r : HS.rid) (init : a) :
  ST (lbuffer a len)
  (requires (fun h0 ->
    ST.is_eternal_region r))
  (ensures (fun h0 o h1 ->
    let o : buffer a = o in
    B.(modifies loc_none h0 h1) /\
    B.live h1 o /\
    B.as_seq h1 o == Seq.create (size_v len) init /\
    B.fresh_loc (B.loc_buffer o) h0 h1 /\
    begin
    size_v len > 0 ==>
    (B.(loc_includes (loc_region_only true r) (B.loc_addr_of_buffer o)) /\
     B.freeable o)
    end /\
    B.(loc_includes (loc_region_only true r) (B.loc_buffer o)) /\
    (size_v len = 0 ==> B.g_is_null o)))

/// Malloc then copy in the allocated buffer
inline_for_extraction noextract
val lbuffer_malloc_copy (#a : Type0) (#len : size_t{size_v len > 0})
                        (r : HS.rid) (init : a)
                        (i : lbuffer a len) :
  ST (lbuffer a len)
  (requires (fun h0 ->
    live h0 i /\
    ST.is_eternal_region r))
  (ensures (fun h0 o h1 ->
    let i : buffer a = i in
    let o : buffer a = o in
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (B.loc_buffer o) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (B.loc_addr_of_buffer o)) /\
    B.freeable o /\
    B.live h1 o /\
    B.as_seq h1 o == B.as_seq h0 i))

/// Test if len > 0, then malloc and copy (otherwise, return null)
inline_for_extraction noextract
val lbuffer_malloc_copy_also_empty (#a : Type0) (#len : size_t)
                                   (r : HS.rid) (init : a)
                                   (i : lbuffer a len) :
  ST (lbuffer a len)
  (requires (fun h0 ->
    live h0 i /\
    ST.is_eternal_region r))
  (ensures (fun h0 o h1 ->
    let i : buffer a = i in
    let o : buffer a = o in
    B.(modifies loc_none h0 h1) /\
    B.live h1 o /\
    B.as_seq h1 o == B.as_seq h0 i /\
    B.fresh_loc (B.loc_buffer o) h0 h1 /\
    begin
    size_v len > 0 ==>
    (B.(loc_includes (loc_region_only true r) (B.loc_addr_of_buffer o)) /\
     B.freeable o)
    end /\
    B.(loc_includes (loc_region_only true r) (B.loc_buffer o)) /\
    (size_v len = 0 ==> B.g_is_null o)))

inline_for_extraction noextract
let type_or_unit (ty : Type0) (b : bool) : Type0 =
  if b then ty else unit

// Note: we don't use this type in the below signatures because sometimes there are unification problems
// TODO: investigate
inline_for_extraction noextract
type lbuffer_or_unit (a : Type0) (len : size_t) (b : bool) = type_or_unit (lbuffer a len) b

inline_for_extraction noextract
let lbuffer_or_unit_to_buffer (#a : Type0) (#len : size_t) (#b : bool)
                              (buf : type_or_unit (lbuffer a len) b) : buffer a =
  if b then buf else B.null
inline_for_extraction noextract
let lbuffer_or_unit_to_lbuffer_or_null (#a : Type0) (#len : size_t) (#b : bool)
                                       (buf : type_or_unit (lbuffer a len) b) : buffer a =
  if b then buf else B.null
inline_for_extraction noextract
let lbuffer_or_unit_to_seq (#a : Type0) (#len : size_t) (#b : bool)
                           (h : HS.mem) (buf : type_or_unit (lbuffer a len) b) :
  GTot (seq a) =
  if b then as_seq #MUT #a #len h buf else Seq.empty
inline_for_extraction noextract
let lbuffer_or_unit_to_opt_lseq (#a : Type0) (#len : size_t) (#b : bool)
                               (h : HS.mem) (buf : type_or_unit (lbuffer a len) b) :
  GTot (option (lseq a (size_v len))) =
  if b then Some (as_seq #MUT #a #len h buf) else None

// TODO: rename
inline_for_extraction noextract
let lbuffer_or_unit_to_loc (#a : Type0) (#len : size_t) (#b : bool)
                           (buf : type_or_unit (lbuffer a len) b) : GTot B.loc =
  if b then B.loc_addr_of_buffer (buf <: buffer a) else B.loc_none

inline_for_extraction noextract
let lbuffer_or_unit_loc (#a : Type0) (#len : size_t) (#b : bool)
                        (buf : type_or_unit (lbuffer a len) b) : GTot B.loc =
  if b then B.loc_buffer (buf <: buffer a) else B.loc_none

inline_for_extraction noextract
let lbuffer_or_unit_freeable (#a : Type0) (#len : size_t) (#b : bool)
                             (buf : type_or_unit (lbuffer a len) b) : GTot Type0 =
  if b then B.freeable (lbuffer_or_unit_to_buffer buf) else True
inline_for_extraction noextract
let lbuffer_or_unit_live (#a : Type0) (#len : size_t) (#b : bool)
                         (h : mem) (buf : type_or_unit (lbuffer a len) b) : GTot Type0 =
  if b then live h (lbuffer_or_unit_to_buffer buf) else True

val lbuffer_or_unit_frame_lem (#a : Type0) (#len : size_t) (#b : bool)
                              (l : B.loc) (h0 h1 : HS.mem) (buf : type_or_unit (lbuffer a len) b) :
  Lemma
  (requires (
    lbuffer_or_unit_live h0 buf /\
    B.loc_disjoint l (lbuffer_or_unit_to_loc buf) /\
    B.modifies l h0 h1))
  (ensures (
    lbuffer_or_unit_to_seq h1 buf == lbuffer_or_unit_to_seq h0 buf /\
    lbuffer_or_unit_to_opt_lseq h1 buf == lbuffer_or_unit_to_opt_lseq h0 buf))

inline_for_extraction noextract
val lbuffer_or_unit_alloca (#a : Type0) (#len : size_t{size_v len > 0}) (#b : bool)
                           (zero : a) :
  StackInline (type_or_unit (lbuffer a len) b)
  (requires (fun _ -> True))
  (ensures (fun h0 p h1 ->
     B.(modifies loc_none h0 h1) /\
     B.fresh_loc (lbuffer_or_unit_to_loc p) h0 h1 /\
     B.(loc_includes (loc_region_only true (HS.get_tip h1)) (lbuffer_or_unit_to_loc p)) /\
     B.live h1 (lbuffer_or_unit_to_buffer p)))

inline_for_extraction noextract
val lbuffer_or_unit_malloc (#a : Type0) (#len : size_t{size_v len > 0}) (#b : bool)
                           (r : HS.rid) (init : a) :
  ST (type_or_unit (lbuffer a len) b)
  (requires (fun _ ->
    ST.is_eternal_region r))
  (ensures (fun h0 p h1 ->
     B.(modifies loc_none h0 h1) /\
     B.fresh_loc (lbuffer_or_unit_to_loc p) h0 h1 /\
     B.(loc_includes (loc_region_only true r) (lbuffer_or_unit_to_loc p)) /\
     lbuffer_or_unit_freeable p /\
     B.live h1 (lbuffer_or_unit_to_buffer p)))

inline_for_extraction noextract
val lbuffer_or_unit_free (#a : Type0) (#len : size_t{size_v len > 0}) (#b : bool)
                         (buf : type_or_unit (lbuffer a len) b) :
  ST unit
  (requires (fun h0 ->
    B.live h0 (lbuffer_or_unit_to_buffer buf) /\
    lbuffer_or_unit_freeable buf))
  (ensures (fun h0 _ h1 ->
     B.modifies (lbuffer_or_unit_to_loc buf) h0 h1))

inline_for_extraction noextract
val lbuffer_or_unit_copy (#a : Type0) (#len : size_t{size_v len > 0}) (#b : bool)
                         (o i : type_or_unit (lbuffer a len) b) :
  Stack unit
  (requires (fun h0 ->
    B.live h0 (lbuffer_or_unit_to_buffer o) /\
    B.live h0 (lbuffer_or_unit_to_buffer i) /\
    disjoint (lbuffer_or_unit_to_buffer o) (lbuffer_or_unit_to_buffer i)))
  (ensures (fun h0 _ h1 ->
     let o_loc = if b then B.loc_buffer (o <: buffer a) else B.loc_none in
     B.modifies o_loc h0 h1 /\
     lbuffer_or_unit_to_seq h1 o == lbuffer_or_unit_to_seq h0 i /\
     B.live h1 (lbuffer_or_unit_to_buffer o)))

/// Malloc then copy in the allocated buffer
inline_for_extraction noextract
val lbuffer_or_unit_malloc_copy (#a : Type0) (#len : size_t{size_v len > 0}) (#b : bool)
                                (r : HS.rid) (init : a)
                                (i : type_or_unit (lbuffer a len) b) :
  ST (type_or_unit (lbuffer a len) b)
  (requires (fun h0 ->
    B.live h0 (lbuffer_or_unit_to_buffer i) /\
    ST.is_eternal_region r))
  (ensures (fun h0 o h1 ->
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (lbuffer_or_unit_to_loc o) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (lbuffer_or_unit_to_loc o)) /\
    lbuffer_or_unit_freeable o /\
    B.live h1 (lbuffer_or_unit_to_buffer o) /\
    lbuffer_or_unit_to_seq h1 o == lbuffer_or_unit_to_seq h0 i))

[@@ noextract_to "krml"] inline_for_extraction noextract
val sub_or_unit (#a : Type0)
                (b : bool)
                (input : buffer a)
                (i len : size_t) :
  Stack (lbuffer_or_unit a len b)
  (requires (fun h0 ->
    B.live h0 input /\
    (b ==> size_v i + size_v len <= length input)))
  (ensures (fun h0 out h1 ->
    h1 == h0 /\
    lbuffer_or_unit_live h1 out /\
    (b ==> out == B.gsub input i len)))

(*** Cryptographic types *)
inline_for_extraction noextract
type private_key_t_or_unit (nc : iconfig) (b : bool) : Type0 =
  type_or_unit (private_key_t nc) b
inline_for_extraction noextract
type public_key_t_or_unit (nc : iconfig) (b : bool) : Type0 =
  type_or_unit (public_key_t nc) b
inline_for_extraction noextract
type preshared_key_t_or_unit (b : bool) : Type0 =
  type_or_unit preshared_key_t b

let keys_t_or_unit_to_keypair (#nc : iconfig) (#b : bool)
                              (h : mem)
                              (priv : private_key_t_or_unit nc b)
                              (pub : public_key_t_or_unit nc b) :
  GTot (option (keypair (get_config nc))) =
  let priv_v = lbuffer_or_unit_to_opt_lseq h priv in
  let pub_v = lbuffer_or_unit_to_opt_lseq h pub in
  if b then Some (mk_keypair (Some?.v pub_v) (Some?.v priv_v)) else None

(*** Booleans *)

inline_for_extraction noextract
let bool_or_gbool (b : bool) : Type0 =
  if b then bool else Ghost.erased bool

inline_for_extraction noextract
let bool_or_gbool_to_gbool (#b : bool) (x : bool_or_gbool b) : Tot (Ghost.erased bool) =
  if b then Ghost.hide x else x

inline_for_extraction noextract
let bool_or_gbool_to_bool (#b : bool) (x : bool_or_gbool b) (dvalue : bool) : Tot bool =
  if b then x else dvalue

inline_for_extraction noextract
let bool_to_bool_or_gbool (#b : bool) (x : bool) : Tot (bool_or_gbool b) =
  if b then x else Ghost.hide x
