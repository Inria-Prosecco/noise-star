/// This module implements utilities to manipulate strings of characters.
module Impl.Noise.String

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

// We switch between char and uint8, so we need decidable equality on secret
// integers. Note that using secret integers instead of public integers allows
// us to use the byte buffers with the cryptographic primitives (as
// authentication data, input to hash, etc.). To use with care, of course.
open Lib.RawIntTypes
open Lib.IntTypes
module U8 = FStar.UInt8

open Lib.Sequence
module S = Lib.Sequence
module L = FStar.List.Tot
module Seq = FStar.Seq

open Lib.Buffer
module LB = Lib.Buffer
open LowStar.BufferOps

module B = LowStar.Buffer
module G = FStar.Ghost

module IB = LowStar.ImmutableBuffer
module CB = LowStar.ConstBuffer
module LMB = LowStar.Monotonic.Buffer

open Impl.Noise.Allocate
open Impl.Noise.Stateful
open Impl.Noise.TypeOrUnit

module String = FStar.String
module Literal = LowStar.Literal
module Char = FStar.Char

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"

(*** Null-terminated strings *)
(**** Base types, predicates, lemmas *)
/// Because the memory model used in Low* prevents us from casting buffers, and as
/// we need to use peer names as authentication data, we use uint8* for the string
/// type, and let the user perform the casts. We tried to do differently (by copying
/// the strings provided by the user to buffers of uint8 stored internally) but it
/// proved extremely tedious, because there are a lot of places where performing a
/// cast is natural, and we actually have to perform a copy that we throw away.

/// The low-level char type
[@@ noextract_to "Karamel"] inline_for_extraction noextract
type char_t = uint8

/// The high-level char type
[@@ noextract_to "Karamel"] inline_for_extraction noextract
type char = Char.char

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let null_char : char_t = u8 0

let char_v (c : char) = v (Char.u32_of_char c)
let to_char (x : nat{x <= 255}) : char =
  (**) assert_norm(255 < pow2 21);
  Char.char_of_u32 (FStar.UInt32.uint_to_t x)

// TODO: remove those?
let char_t_is_null (x : char_t) : bool =
  u8_to_UInt8 x = u8_to_UInt8 null_char

let char_t_is_not_null (x : char_t) : bool =
  u8_to_UInt8 x <> u8_to_UInt8 null_char

let uint8_to_char (x : uint8) : c:char{char_v c <= 255} = to_char (v x)
let char_to_uint8 (x : char{char_v x <= 255}) : uint8 = u8 (UInt32.v (Char.u32_of_char x))

val uint8_to_char_bij (x : uint8) :
  Lemma (char_to_uint8 (uint8_to_char x) == x)
  [SMTPat (char_to_uint8 (uint8_to_char x))]
let uint8_to_char_bij x = assert_norm(255 < pow2 21)

val char_to_uint8_bij (x : char{char_v x <= 255}) :
  Lemma (uint8_to_char (char_to_uint8 x) == x)
  [SMTPat (uint8_to_char (char_to_uint8 x))]
let char_to_uint8_bij x = assert_norm(255 < pow2 21)

val list_seq_index_lem (#a : Type0) (s : Seq.seq a) (i : nat{i < Seq.length s}) :
  Lemma
  (ensures (Seq.index s i == L.index (Seq.seq_to_list s) i))
  (decreases i)
  [SMTPatOr [[SMTPat (Seq.index s i); SMTPat (Seq.seq_to_list s)];
             [SMTPat (L.index (Seq.seq_to_list s) i)]]]

#push-options "--fuel 1 --ifuel 1"
let rec list_seq_index_lem #a s i =
  if i = 0 then ()
  else 
    begin
    Seq.lemma_seq_list_bij s;
    match Seq.seq_to_list s with
    | [] -> () // impossible
    | x :: l1 ->
      Seq.lemma_list_seq_bij l1;
      let s1 = Seq.seq_of_list l1 in
      list_seq_index_lem s1 (i-1)
    end
#pop-options

val seq_list_index_lem (#a : Type0) (l : list a) (i : nat{i < L.length l}) :
  Lemma (requires True)
  (ensures (L.index l i == Seq.index (Seq.seq_of_list l) i))
  (decreases i)
  [SMTPatOr [[SMTPat (L.index l i); SMTPat (Seq.seq_of_list l)];
             [SMTPat (Seq.index (Seq.seq_of_list l) i)]]]

#push-options "--fuel 1 --ifuel 1"
let rec seq_list_index_lem l i =
  if i = 0 then ()
  else 
    begin
    Seq.lemma_list_seq_bij l;
    match l with
    | [] -> () // impossible
    | x :: l1 ->
      seq_list_index_lem l1 (i-1)
    end
#pop-options

// Magical lemma to reason with sequences and lists
val list_seq_decompose_index_lem (s : Seq.seq char_t) :
  Lemma (requires (True)) //Seq.length s > 0))
  (ensures (
    let l = Seq.seq_to_list s in
    match l with
    | [] -> True
    | x :: l1 ->
      let s1 = Seq.seq_of_list l1 in
      Seq.length s > 0 /\
      Seq.length s1 == Seq.length s - 1 /\
      L.length l1 == L.length l - 1 /\
      (forall (i : nat). i < Seq.length s ==> Seq.index s i == L.index l i) /\
      (forall (i : nat). i < Seq.length s1 ==> Seq.index s1 i == L.index l1 i) /\
      (forall (i : nat). (i < Seq.length s /\ i > 0) ==> L.index l i == L.index l1 (i-1))
    | _ -> False))
  (decreases (Seq.length s))

#push-options "--fuel 1 --ifuel 1"
let rec list_seq_decompose_index_lem s =
  let l = Seq.seq_to_list s in
  Seq.lemma_seq_list_bij s;
  match l with
  | [] -> ()
  | x :: l1 ->
    Seq.lemma_list_seq_bij l1;
    let s1 = Seq.seq_of_list l1 in
    assert(forall (i : nat). i < Seq.length s ==> Seq.index s i == L.index l i);
    assert(forall (i : nat). i < Seq.length s1 ==> Seq.index s1 i == L.index l1 i);
    assert(forall (i : nat). (i < Seq.length s /\ i > 0) ==> L.index l i == L.index l1 (i-1));
    list_seq_decompose_index_lem s1
#pop-options

// Rk.: those override the LowStar.Literal.string_is_ascii and
// LowStar.Literal.ascii_string definitions.
// Note that they are actually equivalent: the LowStar version uses
// a computable function while here we express the same property with
// quantifiers.
let string_is_ascii (s : string) =
  forall (i : nat{i < String.length s}). Literal.is_ascii_char (String.index s i)

type ascii_string = s:string{string_is_ascii s}

val list_char_to_uint8 (l : list char) :
  Pure (list uint8)
  (requires (
    forall (i : nat{i < L.length l}). char_v (L.index l i) <= 255))
  (ensures (fun l' ->
    L.length l' = L.length l /\
    (forall (i : nat{i < L.length l'}). v (L.index l' i) == char_v (L.index l i))))

#push-options "--ifuel 1 --fuel 1"    
let rec list_char_to_uint8 l =
  match l with
  | [] -> []
  | x :: l1 ->
    (**) assert(char_v (L.index l 0) <= 255);
    (**) assert(forall (i:nat{i < L.length l1}). L.index l1 i == L.index l (i+1));
    let l2 = list_char_to_uint8 l1 in
    let l3 = char_to_uint8 x :: l2 in
    (**) assert(forall (i:nat{i < L.length l3 /\ i > 0}). L.index l3 i == L.index l2 (i-1));
    l3
#pop-options

val list_uint8_to_char (l : list uint8) :
  Pure (list char)
  (requires (True))
  (ensures (fun l' ->
    L.length l' = L.length l /\
    (forall (i : nat{i < L.length l'}). char_v (L.index l' i) == v (L.index l i))))

#push-options "--ifuel 1 --fuel 1"    
let rec list_uint8_to_char l =
  match l with
  | [] -> []
  | x :: l1 ->
    (**) assert_norm(255 <= pow2 21);
    (**) assert(forall (i:nat{i < L.length l1}). L.index l1 i == L.index l (i+1));
    let l2 = list_uint8_to_char l1 in
    (**) assert(forall (i:nat{i < L.length l2}). char_v (L.index l2 i) == v (L.index l1 i));
    let l3 = uint8_to_char x :: l2 in
    (**) assert(forall (i:nat{i < L.length l3 /\ i > 0}). L.index l3 i == L.index l2 (i-1));
    l3
#pop-options

val seq_char_to_uint8 (s : Seq.seq char) :
  Pure (Seq.seq uint8)
  (requires (forall (i:nat{i < Seq.length s}). char_v (Seq.index s i) <= 255))
  (ensures (fun s' ->
    Seq.length s' = Seq.length s /\
    (forall (i:nat{i < Seq.length s'}). char_v (Seq.index s i) == v (Seq.index s' i))))

let seq_char_to_uint8 s =
  let l1 = Seq.seq_to_list s in
  let l2 = list_char_to_uint8 l1 in
  let s3 = Seq.seq_of_list l2 in
  (**) assert(forall (i:nat{i < L.length l1}). L.index l1 i == Seq.index s i);
  (**) assert(forall (i:nat{i < L.length l2}). v (L.index l2 i) == char_v (L.index l1 i));
  (**) assert(forall (i:nat{i < Seq.length s3}). Seq.index s3 i == L.index l2 i);
  s3

val seq_uint8_to_char (s : Seq.seq uint8) :
  Pure (Seq.seq char)
  (requires True)
  (ensures (fun s' ->
    Seq.length s' = Seq.length s /\
    (forall (i:nat{i < Seq.length s'}). v (Seq.index s i) == char_v (Seq.index s' i))))

let seq_uint8_to_char s =
  let l1 = Seq.seq_to_list s in
  let l2 = list_uint8_to_char l1 in
  let s3 = Seq.seq_of_list l2 in
  (**) assert(forall (i:nat{i < L.length l1}). L.index l1 i == Seq.index s i);
  (**) assert(forall (i:nat{i < L.length l2}). char_v (L.index l2 i) == v (L.index l1 i));
  (**) assert(forall (i:nat{i < Seq.length s3}). Seq.index s3 i == L.index l2 i);
  s3

val seq_uint8_to_from_char_eq (s : Seq.seq uint8) :
  Lemma (seq_char_to_uint8 (seq_uint8_to_char s) == s)
  [SMTPat (seq_char_to_uint8 (seq_uint8_to_char s))]

let seq_uint8_to_from_char_eq s0 =
  let sf = seq_char_to_uint8 (seq_uint8_to_char s0) in
  assert(Seq.equal sf s0)

val seq_char_to_from_uint8_eq (s : Seq.seq char) :
  Lemma
  (requires (
    forall (i : nat{i < Seq.length s}). char_v (Seq.index s i) <= 255))
  (ensures (seq_uint8_to_char (seq_char_to_uint8 s) == s))
  [SMTPat (seq_uint8_to_char (seq_char_to_uint8 s))]

let seq_char_to_from_uint8_eq s0 =
  let sf = seq_uint8_to_char (seq_char_to_uint8 s0) in
  assert(Seq.equal sf s0)

// Sanity check
val list_of_string_length (s:string) :
  Lemma (L.length (String.list_of_string s) = String.length s)

let list_of_string_length s = ()

// This one is not trivial however
val string_of_list_length (l:list FStar.Char.char) :
  Lemma (String.length (String.string_of_list l) = L.length l)
  [SMTPat (String.length (String.string_of_list l))]

let string_of_list_length l = String.list_of_string_of_list l

val index_string_of_list (l:list String.char) (i : nat{i < L.length l}) :
  Lemma (String.index (String.string_of_list l) i == L.index l i)
  [SMTPatOr [[SMTPat (String.index (String.string_of_list l) i)];
             [SMTPat (String.string_of_list l); SMTPat (L.index l i)]]]

let index_string_of_list l i = String.index_string_of_list l i

val index_list_of_string (s:string) (i : nat{i < String.length s}) :
  Lemma (L.index (String.list_of_string s) i == String.index s i)
  [SMTPatOr [[SMTPat (L.index (String.list_of_string s) i)];
             [SMTPat (String.list_of_string s); SMTPat (String.index s i)]]]

let index_list_of_string s i = String.index_list_of_string s i

val seq_to_string (s : Seq.seq char) :
  Pure string (requires True)
  (ensures (fun s' ->
    String.length s' = Seq.length s /\
    (forall (i:nat{i < String.length s'}). String.index s' i == Seq.index s i)))

let seq_to_string s = String.string_of_list (Seq.seq_to_list s)

val string_to_seq (s : string) :
  Pure (Seq.seq char) (requires True)
  (ensures (fun s' ->
    Seq.length s' = String.length s /\
    (forall (i:nat{i < Seq.length s'}). Seq.index s' i == String.index s i)))

let string_to_seq s = Seq.seq_of_list (String.list_of_string s)

val seq_to_string_to_seq_eq (s : Seq.seq char) :
  Lemma (string_to_seq (seq_to_string s) == s)
  [SMTPat (string_to_seq (seq_to_string s))]

let seq_to_string_to_seq_eq s =
  assert(Seq.equal (string_to_seq (seq_to_string s)) s)

val string_to_seq_to_string_eq (s : ascii_string) :
  Lemma (seq_to_string (string_to_seq s) == s)
  [SMTPat (seq_to_string (string_to_seq s))]

let string_to_seq_to_string_eq s =
  let s' = seq_to_string (string_to_seq s) in
  assert(
    s' == String.string_of_list (Seq.seq_to_list (Seq.seq_of_list (String.list_of_string s))));
  Seq.lemma_list_seq_bij (String.list_of_string s);
  assert(Seq.seq_to_list (Seq.seq_of_list (String.list_of_string s)) == String.list_of_string s);
  assert(s' == String.string_of_list (String.list_of_string s));
  String.string_of_list_of_string s

val list_of_string_inj (s1 s2 : string) :
  Lemma (String.list_of_string s1 == String.list_of_string s2 <==> s1 == s2)

let list_of_string_inj s1 s2 =
  assert(
    String.list_of_string s1 == String.list_of_string s2 ==>
    String.string_of_list (String.list_of_string s1) ==
    String.string_of_list (String.list_of_string s2));
  String.string_of_list_of_string s1;
  String.string_of_list_of_string s2

val string_empty_lem (x : Prims.string) :
  Lemma (String.length x = 0 <==> x == "")
  [SMTPat (String.length x)]

#push-options "--ifuel 1 --fuel 1"
let string_empty_lem s =
  let l1 = String.list_of_string s in
  assert_norm(String.list_of_string "" == []);
  String.string_of_list_of_string s;
  assert_norm(String.length s = 0 <==> l1 == []);
  // We don't need to use injectivity of list_of_string (which is proven only
  // for this lemma) but there seems to be encoding problems, making the proof
  // fails.
  list_of_string_inj s ""
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let buffer_or_null_loc_addr (#ty : buftype) (#a:Type0) (b:buffer_t ty a) : GTot B.loc =
  if g_is_null b then loc b // For some reason, we need to return loc_buffer b (and not loc_none)
  else loc_addr_of_buffer b

let buffer_or_null_freeable (#ty : buftype) (#a:Type0) (b:buffer_t ty a) : GTot Type0 =
  if g_is_null b then True else freeable b

/// We need to redefine [as_seq], [index] and [upd] because the lib versions have
/// an implicit parameter for the length, which we don't use.

#push-options "--ifuel 1"
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let as_seq (#t:buftype) (#a:Type0) (h:mem) (b:buffer_t t a) :
  GTot (Seq.lseq a (length b)) =
  match t with
  | MUT -> B.as_seq h (b <: buffer a)
  | IMMUT -> IB.as_seq h (b <: ibuffer a)
  | CONST -> CB.as_seq h (b <: cbuffer a)
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val index:
     #ty:buftype
  -> #a:Type0
  -> b:buffer_t ty a
  -> i:size_t{v i < length b} ->
  Stack a
  (requires fun h0 -> live h0 b)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    r == get h0 b (size_v i))
#push-options "--ifuel 1"
let index #ty #a b i =
  match ty with
  | IMMUT -> IB.index (b <: ibuffer a) i
  | MUT -> B.index (b <: buffer a) i
  | CONST -> CB.index (b <: cbuffer a) i
#pop-options

inline_for_extraction
val upd:
     #a:Type0
  -> b:buffer a
  -> i:size_t{v i < length b}
  -> x:a ->
  Stack unit
  (requires fun h0 -> live h0 b)
  (ensures  fun h0 _ h1 ->
    modifies1 b h0 h1 /\
    B.as_seq h1 b == Seq.upd #a (B.as_seq h0 b) (v i) x)
#push-options "--ifuel 1"
let upd #a b i x =
  B.upd b i x
#pop-options

/// Null-terminated Low* strings.
/// Note that the length gives the number of characters WITHOUT the last NULL
/// character delimiting the end of the string.
[@@ noextract_to "Karamel"] noextract
let is_string_or_null (ty:buftype) (l : G.erased size_nat) (s : buffer_t ty char_t) :
  GTot Type0 =
  if not (g_is_null s) then    
    // Rk.: B.length s <= max_size_t, so we don't need the condition:
    // length+1 <= max_size_t
    length s = l+1
  else G.reveal l = 0

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type string_or_null (ty:buftype) (length : G.erased size_nat) =
  s:buffer_t ty char_t {is_string_or_null ty length s}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type string (ty:buftype) (length : G.erased size_nat) =
  s:string_or_null ty length{not (g_is_null s)}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val wf_string (#ty:buftype) (#length : G.erased size_nat)
              (h : mem) (s : string ty length) : GTot Type0
let wf_string #ty #length h s =
  live h s /\
  (forall (i : nat). i < length ==> get h s i =!= null_char) /\
  get h s length == null_char

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val wf_string_or_null (#ty:buftype) (#length : G.erased size_nat)
                      (h : mem) (s : string_or_null ty length) : GTot Type0
let wf_string_or_null #ty #length h s =
  if g_is_null s then True
  else
    wf_string h s

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val wf_string_i_lem (#ty:buftype) (#length : G.erased size_nat)
                    (h : mem) (s : string ty length)
                    (i : nat{i <= length}):
  Lemma (requires (wf_string h s))
  (ensures (get h s i == null_char <==> i = G.reveal length))
let wf_string_i_lem #length h s i = ()

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val wf_string_not_last_lem (#ty:buftype) (#length : G.erased size_nat)
                           (h : mem) (s : string ty length)
                           (i : nat{i < length}):
  Lemma (requires (wf_string h s))
  (ensures (get h s i =!= null_char))
let wf_string_not_last_lem #ty #length h s i = ()

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val wf_string_last_lem (#ty:buftype) (#length : G.erased size_nat) (h : mem) (s : string ty length) :
  Lemma (requires (wf_string h s))
  (ensures (get h s length == null_char))
let wf_string_last_lem #length h s = ()

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let wf_string_loc (#ty:buftype) (#length : G.erased size_nat) (s : string ty length) :
  GTot B.loc =
  loc s
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let wf_string_loc_addr (#ty:buftype) (#length : G.erased size_nat) (s : string ty length) :
  GTot B.loc =
  loc_addr_of_buffer s
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let wf_string_freeable (#ty:buftype) (#length : G.erased size_nat) (s : string ty length) :
  GTot Type0 =
  freeable s
[@@ noextract_to "Karamel"] inline_for_extraction noextract
let wf_string_as_seq (#ty:buftype) (#length : G.erased size_nat) (h : mem) (s : string ty length) :
  GTot (seq char_t) =
  as_seq h s

[@@ noextract_to "Karamel"] inline_for_extraction noextract
type string256 =
  s:Prims.string{
    forall (i:nat{i < String.length s}). char_v (String.index s i) <= 255}

// This function operates on a null terminated string
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val string_v (#ty : buftype) (h : mem) (s : buffer_t ty char_t) :
  Ghost string256
  (requires True)
  (ensures (fun s' ->
    String.length s' <= length s /\
    (forall (i:nat{i < String.length s'}). String.index s' i == uint8_to_char (get h s i))))

let string_v #ty h s =
  if length s = 0 then ""
  else
    begin
    // Ignore the last character
    let s0 = as_seq h s in
    let s1 = Seq.slice s0 0 (Seq.length s0 - 1) in
    let s2 = seq_uint8_to_char s1 in
    seq_to_string s2
    end

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val wf_string_frame_invariant (#ty:buftype) (#length : G.erased size_nat)
                              (l : B.loc) (s : string ty length) (h0 h1 : mem) :
  Lemma (requires (
    wf_string h0 s /\
    B.modifies l h0 h1 /\
    B.loc_disjoint l (wf_string_loc s)))
  (ensures (wf_string h1 s))
let wf_string_frame_invariant #ty #length l s h0 h1 = ()

(**** Utilities *)
(** Compute the length of a string *)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val string_get_length (#ty:buftype) (#length : G.erased size_nat) (s : string ty length) :
  Stack size_t
  (requires (fun h0 -> wf_string h0 s))
  (ensures (fun h0 l h1 ->
    B.(modifies loc_none h0 h1) /\
    size_v l = G.reveal length))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val string_get_length_aux (#ty:buftype) (#length : G.erased size_nat)
                          (s : string ty length) (i : B.pointer size_t) :
  Stack unit
  (requires (fun h0 ->
    wf_string h0 s /\
    B.live h0 i /\
    B.loc_disjoint (wf_string_loc s) (B.loc_buffer i) /\
    size_v (B.deref h0 i) == 0))
  (ensures (fun h0 l h1 ->
    B.(modifies (loc_buffer i) h0 h1) /\
    size_v (B.deref h1 i) = G.reveal length))

let string_get_length_aux #ty #length s ip =
  (**) let h00 = ST.get () in
  [@inline_let]
  let inv (h : mem) : GTot Type0 =
    wf_string h s /\
    B.live h ip /\
    B.loc_disjoint (wf_string_loc s) (B.loc_buffer ip) /\
    size_v (B.deref h ip) <= length /\
    B.modifies (B.loc_buffer ip) h00 h
  in
  [@inline_let]
  let guard (h : mem{inv h}) : GTot bool =
    let i = B.deref h ip in
    u8_to_UInt8 (get h s (size_v i)) <> u8_to_UInt8 null_char
  in
  [@inline_let]
  let test () : Stack bool
    (requires inv)
    (ensures (fun h0 b h1 -> inv h1 /\ b == guard h1)) =
    let i = B.index ip 0ul in
    let c = index s i in
    u8_to_UInt8 c <> u8_to_UInt8 null_char
  in
  [@inline_let]
  let body () : Stack unit
    (requires (fun h0 -> inv h0 /\ guard h0))
    (ensures (fun h0 _ h1 -> B.(modifies (loc_buffer ip) h0 h1) /\ inv h1)) =
    let i = B.index ip 0ul in
    B.upd ip 0ul FStar.UInt32.(i +^ uint_to_t 1)
  in
  C.Loops.while #inv #(fun b h -> inv h /\ b == guard h) test body;
  (**) let h1 = ST.get () in
  (**) begin
  (**) let i1 = size_v (B.deref h1 ip) in
  (**) assert(i1 <= length);
  (**) assert(get h1 s i1 == null_char);
  (**) wf_string_i_lem h1 s i1;
  (**) assert(i1 = G.reveal length)
  (**) end

let string_get_length #ty #length s =
  push_frame ();
  let ip = B.alloca (FStar.UInt32.uint_to_t 0) 1ul in
  string_get_length_aux s ip;
  let i = B.index ip 0ul in
  pop_frame ();
  i

(** Copy a string *)
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val string_copy (#ty :buftype) (#length : G.erased size_nat)
                (o : string MUT length) (i : string ty length) :
  Stack unit
  (requires (fun h0 ->
    B.live h0 (o <: buffer char_t) /\
    wf_string h0 i /\
    B.loc_disjoint (loc o) (loc i)))
  (ensures (fun h0 l h1 ->
    wf_string h1 o /\
    B.(modifies (wf_string_loc o) h0 h1) /\
    wf_string_as_seq h1 o == wf_string_as_seq h0 i))

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val string_copy_aux (#ty :buftype) (#length : G.erased size_nat)
                    (o : string MUT length) (i : string ty length)
                    (np : B.pointer size_t):
  Stack unit
  (requires (fun h0 ->
    live h0 o /\
    wf_string h0 i /\
    B.live h0 np /\
    B.all_disjoint [loc o; wf_string_loc i; B.loc_buffer np] /\
    size_v (B.deref h0 np) == 0))
  (ensures (fun h0 _ h1 ->
    wf_string h1 o /\
    B.modifies (B.loc_union (LB.loc o) (B.loc_buffer np)) h0 h1 /\
    wf_string_as_seq h1 o == wf_string_as_seq h0 i))

let string_copy_aux #ty #length o i np =
  (**) let h00 = ST.get () in
  [@inline_let]
  let inv (h : mem) : GTot Type0 =
    live h o /\ wf_string h i /\
    B.live h np /\
    B.all_disjoint [loc o; wf_string_loc i; B.loc_buffer np] /\
    B.(modifies (loc_union (LB.loc o) (loc_buffer np)) h00 h) /\
    begin
    let n = size_v (B.deref h np) in
    n <= length /\
    // Originally written with Seq.equal (Seq.slice ...) (Seq.slice ...) but
    // the patterns did not trigger correctly
    (forall (m:nat{m < n}).{:pattern (Seq.index (as_seq h o) m); Seq.index (as_seq h i) m}
      Seq.index (as_seq h o) m == Seq.index (as_seq h i) m)
    end
  in
  [@inline_let]
  let guard (h : mem{inv h}) : GTot bool =
    let n = B.deref h np in
    u8_to_UInt8 (get h i (size_v n)) <> u8_to_UInt8 null_char
  in
  [@inline_let]
  let test () : Stack bool
    (requires inv)
    (ensures (fun h0 b h1 -> inv h1 /\ b == guard h1)) =
    let n = B.index np 0ul in
    let c = index i n in
    u8_to_UInt8 c <> u8_to_UInt8 null_char
  in
  [@inline_let]
  let body () : Stack unit
    (requires (fun h0 -> inv h0 /\ guard h0))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_union (LB.loc o) (loc_buffer np)) h0 h1) /\ inv h1)) =
    (**) let h0 = ST.get () in
    let n = B.index np 0ul in
    (**) assert((forall (m:nat{m < size_v n}). Seq.index (as_seq h0 o) m == Seq.index (as_seq h0 i) m));
    let c = index i n in
    upd o n c;
    B.upd np 0ul (FStar.UInt32.add n (FStar.UInt32.uint_to_t 1));
    (**) let h1 = ST.get () in
    (**) assert((forall (m:nat{m < size_v n}). Seq.index (as_seq h1 o) m == Seq.index (as_seq h1 i) m));
    (**) assert((forall (m:nat{m <= size_v n}). Seq.index (as_seq h1 o) m == Seq.index (as_seq h1 i) m))
  in
  C.Loops.while #inv #(fun b h -> inv h /\ b == guard h) test body;
  (**) let h1 = ST.get () in
  (**) assert(forall (m:nat{m < length}). Seq.index (as_seq h1 o) m == Seq.index (as_seq h1 i) m);
  // We need to update the last character - null_char
  let n = B.index np 0ul in
  (**) assert(size_v n == G.reveal length);
  (**) assert(Seq.index (as_seq h1 i) length == null_char);
  upd o n null_char;
  // Finish the proof
  (**) let h2 = ST.get () in
  (**) assert(Seq.index (as_seq h2 o) length == null_char);
  (**) assert(forall (m:nat{m <= length}). Seq.index (as_seq h2 o) m == Seq.index (as_seq h2 i) m);
  (**) assert(Seq.equal (as_seq h2 o) (as_seq h2 i));
  (**) assert(as_seq h2 i == as_seq h00 i);
  (**) assert(as_seq h2 o == as_seq h2 i)

let string_copy #ty #length o i =
  push_frame ();
  let np = B.alloca (FStar.UInt32.uint_to_t 0) 1ul in
  string_copy_aux o i np;
  pop_frame ()

/// When converting from bytes to string: we may need to check if the content of
/// the buffer doesn't contain 0.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val bytes_no_zero (#ty:buftype) (l : size_t) (buf : buffer_t ty uint8) :
  Stack bool
  (requires (fun h0 -> live h0 buf /\ length buf == size_v l))
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b <==> (forall (i:nat{i < size_v l}). uint_v (Seq.index (as_seq h1 buf) i) =!= 0))))

// This can be generalized. No use for now though.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val bytes_no_zero_aux (#ty:buftype) (l : size_t)
                      (buf : buffer_t ty uint8)
                      (i : B.pointer size_t) :
  Stack unit
  (requires (fun h0 ->
    live h0 buf /\ length buf == size_v l /\
    B.live h0 i /\
    B.loc_disjoint (loc buf) (B.loc_buffer i) /\
    size_v (B.deref h0 i) == 0))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer i) h0 h1) /\
    begin
    let i = size_v (B.deref h1 i) in
    i <= size_v l /\
    (forall (j:nat{j < i}). uint_v (Seq.index (as_seq h1 buf) j) =!= 0) /\
    (i < size_v l ==> uint_v (Seq.index (as_seq h1 buf) i) = 0)
    end))

let bytes_no_zero_aux #ty l buf ip =
  (**) let h00 = ST.get () in
  [@inline_let]
  let inv (h : mem) : GTot Type0 =
    live h buf /\ length buf == size_v l /\
    B.live h ip /\
    B.loc_disjoint (loc buf) (B.loc_buffer ip) /\
    B.modifies (B.loc_buffer ip) h00 h /\
    begin
    let i = size_v (B.deref h ip) in
    i <= size_v l /\
    (forall (j:nat{j < i}). {:pattern (Seq.index (as_seq h buf) j)}
      uint_v (Seq.index (as_seq h buf) j) =!= 0)
    end
  in
  [@inline_let]
  let guard (h : mem{inv h}) : GTot bool =
    let i = B.deref h ip in
    size_v i < size_v l && uint_v (get h buf (size_v i)) <> 0
  in
  [@inline_let]
  let test () : Stack bool
    (requires inv)
    (ensures (fun h0 b h1-> inv h1 /\ b == guard h1)) =
    let i = B.index ip 0ul in
    if FStar.UInt32.(i <^ l) then
      begin
      let c = index buf i in
      u8_to_UInt8 c <> u8_to_UInt8 null_char
      end
    else
      begin
      false
      end
  in
  [@inline_let]
  let body () : Stack unit
    (requires (fun h0 -> inv h0 /\ guard h0))
    (ensures (fun h0 _ h1 -> B.(modifies (loc_buffer ip) h0 h1) /\ inv h1)) =
    (**) let h0 = ST.get () in
    let i = B.index ip 0ul in
    B.upd ip 0ul FStar.UInt32.(i +^ uint_to_t 1);
    (**) let h1 = ST.get () in
    (**) begin
    (**) assert(forall (j:nat{j < size_v i}). uint_v (Seq.index (as_seq h0 buf) j) =!= 0);
    (**) assert(forall (j:nat{j < size_v i}). uint_v (Seq.index (as_seq h1 buf) j) =!= 0)
    (**) end
  in
  C.Loops.while #inv #(fun b h -> inv h /\ b == guard h) test body;
  (**) let h1 = ST.get () in
  (**) assert(not (guard h1))

let bytes_no_zero #ty l buf =
  (**) let h0 = ST.get () in
  push_frame ();
  let ip = B.alloca (FStar.UInt32.uint_to_t 0) 1ul in
  bytes_no_zero_aux #ty l buf ip;
  let i = B.index ip 0ul in
  (**) let h1 = ST.get () in
  (**) begin
  (**) assert(forall (j:nat{j < size_v i}). uint_v (Seq.index (as_seq h1 buf) j) =!= 0);
  (**) assert(i = l ==> (forall (j:nat{j < size_v l}). uint_v (Seq.index (as_seq h1 buf) j) =!= 0));
  (**) assert(i =!= l ==> uint_v (Seq.index (as_seq h1 buf) (size_v i)) = 0);
  (**) assert(i =!= l ==> ~(forall (j:nat{j < size_v l}). uint_v (Seq.index (as_seq h1 buf) j) =!= 0))
  (**) end;
  pop_frame ();
  i = l

(*** Stateful string instance *)
/// Below, we define several instantiations of stateful classes for string.
/// Note that both [lstring] and [hstring] extract to string pointers,
/// because only the pointer field is not erased at extraction.

/// [lstring]: we carry the ghost length with the string pointer.
inline_for_extraction
noeq type lstring_raw (str_ty : Type0) = {
  lstr_length : G.erased size_nat; // erased
  lstr_str : str_ty; // Not being able to put string_or_null ty lstr_length here is a bit annoying for type inference
}

/// Note that we enforce that strings can be used as authentication data for
/// encryption/decryption. We need it to serialize/deserialize the peers
/// (we use the peer names as AD for the encryption/decryption of the long term
/// keys). The following constant is the maximum length a string can have (without
/// the termination character) accordingly.
/// Note that this constant is by far big enough for peer names...
let max_string_length : size_nat =
  // We have: len1 < len2, but writing it this way makes the proofs
  // easier (we want to have: forall nc. max_string_length <= aead_max_input nc
  let len1 = pow2 31 in
  let len2 = pow2 32 - 1 - 16 in
  if len1 <= len2 then len1 else len2

inline_for_extraction
type lstring (ty : buftype) : Type0 =
  s:lstring_raw (buffer_t ty char_t){
    is_string_or_null ty s.lstr_length s.lstr_str /\
    s.lstr_length <= max_string_length}

// For the type abbreviation - TODO: make Karamel inline the lstring_raw abbreviation
type noise_string = lstring MUT
type noise_cstring = lstring CONST

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let lstring_null (ty : buftype) : lstring ty =
  {
    lstr_length = 0;
    lstr_str = null #ty char_t;
  }

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_invariant (#ty : buftype) (h : mem) (str : lstring ty) : GTot Type0
let lstring_invariant #ty h str =
  wf_string_or_null #ty #str.lstr_length h str.lstr_str

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_freeable (#ty : buftype) (str : lstring ty) : GTot Type0
let lstring_freeable #ty str =
  buffer_or_null_freeable str.lstr_str

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let lstring_footprint (#ty : buftype) (str : lstring ty) : GTot B.loc =
  buffer_or_null_loc_addr str.lstr_str

// TODO: hstring should store the length (hstring is always used internally).
/// [hstring]: heap allocated string. Note that we add a pointer indirection.
/// We do that in order to be able to implement [copy].
inline_for_extraction
noeq type hstring = {
  hstr_ptr : B.pointer (lstring MUT);
  // The region containing the string - allows to implement copy without
  // asking for a region on the user side
  hstr_r : rid; // erased
  // The sub-region in which to allocate new strings, whenever we need
  // reallocation. We need to remember it, otherwise we can't prove
  // disjointness with the pointer (which is also allocated in hstr_r)
  hstr_r_str : rid; // erased
}

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_invariant (h : mem) (str : hstring) : GTot Type0
let hstring_invariant h str_p =
  let str = B.deref h str_p.hstr_ptr in
  B.live h str_p.hstr_ptr /\
  B.freeable str_p.hstr_ptr /\
  lstring_invariant h str /\
  lstring_freeable str /\
  is_eternal_region str_p.hstr_r /\
  is_eternal_region str_p.hstr_r_str /\
  str_p.hstr_r <> root /\
  begin
  // We don't waste space (also saves some tests)
  not (B.g_is_null str.lstr_str) ==>
  str.lstr_length > 0
  end /\
  // Aliasing
  begin
  let str_p_loc = B.loc_addr_of_buffer str_p.hstr_ptr in
  let str_loc = lstring_footprint str in
  B.loc_disjoint str_p_loc str_loc /\
  B.loc_disjoint str_p_loc (region_to_loc str_p.hstr_r_str) /\
  region_includes_region str_p.hstr_r str_p.hstr_r_str /\
  region_includes str_p.hstr_r (B.loc_union str_p_loc str_loc)
  end

[@@ noextract_to "Karamel"] inline_for_extraction noextract
let hstring_footprint (str : hstring) : GTot B.loc =
  region_to_loc str.hstr_r

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_v (#ty : buftype) (h : mem) (s : lstring ty) :
  Ghost string256
  (requires True)
  (ensures (fun s' ->    
    String.length s' <= max_string_length /\
    // Sanity check, mostly
    (lstring_invariant h s ==> String.length s' = G.reveal s.lstr_length)))

let lstring_v #ty h s =
  // This is a bit annoying, but we need the postcondition on
  // the length.
  let s_v = string_v #ty h s.lstr_str in
  if String.length s_v > max_string_length then
    String.sub s_v 0 max_string_length
  else s_v

val lstring_v_null_is_empty (ty : buftype) (h : mem) :
  Lemma (lstring_v h (lstring_null ty) == "")
  [SMTPat (lstring_v h (lstring_null ty))]
let lstring_v_null_is_empty ty h =
  assert(String.length (lstring_v h (lstring_null ty)) = 0)

val hstring_v (h : mem) (s : hstring) : GTot string256
let hstring_v h s =
  let str = B.deref h s.hstr_ptr in
  lstring_v h str

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_frame_invariant (#ty : buftype) (l : B.loc) (s : lstring ty) (h0 h1 : mem) :
  Lemma
  (requires (
    lstring_invariant h0 s /\
    B.loc_disjoint l (lstring_footprint s) /\
    B.modifies l h0 h1))
  (ensures (
    lstring_invariant h1 s /\
    lstring_v h0 s == lstring_v h1 s))

let lstring_frame_invariant #ty l s h0 h1 = ()

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_frame_invariant (l : B.loc) (s : hstring) (h0 h1 : mem) :
  Lemma
  (requires (
    hstring_invariant h0 s /\
    B.loc_disjoint l (hstring_footprint s) /\
    B.modifies l h0 h1))
  (ensures (
    hstring_invariant h1 s /\
    hstring_v h0 s == hstring_v h1 s))

let hstring_frame_invariant l s h0 h1 = ()

/// [clstring]: constant lstring
inline_for_extraction
type clstring = lstring CONST

/// A stateful well-formed string.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_stateful (ty : buftype) : Impl.Noise.Stateful.stateful unit

let lstring_stateful (ty : buftype) =
Stateful
  // s
  (fun _ -> lstring ty)

  // footprint
  (fun #_ s -> lstring_footprint s)
  // freeable
  (fun #_ h s -> lstring_freeable s)
  // invariant
  (fun #_ h s -> lstring_invariant h s)

  // t
  (fun _ -> s:string256{String.length s <= max_string_length})
  // v
  (fun _ h s -> lstring_v h s)

  // frame invariant
  (fun #_ l s h0 h1 -> lstring_frame_invariant l s h0 h1)
  // frame freeable
  (fun #_ l s h0 h1 -> ())

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val clstring_stateful : Impl.Noise.Stateful.stateful unit

let clstring_stateful = lstring_stateful CONST

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_free (ty : buftype{ty <> CONST}) : free_st (lstring_stateful ty)
#push-options "--ifuel 1"
let lstring_free ty _ s =
  if is_null s.lstr_str then ()
  else
    match ty with
    | IMMUT -> IB.free (s.lstr_str <: ibuffer char_t)
    | MUT -> B.free (s.lstr_str <: buffer char_t)
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_clone_gen (ty0 ty1 : buftype) :
  r:rid ->
  input:lstring ty0 ->
  ST (lstring ty1)
  (requires (fun h0 ->
    is_eternal_region r /\
    lstring_invariant h0 input /\
    (ty1 = IMMUT ==> ty0 <> CONST) // We don't know what to do in this situation...
    ))
  (ensures (fun h0 p h1 ->
    lstring_invariant h1 p /\
    B.(modifies loc_none h0 h1) /\
    B.(loc_includes (loc_all_regions_from false r) (lstring_footprint p)) /\
    lstring_freeable p /\
    lstring_v h1 p == lstring_v h0 input /\
    // We don't waste space
    (not (g_is_null p.lstr_str) ==> p.lstr_length > 0)))

#push-options "--ifuel 1"
let lstring_clone_gen ty0 ty1 r input =
    (**) let h0 = ST.get () in
  [@inline_let]
  let str : string_or_null ty0 input.lstr_length = input.lstr_str in
  let b = is_null str in
  if b then
    begin
    [@inline_let]
    let out : lstring ty1 = {
      lstr_length = 0;
      lstr_str = null #ty1 char_t <: buffer_t ty1 char_t;
    }
    in
    (**) let h1 = ST.get () in
    (**) assert(lstring_invariant h1 out);
    (**) lstring_v_null_is_empty ty0 h1;
    (**) lstring_v_null_is_empty ty1 h1;
    out
    end
  else
    let len = string_get_length str in
    if len = 0ul then
      begin
      [@inline_let]
      let out : lstring ty1 = {
        lstr_length = 0;
        lstr_str = null #ty1 char_t <: buffer_t ty1 char_t;
      } in
      out
      end
    else
      begin
      [@inline_let]
      let malloc_len = FStar.UInt32.(len +^ 1ul) in
      let out_str : buffer_t ty1 char_t =
        if ty1 = IMMUT then
          begin
          match ty0 with
          | IMMUT ->
            IB.imalloc_and_blit r (input.lstr_str <: ibuffer char_t) 0ul malloc_len
          | MUT ->
            IB.imalloc_and_blit r (input.lstr_str <: buffer char_t) 0ul malloc_len
          end
        else
          begin
          let out_str : buffer char_t =  B.malloc r null_char malloc_len in
          string_copy #ty0 #(UInt32.v len) out_str str;
          [@inline_let]
          let out_str : buffer_t ty1 char_t =
            match ty1 with
            | MUT -> out_str
            | CONST -> CB.of_buffer (out_str <: buffer char_t)
          in
          out_str
          end
      in
      (**) let h1 = ST.get () in
      [@inline_let]
      let out : lstring ty1 = {
        lstr_length = size_v len;
        lstr_str = out_str;
      }
      in
      (**) let h1 = ST.get () in
      (**) assert(lstring_v h1 out == lstring_v h0 input);
      (**) assert(B.(modifies (LB.loc out_str) h0 h1));
      (**) B.(modifies_only_not_unused_in loc_none h0 h1);
      out
      end
#pop-options

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_clone (ty : buftype) : clone_st (lstring_stateful ty)

let lstring_clone ty #_ r (input : lstring ty) =
  lstring_clone_gen ty ty r input

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_to_bytes_seq (ty : buftype) : to_bytes_seq_t (lstring_stateful ty)

let lstring_to_bytes_seq ty #i s =
  seq_char_to_uint8 (string_to_seq s)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_stateful : Impl.Noise.Stateful.stateful unit

let hstring_stateful =
Stateful
  // s
  (fun _ -> hstring)

  // footprint
  (fun #_ s -> hstring_footprint s)
  // freeable
  (fun #_ h s -> True)
  // invariant
  (fun #_ h s -> hstring_invariant h s)

  // t
  (fun _ -> s:string256{String.length s <= max_string_length})

  // v
  (fun _ h s -> hstring_v h s)

  // frame invariant
  (fun #_ l s h0 h1 -> hstring_frame_invariant l s h0 h1)
  // frame freeable
  (fun #_ l s h0 h1 -> ())

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_clone : clone_st hstring_stateful
let hstring_clone #_ r0 (input : hstring) =
  (**) let h0 = ST.get () in
  let r = new_region r0 in
  let r_str = new_region r in
  let r_ptr = new_region r in
  (**) assert(region_includes_region r r_str);
  (**) assert(region_includes_region r r_ptr);
  (**) assert(region_includes_region r0 r_str);
  (**) assert(region_includes_region r0 r_ptr);
  let str = B.index input.hstr_ptr 0ul in
  // Calling [lstring_clone_gen] instead of [lstring_clone]: its postcondition
  // is more precise.
  let out_str = lstring_clone_gen MUT MUT r_str str in
  let out_ptr = B.malloc r_ptr out_str 1ul in
  (**) assert(region_includes r_ptr (B.loc_addr_of_buffer out_ptr));
  [@inline_let]
  let out = {
    hstr_ptr = out_ptr;
    hstr_r = r;
    hstr_r_str = r_str;
  }
  in
  (**) let h1 = ST.get () in
  (**) assert(hstring_invariant h1 out);
  out

/// Rk.: we make the hypothesis that we don't need to free the pointer provided
/// by the user.
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_copy : copy_st hstring_stateful
let hstring_copy _ out input =
  let r_str = out.hstr_r_str in
  let input_str = B.index input.hstr_ptr 0ul in
  let out_str = lstring_clone_gen MUT MUT r_str input_str in
  B.upd out.hstr_ptr 0ul out_str

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_malloc : malloc_st hstring_stateful
let hstring_malloc _ r0 =
  let r = new_region r0 in
  let r_str = new_region r in
  let r_ptr = new_region r in
  (**) assert(region_includes_region r r_str);
  (**) assert(region_includes_region r r_ptr);
  (**) assert(region_includes_region r0 r_str);
  (**) assert(region_includes_region r0 r_ptr);
  [@inline_let]
  let out_str = {
    lstr_length = 0;
    lstr_str = null #MUT char_t;
  }
  in
  let out_ptr = B.malloc r_ptr out_str 1ul in
  [@inline_let]
  let out = {
    hstr_ptr = out_ptr;
    hstr_r = r;
    hstr_r_str = r_str;
  }
  in
  (**) let h1 = ST.get () in
  out

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_free : free_st hstring_stateful
let hstring_free _ s =
  let str = B.index s.hstr_ptr 0ul in
  lstring_free MUT () str;
  B.free s.hstr_ptr

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_malloc_from_input : malloc_from_input_st (lstring_stateful MUT) hstring_stateful
let hstring_malloc_from_input _ r0 input =
  let r = new_region r0 in
  let r_str = new_region r in
  let r_ptr = new_region r in
  (**) assert(region_includes_region r r_str);
  (**) assert(region_includes_region r r_ptr);
  (**) assert(region_includes_region r0 r_str);
  (**) assert(region_includes_region r0 r_ptr);
  let out_str = lstring_clone_gen MUT MUT r_str input in
  let out_ptr = B.malloc r_ptr out_str 1ul in
  [@inline_let]
  let out = {
    hstr_ptr = out_ptr;
    hstr_r = r;
    hstr_r_str = r_str;
  }
  in
  (**) let h1 = ST.get () in
  out

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_from_hstring : input_from_output_st (lstring_stateful MUT) hstring_stateful
let lstring_from_hstring _ input =
  let lstr = B.index input.hstr_ptr 0ul in
  [@inline_let]
  let str : buffer char_t = lstr.lstr_str in
  {
    lstr_length = lstr.lstr_length;
    lstr_str = str;
  }

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_to_bytes_seq : to_bytes_seq_t hstring_stateful

let hstring_to_bytes_seq #i s =
  seq_char_to_uint8 (string_to_seq s)

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_to_bytes : to_bytes_st hstring_to_bytes_seq

#push-options "--z3rlimit 100"
let hstring_to_bytes #i r out outlen s0 =
  (**) let h0 = ST.get () in
  let s1 = B.index s0.hstr_ptr 0ul in
  if B.is_null s1.lstr_str then
    begin
    B.upd out 0ul B.null;
    B.upd outlen 0ul 0ul;
    (**) let h1 = ST.get () in
    begin
    (**) assert(hstring_v h0 s0 == "");
    (**) assert(Seq.equal (hstring_to_bytes_seq "") Seq.empty);
    (**) assert(Seq.equal (B.as_seq h1 (B.deref h1 out)) Seq.empty);
    (**) assert(B.as_seq h1 (B.deref h1 out) == hstring_to_bytes_seq (hstring_v h0 s0))
    end
    end
  else
    begin
    // Note that the length is necessarily > 0 following the invariant
    let len = string_get_length #MUT #s1.lstr_length s1.lstr_str in
    let out1 = B.malloc r (u8_from_UInt8 (U8.uint_to_t 0)) len in
    let s2 = s1.lstr_str in //buffer_char_to_uint8 s1.lstr_str in
    B.blit s2 0ul out1 0ul len;
    B.upd out 0ul out1;
    B.upd outlen 0ul len;
    (**) let h1 = ST.get () in
    (**) begin
    (**) let l0 = B.(loc_union (loc_buffer out) (loc_buffer outlen)) in
    (**) B.(modifies_only_not_unused_in l0 h0 h1);
    (**) let s0_v = hstring_v h0 s0 in
    (**) let bs_v = hstring_to_bytes_seq s0_v in
    (**) assert(bs_v == seq_char_to_uint8 (string_to_seq s0_v));
    (**) let s1_v = B.as_seq h0 s1.lstr_str in
    (**) let s2_v = Seq.slice s1_v 0 (Seq.length s1_v - 1) in
    (**) assert(s0_v == seq_to_string (seq_uint8_to_char s2_v));
    (**) let out1_v = B.as_seq h1 out1 in
    (**) assert(Seq.equal out1_v (Seq.slice s1_v 0 (size_v len)));
    (**) assert(Seq.slice s1_v 0 (size_v len) == Seq.slice s1_v 0 (size_v len));
    (**) assert(B.as_seq h1 out1 == seq_char_to_uint8 (string_to_seq s0_v));
    (**) assert(out1_v == bs_v)
    (**) end
    end
#pop-options


[@@ noextract_to "Karamel"] inline_for_extraction noextract
val clstring_cast_to_bytes : cast_to_bytes_st (lstring_to_bytes_seq MUT)

let clstring_cast_to_bytes #i s0 =
  (**) let h0 = ST.get () in
  [@inline_let] let s : buffer uint8 = s0.lstr_str in
//  [@inline_let] let s = CB.to_buffer s0.lstr_str in
  if is_null s then
    begin
    (**) assert(Seq.equal (lstring_to_bytes_seq MUT "") Seq.empty);
    (**) assert(Seq.equal (B.as_seq h0 (B.null #uint8)) Seq.empty);
    (0ul, B.null)
    end
  else
    begin
    let l = string_get_length #MUT #s0.lstr_length s0.lstr_str in
    if l = 0ul then
      begin
      (**) assert(Seq.equal (lstring_to_bytes_seq MUT "") Seq.empty);
      (**) assert(Seq.equal (B.as_seq h0 (B.null #uint8)) Seq.empty);
      (0ul, B.null)
      end
    else
      begin
      let s = B.sub s 0ul l in
      (**) let h2 = ST.get () in
      (**) assert(B.as_seq h2 s == lstring_to_bytes_seq MUT (lstring_v h0 s0));
      (l, s)
      end
    end

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_cast_to_bytes : cast_to_bytes_st hstring_to_bytes_seq

let hstring_cast_to_bytes #i s0 =
  (**) let h0 = ST.get () in
  (**) assert(hstring_invariant h0 s0);
  let s = B.index s0.hstr_ptr 0ul in
  if B.is_null s.lstr_str then
    begin
    (**) assert(hstring_v h0 s0 == "");
    (**) assert(Seq.equal (hstring_to_bytes_seq "") Seq.empty);
    (**) assert(Seq.equal (B.as_seq h0 (B.null #uint8)) Seq.empty);
    (0ul, B.null)
    end
  else
    begin
    let l = string_get_length #MUT #s.lstr_length s.lstr_str in
    [@inline_let] let s = s.lstr_str in
    let s = B.sub s 0ul l in
    (**) let h1 = ST.get () in
    (**) assert(B.as_seq h1 s == hstring_to_bytes_seq (hstring_v h0 s0));
    (l, s)
    end

[@@ noextract_to "Karamel"] inline_for_extraction noextract
val lstring_input_to_bytes_seq (ty : buftype) : input_to_bytes_seq_t (lstring_stateful ty) hstring_to_bytes_seq

let lstring_input_to_bytes_seq ty #i s =
  seq_char_to_uint8 (string_to_seq s)

// Note: it would be good to request const char* buffers as user inputs,
// but we can't for several reasons. First, we can't cast from char* to
// uint8* (this comes from the limits of the Low* memory model). Moreover,
// using const buffers is difficult, because Hacl* doesn't handle them,
// and it would require a fair amount of updates. For now, we thus
// use uint8* buffers everywhere (no char*, no const buffers).
[@@ noextract_to "Karamel"] inline_for_extraction noextract
val hstring_smficc : Impl.Noise.Stateful.stateful_malloc_from_input_clone_copy unit

let hstring_smficc =
  Stateful_malloc_from_input_clone_copy
    (lstring_stateful MUT)
    hstring_stateful
    hstring_malloc
    hstring_malloc_from_input
    hstring_clone
    hstring_free
    hstring_copy
    lstring_from_hstring
    hstring_to_bytes_seq
    hstring_cast_to_bytes
    (lstring_input_to_bytes_seq MUT)
    clstring_cast_to_bytes
