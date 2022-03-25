module Impl.Noise.BufferEquality

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

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** Buffer equality *)
// TODO: move?
val logxor_uint_eq_zero_lem :#t:inttype{unsigned t} -> #l:secrecy_level -> a:uint_t t l -> b:uint_t t l ->
  Lemma (logxor a b == zeros t l <==> a == b)

let logxor_uint_eq_zero_lem #t #l a b =
  assert(v (zeros t l) = 0);
  UInt.logxor_neq_nonzero #(bits t) (v a) (v b);
  assert(
    Lib.IntTypes.v a <> Lib.IntTypes.v b ==>
    UInt.logxor #(bits t) (Lib.IntTypes.v a) (Lib.IntTypes.v b) <> 0);
  logxor_spec a b;
  assert(v a <> v b ==> v (logxor a b) <> 0);
  assert((~(a == b)) ==> v (logxor a b) <> 0);
  UInt.logxor_self #(bits t) (v a);
  logxor_spec a a

val logxor_commutative: #t:inttype{unsigned t} -> #l:secrecy_level -> a:uint_t t l -> b:uint_t t l ->
  Lemma (requires True) (ensures (logxor a b == logxor b a))

let logxor_commutative #t #l a b =
  logxor_spec a b;
  logxor_spec b a;
  UInt.logxor_commutative #(bits t) (v a) (v b)

val logxor_associative: #t:inttype{unsigned t} -> #l:secrecy_level -> a:uint_t t l -> b:uint_t t l -> c:uint_t t l ->
  Lemma (requires True) (ensures (logxor (logxor a b) c == logxor a (logxor b c)))

let logxor_associative #t #l a b c =
  logxor_spec a b;
  logxor_spec b c;
  logxor_spec (logxor a b) c;
  logxor_spec a (logxor b c);
  UInt.logxor_associative #(bits t) (v a) (v b) (v c)

val logor_eq_zero_i (#n:pos) (a:UInt.uint_t n) (b:UInt.uint_t n) (i : nat{i < n}) :
  Lemma (requires True)
  (ensures (
    UInt.nth (UInt.logor a b) i == false <==>
    (UInt.nth a i == false /\
     UInt.nth b i == false)))
  [SMTPat (UInt.nth (UInt.logor a b) i)]

let logor_eq_zero_i #n a b i = ()

module BV = FStar.BitVector

val nth_zero_eq_lemma1: #n:pos -> a:UInt.uint_t n ->
  Lemma (a == UInt.zero n ==> (forall (i:nat{i<n}). UInt.nth a i = false))

let nth_zero_eq_lemma1 #n a = ()

val nth_zero_eq_lemma2_aux: #n:pos -> a:UInt.uint_t n ->
  Lemma
  (requires (forall (i:nat{i<n}). UInt.nth a i = false))
  (ensures (a == UInt.zero n))

let nth_zero_eq_lemma2_aux #n a =
  let lemi (i:nat{i<n}) :
    Lemma(UInt.nth a i = UInt.nth (UInt.zero n) i)
    [SMTPat (UInt.nth a i)] =
    assert(UInt.nth a i = false);
    UInt.zero_nth_lemma #n i
  in
  assert(forall (i:nat{i<n}). UInt.nth a i = UInt.nth (UInt.zero n) i);
  UInt.nth_lemma #n a (UInt.zero n)

val nth_zero_eq_lemma2: #n:pos -> a:UInt.uint_t n ->
  Lemma
  ((forall (i:nat{i<n}). UInt.nth a i = false) ==> (a == UInt.zero n))

let nth_zero_eq_lemma2 #n a =
  // This proof is insanely complex because of problems with pattern matching...
  let foralli_eq a = (forall (i:nat{i<n}). UInt.nth #n a i = false) in
  let eq (a b : UInt.uint_t n) = (a = b) in
  let l a :
  Lemma
  (requires (foralli_eq a))
  (ensures (eq a (UInt.zero n)))
  [SMTPat (eq a (UInt.zero n))] =
  nth_zero_eq_lemma2_aux #n a
  in
  assert(foralli_eq a <==> eq a (UInt.zero n))

val nth_zero_eq_lemma: #n:pos -> a:UInt.uint_t n ->
  Lemma (a == UInt.zero n <==> (forall (i:nat{i<n}). UInt.nth a i = false))

let nth_zero_eq_lemma #n a =
  nth_zero_eq_lemma1 a;
  nth_zero_eq_lemma2 a

val logor_eq_zero: #t:inttype{unsigned t} -> #l:secrecy_level -> a:uint_t t l -> b:uint_t t l ->
  Lemma (requires True) (ensures (logor a b == zeros t l <==> (a == zeros t l /\ b == zeros t l)))

let logor_eq_zero #t #l a b =
 logor_spec a b;
 let n = bits t in
 let av : UInt.uint_t n = v a in
 let bv : UInt.uint_t n = v b in
 assert(v (logor a b) == UInt.logor av bv);
 assert(forall (i : nat{i < n}).
    UInt.nth (UInt.logor #n av bv) i == false <==>
    (UInt.nth #n av i == false /\
     UInt.nth #n bv i == false));
 assert((v (logor a b) = 0) <==> (UInt.logor #(bits t) (v a) (v b) == UInt.zero n));
 nth_zero_eq_lemma #n (UInt.logor av bv);
 nth_zero_eq_lemma #n av;
 nth_zero_eq_lemma #n bv

/// Constant-time comparison of buffers
inline_for_extraction noextract
val lbuffers_uint_eq_aux :
     #t:inttype{unsigned t}
  -> #l:secrecy_level
  -> #len:size_t
  -> b1:lbuffer (uint_t t l) len
  -> b2:lbuffer (uint_t t l) len
  -> accp:B.pointer (uint_t t l) ->
  Stack unit
  (requires (fun h ->
    live h b1 /\ live h b2 /\ B.live h accp /\
    B.disjoint accp (b1 <: B.buffer (uint_t t l)) /\ B.disjoint accp (b2 <: B.buffer (uint_t t l)) /\
    B.deref h accp == zeros t l))
  (ensures (fun h0 _ h1 ->
    modifies1 accp h0 h1 /\
    (B.deref h1 accp == zeros t l <==>
     Seq.equal (as_seq h0 b1) (as_seq h0 b2))))

let lbuffers_uint_eq_aux #t #l #len b1 b2 accp =
  (**) let h0 = ST.get () in
  Lib.Loops.for 0ul len
    (fun h i ->
      live h b1 /\ live h b2 /\ B.live h accp /\
      modifies1 accp h0 h /\
      (B.deref h accp == zeros t l <==>
       (forall (j : nat{j < i}). Seq.index (as_seq h0 b1) j == Seq.index (as_seq h0 b2) j)))
    (fun i ->
      (**) let h1 = ST.get () in
      let x1 = index b1 i in
      let x2 = index b2 i in
      let diff = logxor x1 x2 in
      let acc = B.index accp 0ul in
      let acc' = logor diff acc in
      B.upd accp 0ul acc';
      (**) let h2 = ST.get () in
      (**) logxor_uint_eq_zero_lem x1 x2;
      (**) assert(diff == zeros t l <==> x1 == x2);
      (**) logor_eq_zero diff acc;
      (**) [@inline_let] let s1 = as_seq h0 b1 in
      (**) [@inline_let] let s2 = as_seq h0 b2 in
      (**) [@inline_let] let i = size_v i in
      (**) assert(
      (**)   B.deref h1 accp == zeros t l <==>
      (**)   (forall (j : nat{j < i}). Seq.index s1 j == Seq.index s2 j));
      (**) assert(
      (**)   (forall (j : nat{j < i+1}). Seq.index s1 j == Seq.index s2 j) <==>
      (**)   ((forall (j : nat{j < i}). Seq.index s1 j == Seq.index s2 j) /\
      (**)   Seq.index s1 i == Seq.index s2 i))
      );
  (**) let h1 = ST.get () in
  (**) assert(
  (**)   B.deref h1 accp == zeros t l <==>
  (**)   (forall (j : nat{j < size_v len}). Seq.index (as_seq h0 b1) j == Seq.index (as_seq h0 b2) j));
  (**) assert(
  (**)   B.deref h1 accp == zeros t l <==>
  (**)   Seq.equal (as_seq h0 b1) (as_seq h0 b2))

/// WARNING: BREAKS parametricity
inline_for_extraction noextract
val uint_is_zero :
     #t:inttype{unsigned t /\ t <> U1} // TODO: add conversion for U1 in Lib.RawIntTypes
  -> #l:secrecy_level
  -> u:uint_t t l ->
  Pure bool
  (requires True)
  (ensures (fun b -> b <==> v u = 0))

#push-options "--ifuel 1"
let uint_is_zero #t #l u =
  if l = PUB then
    [@inline_let] let u : int_t t PUB = u in
    match t with
    | U8 -> u = UInt8.uint_to_t 0
    | U16 -> u = UInt16.uint_to_t 0
    | U32 -> u = UInt32.uint_to_t 0
    | U64 -> u = UInt64.uint_to_t 0
    | U128 -> UInt128.eq u (Int.Cast.Full.uint64_to_uint128 (UInt64.uint_to_t 0))
  else
    match t with
    | U8 -> u8_to_UInt8 u = UInt8.uint_to_t 0
    | U16 -> u16_to_UInt16 u = UInt16.uint_to_t 0
    | U32 -> u32_to_UInt32 u = UInt32.uint_to_t 0
    | U64 -> u64_to_UInt64 u = UInt64.uint_to_t 0
    | U128 -> UInt128.eq (u128_to_UInt128 u) (Int.Cast.Full.uint64_to_uint128 (UInt64.uint_to_t 0))
#pop-options

inline_for_extraction noextract
val lbuffers_uint_eq :
     #t:inttype{unsigned t /\ t <> U1}
  -> #l:secrecy_level
  -> #len:size_t
  -> b1:lbuffer (uint_t t l) len
  -> b2:lbuffer (uint_t t l) len ->
  Stack bool
  (requires (fun h ->
    live h b1 /\ live h b2))
  (ensures (fun h0 b h1 ->
    modifies0 h0 h1 /\
    (b <==> Seq.equal (as_seq h0 b1) (as_seq h0 b2))))

let lbuffers_uint_eq #t #l #len b1 b2 =
  let h0 = ST.get () in
  push_frame ();
  let accp = B.alloca (zeros t l) 1ul in
  lbuffers_uint_eq_aux b1 b2 accp;
  let r = B.index accp 0ul in
  pop_frame ();
  uint_is_zero r

//inline_for_extraction noextract
[@ "c_inline"]
val lbytes_eq :
     #len:size_t
  -> b1:lbuffer uint8 len
  -> b2:lbuffer uint8 len ->
  Stack bool
  (requires (fun h ->
    live h b1 /\ live h b2))
  (ensures (fun h0 b h1 ->
    modifies0 h0 h1 /\
    (b = BS.lbytes_eq (as_seq h0 b1) (as_seq h0 b2))))

let lbytes_eq #len b1 b2 =
  lbuffers_uint_eq b1 b2
