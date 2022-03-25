module Impl.Noise.TypeOrUnit

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open Impl.Noise.Types

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let lbuffer_malloc_also_empty #a #len r init =
  if len >. 0ul then
    B.malloc r init len
  else
    begin
    (**) let h0 = HST.get () in
    (**) assert(Seq.equal (Seq.create (size_v len) init) Seq.empty);
    (**) assert(B.as_seq h0 (null #MUT #a) `Seq.equal` Seq.empty);
    null
    end

let lbuffer_malloc_copy #a #len r init i =
  (**) let h0 = HST.get () in
  let o = B.malloc r init len in
  copy #MUT #a #len o i;
  (**) let h2 = HST.get () in
  (**) B.(modifies_only_not_unused_in loc_none h0 h2);
  o

let lbuffer_malloc_copy_also_empty #a #len r init i =
  if len >. 0ul then
    lbuffer_malloc_copy r init i
  else
    begin
    (**) let h0 = HST.get () in
    (**) assert(as_seq h0 i `Seq.equal` (Seq.empty #a));
    (**) assert(B.as_seq h0 (null #MUT #a) `Seq.equal` Seq.empty);
    null
    end

let lbuffer_or_unit_frame_lem #a #len #b l h0 h1 opt_buf = ()

let lbuffer_or_unit_alloca #a #len #b zero =
  if b then B.alloca zero len else ()

let lbuffer_or_unit_malloc #a #len #b r init =
  if b then B.malloc r init len else ()

let lbuffer_or_unit_free #a #len #b buf =
  if b then B.free (lbuffer_or_unit_to_buffer buf) else ()

let lbuffer_or_unit_copy #a #len #b o i =
  if b then copy #MUT #a #len (lbuffer_or_unit_to_buffer o) (lbuffer_or_unit_to_buffer i)

let lbuffer_or_unit_malloc_copy #a #len #b r init i =
  if b then
    begin
    (**) let h0 = HST.get () in
    let o = B.malloc r init len in
    copy #MUT #a #len o (lbuffer_or_unit_to_buffer i);
    (**) let h2 = HST.get () in
    (**) B.(modifies_only_not_unused_in loc_none h0 h2);
    o
    end
  else ()

let sub_or_unit #a b input i len =    
  if b then B.sub input i len else ()
