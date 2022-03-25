module Impl.Noise.CipherState

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence

module BS = Lib.ByteSequence
module LB = Lib.Buffer
open Lib.Buffer
module BB = Lib.ByteBuffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Impl.Noise.Types

friend Spec.Noise.Base.Definitions

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Integers conversion *)
let uint64_from_buffer i =
  BB.uint_from_bytes_le #U64 #SEC i

let uint64_to_buffer o i =
  BB.uint_to_bytes_le #U64 #SEC o i

let index_0u64_to_bytes_le_ (#t : inttype{unsigned t}) (#l : secrecy_level) :
  Lemma(forall (i : nat{i < numbytes t}). S.index (BS.uint_to_bytes_le #t #l (uint #t #l 0)) i ==
          uint #U8 #l 0) =
  BS.index_uint_to_bytes_le #t #l (uint #t #l 0)

let uint64_from_zeros_eq_lem s =
  uint64_to_from_bytes_eq (u64 0);
  index_0u64_to_bytes_le_ #U64 #SEC;
  assert(s `S.equal` BS.uint_to_bytes_le (u64 0))

(*** Transition functions *)

let initialize_key_Some key st_k =
  update_sub (st_k <: aead_key_t) 0ul aead_key_vs key

let initialized_cipher_state_no_key_lem h st = ()

#push-options "--z3rlimit 50 --ifuel 1"
let encrypt_with_ad_with_key_m #nc csi aad_len aad plen p c st_k nonce =
  [@inline_let] let key : aead_key_t = st_k in
  iaead_encrypt csi key nonce aad_len aad plen p c
#pop-options

#push-options "--z3rlimit 50 --ifuel 1"
let decrypt_with_ad_with_key_m #nc csi aad_len aad plen p c st_k nonce =
  [@inline_let] let key : aead_key_t = st_k in
  iaead_decrypt #nc csi key nonce aad_len aad plen p c
#pop-options
