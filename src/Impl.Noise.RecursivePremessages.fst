module Impl.Noise.RecursivePremessages

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence
module SB = FStar.Seq.Base
module L = FStar.List
module Seq = FStar.Seq

module B = LowStar.Buffer
module BS = Lib.ByteSequence
module LB = Lib.Buffer
open Lib.Buffer
module BB = Lib.ByteBuffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Meta.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState

#set-options "--z3rlimit 100 --ifuel 1 --fuel 0"

/// This file contains the recursive functions we need to make visible to the user
/// in order to allow proper normalisation for the generated code.
(*** Premessages *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 2"
[@(strict_on_arguments [3])]
inline_for_extraction noextract
let rec send_premessage_tokens_m
    (#nc : iconfig)
    (send_premessage_token_impl : send_premessage_token_st nc) :
    send_premessage_tokens_st nc =
  fun smi pattern st out ->
  match pattern with
  | Nil ->
    (**) let h0 = HST.get () in
    (**) send_premessage_tokens_nil_lem (eval_handshake_state_m h0 st smi);
    success tokens_premessage_return_type
  | tk :: pattern' ->
    (**) let h0 = HST.get () in
    let tk_out = sub out 0ul (public_key_vs nc) in
    let out' = sub out (public_key_vs nc)
                   (with_norm (size (List.length pattern' * (public_key_vsv nc)))) in
    (**) assert(h0.[|out|] `S.equal` (S.concat h0.[|tk_out|] h0.[|out'|]));
    (**) let st0_v : Ghost.erased _ = eval_handshake_state_m h0 st smi in
    (**) send_premessage_tokens_unfold_lem tk pattern' st0_v;
    let _ = send_premessage_token_impl smi tk st tk_out in
    send_premessage_tokens_m send_premessage_token_impl smi pattern' st out'
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 2"
[@(strict_on_arguments [3])]
inline_for_extraction noextract
let rec receive_premessage_tokens_m
    (#nc : iconfig)
    (receive_premessage_token_impl : receive_premessage_token_st nc) :
    receive_premessage_tokens_st nc =
  fun smi pattern st input ->
  match pattern with
  | Nil ->
    (**) let h0 = HST.get () in
    (**) assert(Seq.equal h0.[|input|] Seq.empty);
    (**) receive_premessage_tokens_nil_lem (eval_handshake_state_m h0 st smi);
    success _
  | tk :: pattern' ->
    (**) let h0 = HST.get () in
    let tk_input = sub input 0ul (public_key_vs nc) in
    let input' = sub input (public_key_vs nc)
        (with_norm (size (List.length pattern' * (public_key_vsv nc)))) in
    (**) assert(h0.[|input|] `S.equal` (S.concat h0.[|tk_input|] h0.[|input'|]));
    (**) let st0_v : Ghost.erased _ = eval_handshake_state_m h0 st smi in
    (**) receive_premessage_tokens_unfold_lem tk pattern' h0.[|input|] st0_v;
    let _ = receive_premessage_token_impl smi tk st tk_input in
    (**) let smi' : Ghost.erased meta_info = receive_pretoken_update_smi tk smi in
    receive_premessage_tokens_m receive_premessage_token_impl smi' pattern' st input'
#pop-options
