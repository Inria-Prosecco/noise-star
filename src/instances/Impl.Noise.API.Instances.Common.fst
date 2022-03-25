/// This module provides common definitions used for the instantiations of
/// the Noise API

module Impl.Noise.API.Instances.Common
open Impl.Noise.Extraction
open Meta.Noise
open FStar.Tactics
open Spec.Noise.CryptoPrimitives
open Impl.Noise.CryptoPrimitives

module DH = Spec.Agile.DH
open Spec.Agile.DH

module AEAD = Spec.Agile.AEAD
open Spec.Agile.AEAD

module Hash = Spec.Agile.Hash
open Spec.Agile.Hash
module HMAC = Spec.Agile.HMAC
open Spec.Agile.HMAC
module HKDF = Spec.Agile.HKDF
open Spec.Agile.HKDF

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

module ImplCFields = Hacl.Impl.Curve25519.Fields.Core
module ImplPolyFields = Hacl.Impl.Poly1305.Fields
module ImplBlake2Core = Hacl.Impl.Blake2.Core

let dh_alg_to_field (a : dh_alg) : dh_field_spec a =
  match a with
  | DH_Curve25519 -> ImplCFields.M51

let aead_alg_to_field (a : aead_alg) : aead_field_spec a =
  match a with
  | AES256_GCM -> ()
  | CHACHA20_POLY1305 -> ImplPolyFields.M32

let hash_alg_to_field (a : Spec.Noise.CryptoPrimitives.hash_alg) : hash_field_spec a =
  match a with
  | SHA2_256 | SHA2_512 -> ()
  | Hash.Blake2S -> ImplBlake2Core.M32
  | Hash.Blake2B -> ImplBlake2Core.M32

inline_for_extraction noextract
let impls_params (c : config) : config_impls_params c =
  dh_alg_to_field (get_dh_alg c),
  aead_alg_to_field (get_aead_alg c),
  hash_alg_to_field (get_hash_alg c)

/// Some meta-processing functions
/// TODO: move

noextract
let normalize_messages_impl_list_ (dbg : bool) () : Tac unit =
  norm [
    zeta;
    iota;
    primops;
    delta_only [
    `%with_norm;
    (* Send messages *)
    `%Impl.Noise.API.DState.mk_send_message_impls;
    `%Impl.Noise.API.State.StateMachine.mk_send_message_impls;
    `%Impl.Noise.API.State.StateMachine.mk_send_message_impls_aux;
    `%Impl.Noise.API.State.StateMachine.mk_send_messagei_impl;
    `%Impl.Noise.RecursiveMessages.send_message_tokens_with_payload_m;
    (* Receive messages *)
    `%Impl.Noise.API.DState.mk_receive_message_impls;
    `%Impl.Noise.API.State.StateMachine.mk_receive_message_impls;
    `%Impl.Noise.API.State.StateMachine.mk_receive_message_impls_aux;
    `%Impl.Noise.API.State.StateMachine.mk_receive_messagei_impl;
    `%Impl.Noise.API.State.StateMachine.mk_receive_split_messagei_impls;
    `%Impl.Noise.API.State.StateMachine.mk_receive_no_split_messagei_impl;
    `%Impl.Noise.API.State.StateMachine.mk_receive_split_messagei_beg_impl;
    `%Impl.Noise.API.State.StateMachine.mk_receive_split_messagei_end_impl;
    `%Impl.Noise.API.State.StateMachine.mk_receive_split_messagei_end_impl_aux;
    `%Impl.Noise.RecursiveMessages.receive_message_tokens_with_payload_m;
    `%Impl.Noise.RecursiveMessages.receive_message_tokens_nout_with_payload_m;
  ]];
  norm [
    zeta_full;
    iota;
    primops;
    delta_only [
    `%Impl.Noise.RecursiveMessages.send_message_tokens_m;
    `%Impl.Noise.RecursiveMessages.receive_message_tokens_nout_m;
  ]];
  if dbg then dump "";
  trefl()

noextract
let normalize_messages_impl_list () : Tac unit =
  normalize_messages_impl_list_ false ()

noextract
let normalize_read_write_message_ (dbg : bool) (message_impls_lists: list string) () : Tac unit =
  let ids =
    List.Tot.append message_impls_lists
    [
    `%with_norm;
    `%Impl.Noise.API.DState.mk_state_t_handshake_write_rec;
    `%Impl.Noise.API.State.StateMachine.mk_state_t_handshake_write_rec;
    `%Impl.Noise.API.DState.mk_state_t_handshake_read_rec;
    `%Impl.Noise.API.State.StateMachine.mk_state_t_handshake_read_rec;
  ]
  in
  norm [
    zeta;
    iota;
    primops;
    delta_only ids;
  ];
  norm [
    zeta_full;
    iota;
    primops;
    delta_only [
    `%Impl.Noise.API.State.StateMachine.mk_state_t_handshake_writei_rec;
    `%Impl.Noise.API.State.StateMachine.mk_state_t_handshake_readi_rec;
    ]
  ];
  if dbg then dump "";
  trefl()

noextract
let normalize_read_write_message (message_impls_lists: list string) () : Tac unit =
  normalize_read_write_message_ false message_impls_lists ()
