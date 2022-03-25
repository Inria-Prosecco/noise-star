module Impl.Noise.CryptoPrimitives

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

module DH = Spec.Agile.DH

module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module KeyedHash = Spec.Blake2

/// We need to load some specific implementation modules to have access to
/// hardware preconditions and specification fields.
module ImplCFields = Hacl.Impl.Curve25519.Fields.Core
module ImplC64 = Hacl.Curve25519_64
module ImplPolyFields = Hacl.Impl.Poly1305.Fields
module ImplBlake2Core = Hacl.Impl.Blake2.Core

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

(*** DH *)

(**** Curve25519 *)
noextract
let dh_c25519_pre (fs : ImplCFields.field_spec) : Type0 =
  match fs with
  | ImplCFields.M51 -> True
  | ImplCFields.M64 -> ImplC64.p

inline_for_extraction noextract
val dh_sp_c25519 (fs : ImplCFields.field_spec) :
  dh_sp_st DH.DH_Curve25519 (dh_c25519_pre fs)

inline_for_extraction noextract
val dh_c25519 (fs : ImplCFields.field_spec) :
  dh_st DH.DH_Curve25519 (dh_c25519_pre fs)

inline_for_extraction noextract
let dh_field_spec (a : dh_alg) : Type0 =
  match a with
  | DH.DH_Curve25519 -> ImplCFields.field_spec

inline_for_extraction noextract
let dh_pre (#a : dh_alg) (fs : dh_field_spec a) : Type0 =
  match a with
  | DH.DH_Curve25519 -> dh_c25519_pre fs

inline_for_extraction noextract
let dh_sp_m (#a : dh_alg) (fs : dh_field_spec a) : dh_sp_st a (dh_pre fs) =
  match a with
  | DH.DH_Curve25519 -> dh_sp_c25519 fs

inline_for_extraction noextract
let dh_m (#a : dh_alg) (fs : dh_field_spec a) : dh_st a (dh_pre fs) =
  match a with
  | DH.DH_Curve25519 -> dh_c25519 fs

(*** AEAD *)
(**** AES GCM *)
noextract
let aead_aes_gcm_pre : Type0 =
  EverCrypt.AEAD.config_pre AEAD.AES256_GCM

inline_for_extraction noextract
val aead_encrypt_aes256_gcm : aead_encrypt_st AEAD.AES256_GCM aead_aes_gcm_pre

inline_for_extraction noextract
val aead_decrypt_aes256_gcm : aead_decrypt_st AEAD.AES256_GCM aead_aes_gcm_pre

(**** Chaha20Poly1305 *)
inline_for_extraction noextract
val aead_encrypt_cp (fs : ImplPolyFields.field_spec) :
  aead_encrypt_st AEAD.CHACHA20_POLY1305 True

inline_for_extraction noextract
val aead_decrypt_cp (fs : ImplPolyFields.field_spec) :
  aead_decrypt_st AEAD.CHACHA20_POLY1305 True

(**** General *)
inline_for_extraction noextract
let aead_field_spec (a : aead_alg) : Type0 =
  match a with
  | AEAD.AES256_GCM -> unit
  | AEAD.CHACHA20_POLY1305 -> ImplPolyFields.field_spec

inline_for_extraction noextract
let aead_pre (#a : aead_alg) (fs : aead_field_spec a) : Type0 =
  match a with
  | AEAD.AES256_GCM -> aead_aes_gcm_pre
  | AEAD.CHACHA20_POLY1305 -> True

inline_for_extraction noextract
let aead_encrypt_m (#a : aead_alg) (fs : aead_field_spec a) : aead_encrypt_st a (aead_pre fs) =
  match a with
  | AEAD.AES256_GCM -> aead_encrypt_aes256_gcm
  | AEAD.CHACHA20_POLY1305 -> aead_encrypt_cp fs

inline_for_extraction noextract
let aead_decrypt_m (#a : aead_alg) (fs : aead_field_spec a) : aead_decrypt_st a (aead_pre fs) =
  match a with
  | AEAD.AES256_GCM -> aead_decrypt_aes256_gcm
  | AEAD.CHACHA20_POLY1305 -> aead_decrypt_cp fs

(*** Hash *)
(**** SHA2 *)
inline_for_extraction noextract
val hash_sha2_256 : do_hash_st Hash.SHA2_256 True

inline_for_extraction noextract
val hash_sha2_512 : do_hash_st Hash.SHA2_512 True

inline_for_extraction noextract
val hash2_sha2_256 : do_hash2_st Hash.SHA2_256 True

inline_for_extraction noextract
val hash2_sha2_512 : do_hash2_st Hash.SHA2_512 True

inline_for_extraction noextract
val hmac_sha2_256 : hmac_st Hash.SHA2_256 True

inline_for_extraction noextract
val hmac_sha2_512 : hmac_st Hash.SHA2_512 True

(**** Blake2 *)
noextract
let blake2_field_is_valid (a : hash_alg) (m : ImplBlake2Core.m_spec) : bool =
  match a, m with
  | Hash.Blake2S, ImplBlake2Core.M32 | Hash.Blake2S, ImplBlake2Core.M128
  | Hash.Blake2B, ImplBlake2Core.M32 | Hash.Blake2B, ImplBlake2Core.M256 -> true
  | _ -> false

noextract
type valid_blake2_field (a : hash_alg) =
  m:ImplBlake2Core.m_spec{blake2_field_is_valid a m}

/// TODO: not sure here
noextract
let blake2_pre (m : ImplBlake2Core.m_spec) : Type0 =
  match m with
  | ImplBlake2Core.M32 -> True
  | ImplBlake2Core.M128 -> Vale.X64.CPU_Features_s.avx_enabled
  | ImplBlake2Core.M256 -> Vale.X64.CPU_Features_s.avx2_enabled

inline_for_extraction noextract
val hash_blake2 (a : hash_alg) (m : valid_blake2_field a) :
  do_hash_st a (blake2_pre m)

inline_for_extraction noextract
val hash2_blake2 (a : hash_alg) (m : valid_blake2_field a) :
  do_hash2_st a (blake2_pre m)

inline_for_extraction noextract
val hmac_blake2 (a : hash_alg) (m : valid_blake2_field a) :
  hmac_st a (blake2_pre m)

(**** General *)
inline_for_extraction noextract
let hash_field_spec (a : hash_alg) : Type0 =
  match a with
  | Hash.Blake2S | Hash.Blake2B -> valid_blake2_field a
  | _ -> unit

inline_for_extraction noextract
let hash_pre (#a : hash_alg) (fs : hash_field_spec a) : Type0 =
  match a with
  | Hash.Blake2S | Hash.Blake2B -> blake2_pre fs
  | _ -> True

inline_for_extraction noextract
let do_hash_m (#a : hash_alg) (fs : hash_field_spec a) : do_hash_st a (hash_pre fs) =
  match a with
  | Hash.SHA2_256 -> hash_sha2_256
  | Hash.SHA2_512 -> hash_sha2_512
  | _ -> hash_blake2 a fs

inline_for_extraction noextract
let do_hash2_m (#a : hash_alg) (fs : hash_field_spec a) : do_hash2_st a (hash_pre fs) =
  match a with
  | Hash.SHA2_256 -> hash2_sha2_256
  | Hash.SHA2_512 -> hash2_sha2_512
  | _ -> hash2_blake2 a fs

inline_for_extraction noextract
let hmac_m (#a : hash_alg) (fs : hash_field_spec a) : hmac_st a (hash_pre fs) =
  match a with
  | Hash.SHA2_256 -> hmac_sha2_256
  | Hash.SHA2_512 -> hmac_sha2_512
  | _ -> hmac_blake2 a fs
  
