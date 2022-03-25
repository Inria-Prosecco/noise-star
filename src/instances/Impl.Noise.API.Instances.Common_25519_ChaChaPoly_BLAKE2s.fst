/// This module defines a configuration and specializes the protocol functions for
/// this configuration.

module Impl.Noise.API.Instances.Common_25519_ChaChaPoly_BLAKE2s
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

module T = FStar.Tactics
open Impl.Noise.API.Instances.Common

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let nc : config = DH_Curve25519, CHACHA20_POLY1305, Hash.Blake2S

[@@ T.postprocess_with (fun () -> T.norm [delta; zeta; iota; primops]; T.trefl())]
inline_for_extraction noextract
let impls_params : config_impls_params nc = impls_params nc

%splice[dh_secret_to_public; dh; aead_encrypt; aead_decrypt; hash; aead_encrypt; aead_decrypt; ssdhi; inc]
(let d, _, _ = generate_config_declarations true impls_params default_extract_decls_params "inc" in d)
