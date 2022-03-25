module Spec.Noise.Instances

open FStar.Mul

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.WellFormedness

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(** Configuration (Wireguard) *)
inline_for_extraction noextract
let wgc : config =
  Spec.Agile.DH.DH_Curve25519,
  Spec.Agile.AEAD.CHACHA20_POLY1305,
  Spec.Hash.Definitions.Blake2S

(** IKpsk2 pattern *)
(*
 * <- s
 * ---------------
 * -> e, es, s, ss, {t}
 * <- e, ee, se, psk {}
 *)

inline_for_extraction let timestamp_size : size_nat = 12
type timestamp = lbytes timestamp_size

(* protocol_IKpsk2_name = "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s" *)
let protocol_IKpsk2_name_list = List.Tot.map u8_from_UInt8 [
  0x4Euy;  0x6Fuy;  0x69uy;  0x73uy;  0x65uy;  0x5Fuy;  0x49uy;  0x4Buy;  0x70uy;  0x73uy; 
  0x6Buy;  0x32uy;  0x5Fuy;  0x32uy;  0x35uy;  0x35uy;  0x31uy;  0x39uy;  0x5Fuy;  0x43uy; 
  0x68uy;  0x61uy;  0x43uy;  0x68uy;  0x61uy;  0x50uy;  0x6Fuy;  0x6Cuy;  0x79uy;  0x5Fuy; 
  0x42uy;  0x4Cuy;  0x41uy;  0x4Buy;  0x45uy;  0x32uy;  0x73uy ]

irreducible let protocol_IKpsk2_name : lbytes 37 =
  assert_norm(FStar.List.length protocol_IKpsk2_name_list = 37);
  of_list protocol_IKpsk2_name_list

(* protocol_IKpsk2_prologue = "WireGuard v1 zx2c4 Jason@zx2c4.com" *)
let protocol_IKpsk2_prologue_list = List.Tot.map u8_from_UInt8 [
  0x57uy;  0x69uy;  0x72uy;  0x65uy;  0x47uy;  0x75uy;  0x61uy;  0x72uy;  0x64uy;  0x20uy; 
  0x76uy;  0x31uy;  0x20uy;  0x7Auy;  0x78uy;  0x32uy;  0x63uy;  0x34uy;  0x20uy;  0x4Auy; 
  0x61uy;  0x73uy;  0x6Fuy;  0x6Euy;  0x40uy;  0x7Auy;  0x78uy;  0x32uy;  0x63uy;  0x34uy; 
  0x2Euy;  0x63uy;  0x6Fuy;  0x6Duy ]

irreducible let protocol_IKpsk2_prologue : lbytes 34 =
  assert_norm(FStar.List.length protocol_IKpsk2_prologue_list = 34);
  of_list protocol_IKpsk2_prologue_list

let pattern_IKpsk2 =
  wf_hs "IKpsk2" [
    ~<<~ [PS];
    ~>~ [E; ES; S; SS];
    ~<~ [E; EE; SE; PSK]
  ]

let _ : squash(List.Tot.length pattern_IKpsk2.messages == 2) =
  assert_norm(List.Tot.length pattern_IKpsk2.messages == 2)

val initialize_IKpsk2 : hashable wgc -> keypair wgc -> keypair wgc ->
                        Tot (handshake_state wgc)
let initialize_IKpsk2 prologue s e =
  initialize protocol_IKpsk2_name prologue (Some s) (Some e) None

val send_premessage_IKpsk2 : handshake_state wgc ->
                             Tot (peresult (bytes & (handshake_state wgc)))
let send_premessage_IKpsk2 =
  csend_premessage wgc pattern_IKpsk2 false

val receive_premessage_IKpsk2 : bytes -> handshake_state wgc ->
                                Tot (peresult (handshake_state wgc))
let receive_premessage_IKpsk2 =
  creceive_premessage wgc pattern_IKpsk2 false

val create_initiation_IKpsk2 : timestamp -> handshake_state wgc ->
                               Tot (eresult (bytes & (handshake_state wgc)))
let create_initiation_IKpsk2 = csend_message wgc pattern_IKpsk2 0

val consume_initiation_IKpsk2 : bytes -> handshake_state wgc ->
                                Tot (eresult ((hashable wgc) & (handshake_state wgc)))
let consume_initiation_IKpsk2 = creceive_message wgc pattern_IKpsk2 0

val create_response_IKpsk2 : handshake_state wgc ->
                             Tot (eresult (bytes & (handshake_state wgc)))
let create_response_IKpsk2 = csend_message wgc pattern_IKpsk2 1 lbytes_empty

val consume_response_IKpsk2 : bytes -> handshake_state wgc ->
                              Tot (eresult ((hashable wgc) & (handshake_state wgc)))
let consume_response_IKpsk2 = creceive_message wgc pattern_IKpsk2 1

(** XX pattern *)
(*
 * -> e
 * <- e, ee, s, es
 * -> s, se
 *)

(* protocol_XX_name = "Noise_XX_25519_ChaChaPoly_BLAKE2s" *)
let protocol_XX_name_list = List.Tot.map u8_from_UInt8 [
  0x4Euy;  0x6Fuy;  0x69uy;  0x73uy;  0x65uy;  0x5Fuy;  0x58uy;  0x58uy;  0x5Fuy;  0x32uy; 
  0x35uy;  0x35uy;  0x31uy;  0x39uy;  0x5Fuy;  0x43uy;  0x68uy;  0x61uy;  0x43uy;  0x68uy; 
  0x61uy;  0x50uy;  0x6Fuy;  0x6Cuy;  0x79uy;  0x5Fuy;  0x42uy;  0x4Cuy;  0x41uy;  0x4Buy; 
  0x45uy;  0x32uy;  0x73uy ]

let protocol_XX_name : lbytes 33 =
  assert_norm(FStar.List.length protocol_XX_name_list = 33);
  of_list protocol_XX_name_list

(* protocol_XX_prologue = "" *)
let protocol_XX_prologue_list = List.Tot.map u8_from_UInt8 []

let protocol_XX_prologue : lbytes 0 =
  assert_norm(FStar.List.length protocol_XX_prologue_list = 0);
  of_list protocol_XX_prologue_list

let pattern_XX =
  wf_hs "XX" [
    ~>~ [E];
    ~<~ [E; EE; S; ES];
    ~>~ [S; SE]
  ]

let _ : squash(List.Tot.length pattern_XX.messages == 3) =
  assert_norm(List.Tot.length pattern_XX.messages == 3)

val initialize_XX : hashable wgc -> keypair wgc -> keypair wgc ->
                    Tot (handshake_state wgc)
let initialize_XX prologue s e =
  initialize protocol_XX_name prologue (Some s) (Some e) None

val create_initiation_XX : handshake_state wgc ->
                           Tot (eresult (bytes & (handshake_state wgc)))
let create_initiation_XX = csend_message wgc pattern_XX 0 lbytes_empty

val consume_initiation_XX : bytes -> handshake_state wgc ->
                            Tot (eresult ((hashable wgc) & (handshake_state wgc)))
let consume_initiation_XX = creceive_message wgc pattern_XX 0

val create_response1_XX : handshake_state wgc ->
                          Tot (eresult (bytes & (handshake_state wgc)))
let create_response1_XX = csend_message wgc pattern_XX 1 lbytes_empty

val consume_response1_XX : bytes -> handshake_state wgc ->
                           Tot (eresult ((hashable wgc) & (handshake_state wgc)))
let consume_response1_XX = creceive_message wgc pattern_XX 1

val create_response2_XX : handshake_state wgc ->
                          Tot (eresult (bytes & (handshake_state wgc)))
let create_response2_XX = csend_message wgc pattern_XX 2 lbytes_empty

val consume_response2_XX : bytes -> handshake_state wgc ->
                           Tot (eresult ((hashable wgc) & (handshake_state wgc)))
let consume_response2_XX = creceive_message wgc pattern_XX 2
