module Spec.Noise.XX.Test

open Spec.Noise
open Spec.Noise.Instances
open Spec.Noise.Utils

open FStar.All
module IO = FStar.IO
module List = FStar.List

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(*** XX handshake *)

(* is_priv = "60C6697351FF4AEC29CDBAABF2FBE3467CC254F81BE8E78D765A2E63339FC95A" *)
let is_priv_list = List.Tot.map u8_from_UInt8 [
  0x60uy;  0xC6uy;  0x69uy;  0x73uy;  0x51uy;  0xFFuy;  0x4Auy;  0xECuy;  0x29uy;  0xCDuy; 
  0xBAuy;  0xABuy;  0xF2uy;  0xFBuy;  0xE3uy;  0x46uy;  0x7Cuy;  0xC2uy;  0x54uy;  0xF8uy; 
  0x1Buy;  0xE8uy;  0xE7uy;  0x8Duy;  0x76uy;  0x5Auy;  0x2Euy;  0x63uy;  0x33uy;  0x9Fuy; 
  0xC9uy;  0x5Auy ]

let is_priv : lbytes 32 =
  assert_norm(FStar.List.length is_priv_list = 32);
  of_list is_priv_list

(* ie_priv = "60320DB73158A35A255D051758E95ED4ABB2CDC69BB454110E827441213DDC47" *)
let ie_priv_list = List.Tot.map u8_from_UInt8 [
  0x60uy;  0x32uy;  0x0Duy;  0xB7uy;  0x31uy;  0x58uy;  0xA3uy;  0x5Auy;  0x25uy;  0x5Duy; 
  0x05uy;  0x17uy;  0x58uy;  0xE9uy;  0x5Euy;  0xD4uy;  0xABuy;  0xB2uy;  0xCDuy;  0xC6uy; 
  0x9Buy;  0xB4uy;  0x54uy;  0x11uy;  0x0Euy;  0x82uy;  0x74uy;  0x41uy;  0x21uy;  0x3Duy; 
  0xDCuy;  0x47uy ]

let ie_priv : lbytes 32 =
  assert_norm(FStar.List.length ie_priv_list = 32);
  of_list ie_priv_list

(* rs_priv = "70E93EA141E1FC673E017E97EADC6B968F385C2AECB03BFB32AF3C54EC18DB5C" *)
let rs_priv_list = List.Tot.map u8_from_UInt8 [
  0x70uy;  0xE9uy;  0x3Euy;  0xA1uy;  0x41uy;  0xE1uy;  0xFCuy;  0x67uy;  0x3Euy;  0x01uy; 
  0x7Euy;  0x97uy;  0xEAuy;  0xDCuy;  0x6Buy;  0x96uy;  0x8Fuy;  0x38uy;  0x5Cuy;  0x2Auy; 
  0xECuy;  0xB0uy;  0x3Buy;  0xFBuy;  0x32uy;  0xAFuy;  0x3Cuy;  0x54uy;  0xECuy;  0x18uy; 
  0xDBuy;  0x5Cuy ]

let rs_priv : lbytes 32 =
  assert_norm(FStar.List.length rs_priv_list = 32);
  of_list rs_priv_list

(* re_priv = "001AFE43FBFAAA3AFB29D1E6053C7C9475D8BE6189F95CBBA8990F95B1EBF173" *)
let re_priv_list = List.Tot.map u8_from_UInt8 [
  0x00uy;  0x1Auy;  0xFEuy;  0x43uy;  0xFBuy;  0xFAuy;  0xAAuy;  0x3Auy;  0xFBuy;  0x29uy; 
  0xD1uy;  0xE6uy;  0x05uy;  0x3Cuy;  0x7Cuy;  0x94uy;  0x75uy;  0xD8uy;  0xBEuy;  0x61uy; 
  0x89uy;  0xF9uy;  0x5Cuy;  0xBBuy;  0xA8uy;  0x99uy;  0x0Fuy;  0x95uy;  0xB1uy;  0xEBuy; 
  0xF1uy;  0x73uy ]

let re_priv : lbytes 32 =
  assert_norm(FStar.List.length re_priv_list = 32);
  of_list re_priv_list

#push-options "--z3rlimit 50 --ifuel 1"
(* Perform the handshake and check that we get the same state at the end *)
let perform_XX_handshake_ (is ie rs re : keypair wgc) :
  ML (eresult (cipher_states_pair & cipher_states_pair)) =
  (* Initialize *)
  let ist = initialize_XX protocol_XX_prologue is ie in
  let rst = initialize_XX protocol_XX_prologue is ie in
  (* Create initiation *)
  match create_initiation_XX ist with
  | Fail e -> Fail e
  | Res (init_msg, ist1) ->
    (* Consume initiation *)
    if length init_msg > max_size_t then Fail Input_size else // TODO: we can prove than length msg <= max_size_t
    match consume_initiation_XX init_msg rst with
    | Fail e -> Fail e
    | Res (init_decrypt, rst1) ->
      if length init_decrypt > 0 then Fail Input_size else
      let _ = print_handshake_state "Initiation" ist1 in
      let _ = print_handshake_state "Initiation" rst1 in
      (* Create response 1 *)
      match create_response1_XX rst1 with
      | Fail e -> Fail e
      | Res (resp1, rst2) ->
      (* Consume response 1 *)
      if length resp1 > max_size_t then Fail Input_size else // TODO: prove that always ok
      match consume_response1_XX resp1 ist1 with
      | Fail e -> Fail e
      | Res (resp1_decrypt, ist2) ->
        if length resp1_decrypt > 0 then Fail Input_size else
        let _ = print_handshake_state "Response 1" ist2 in
        let _ = print_handshake_state "Response 1" rst2 in
        (* Create response 2 *)
        match create_response2_XX ist2 with
        | Fail e -> Fail e
        | Res (resp2, ist3) ->
        (* Consume response 2 *)
          if length resp2 > max_size_t then Fail Input_size else
          match consume_response2_XX resp2 rst2 with
          | Fail e -> Fail e
          | Res (resp2_decrypt, rst3) ->
            if length resp2_decrypt > 0 then Fail Input_size else
            let _ = print_handshake_state "Response 2" ist3 in
            let _ = print_handshake_state "Response 2" rst3 in
            (* Split and check that the states are the same *)
            let iciphers = split ist3.sym_state in
            let rciphers = split rst3.sym_state in
            (* Print *)
            let _ = IO.print_string "Initiator cipher state:\n" in
            let _ = print_cipher_states_pair iciphers in
            let _ = IO.print_string "Responder cipher state:\n" in
            let _ = print_cipher_states_pair rciphers in
            (* Compare *)
            let b1 = cipher_states_equal (fst iciphers) (fst rciphers) in
            let b2 = cipher_states_equal (snd iciphers) (snd rciphers) in
            if b1 && b2
            then Res (iciphers, (match rciphers with | k1, k2 -> k2, k1))
            else Fail DH // ad-hoc error code
#pop-options

let perform_XX_handshake (pis pie prs pre : private_key wgc) :
  ML (eresult (cipher_states_pair & cipher_states_pair)) =
  (* Generate the public static and ephemeral keys *)
  let ois = keypair_from_private pis in
  let oie = keypair_from_private pie in
  let ors = keypair_from_private prs in
  let ore = keypair_from_private pre in
  match ois, oie, ors, ore with
  | Some is, Some ie, Some rs, Some re ->
    perform_XX_handshake_ is ie rs re
  | _ -> Fail DH

(* Test the handshake protocol *)
#push-options "--ifuel 2"
let test_XX () : ML bool =
  IO.print_string "*** XX:\n";
  let res1 = perform_XX_handshake is_priv ie_priv rs_priv re_priv in
  let ret =
    match res1 with
    | Fail _ -> IO.print_string "[!] Tests failed\n"; false
    | Res _ -> IO.print_string "Tests succeeded\n"; true
  in
  print_separation ();
  ret
#pop-options

let test () : ML bool =
  test_XX ()
