module Spec.Noise.IKpsk2.Test

open Spec.Noise
open Spec.Noise.Instances
open Spec.Noise.Testing
open Spec.Noise.Utils

open FStar.All
module IO = FStar.IO
module List = FStar.List

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(*** IKpsk2 handshake *)

noeq type handshake_result (nc : config) = {
  i_fhash : hash nc;
  i_fck : chaining_key nc;
  r_fhash : hash nc;
  r_fck : chaining_key nc;
  i_send_key : option aead_key;
  i_recv_key : option aead_key;
  r_send_key : option aead_key;
  r_recv_key : option aead_key;
}

let create_handshake_result
  (#nc : config)
  (i_fhash : hash nc)
  (i_fck : chaining_key nc)
  (r_fhash : hash nc)
  (r_fck : chaining_key nc)
  (i_send_key : option aead_key)
  (i_recv_key : option aead_key)
  (r_send_key : option aead_key)
  (r_recv_key : option aead_key) :
  Tot (handshake_result nc) =
  {
    i_fhash = i_fhash;
    i_fck = i_fck;
    r_fhash = r_fhash;
    r_fck = r_fck;
    i_send_key = i_send_key;
    r_send_key = r_send_key;
    i_recv_key = i_recv_key;
    r_recv_key = r_recv_key;
  }

let create_handshake_result_from_ref
  (#nc : config)
  (fhash : hash nc)
  (fck : chaining_key nc)
  (i_send_key : aead_key)
  (i_recv_key : aead_key) :
  Tot (handshake_result nc) =
  {
    i_fhash = fhash;
    i_fck = fck;
    r_fhash = fhash;
    r_fck = fck;
    i_send_key = Some i_send_key;
    r_send_key = Some i_recv_key;
    i_recv_key = Some i_recv_key;
    r_recv_key = Some i_send_key;
  }

let create_handshake_result_from_states
  (#nc : config)
  (ist rst : handshake_state nc)
  (iciphers rciphers : cipher_states_pair) :
  Tot (handshake_result nc) =
  {
    i_fhash = ist.sym_state.h;
    i_fck = rst.sym_state.ck;
    r_fhash = ist.sym_state.h;
    r_fck = rst.sym_state.ck;
    i_send_key = (fst iciphers).k;
    r_send_key = (fst rciphers).k;
    i_recv_key = (snd iciphers).k;
    r_recv_key = (snd rciphers).k;
  }

let print_compare_handshake_results (#nc : config) (res exp : handshake_result nc) :
  ML bool =
  IO.print_string "*** Compare handshake results:\n";
  IO.print_string "** Initiator:\n";
  let b1 = print_compare_named_bytes "- Final hash" res.i_fhash exp.i_fhash in
  let b2 = print_compare_named_bytes "- Final chaining key" res.i_fck exp.i_fck in
  let b3 = print_compare_named_opt_bytes "- Sending key" res.i_send_key exp.i_send_key in
  let b4 = print_compare_named_opt_bytes "- Receiving key" res.i_recv_key exp.i_recv_key in
  IO.print_string "** Responder:\n";
  let b5 = print_compare_named_bytes "- Final hash" res.r_fhash exp.r_fhash in
  let b6 = print_compare_named_bytes "- Final chaining key" res.r_fck exp.r_fck in
  let b7 = print_compare_named_opt_bytes "- Sending key" res.r_send_key exp.r_send_key in
  let b8 = print_compare_named_opt_bytes "- Receiving key" res.r_recv_key exp.r_recv_key in
  IO.print_string "\n\n";
  b1 && b2 && b3 && b4


#push-options "--z3rlimit 50 --ifuel 1"
(* Perform the handshake and test that we get the same state at the end *)
let perform_IKpsk2_handshake_ (is ie rs re : keypair wgc)
                              (psk : preshared_key)
                              (ts : timestamp) :
  ML (eresult (handshake_result wgc)) =
  (* Initialize *)
  IO.print_string "-- Initialisation\n";
  let pist = initialize_IKpsk2 protocol_IKpsk2_prologue is ie in
  let prst = initialize_IKpsk2 protocol_IKpsk2_prologue rs re in
  (* Exchange the premessage *)
  let prres = send_premessage_IKpsk2 prst in
  match prres with
  | Fail e -> Fail DH // ad-hoc error
  | Res (pmsg, rst0) ->
    if length pmsg > max_size_t then Fail Input_size else
    let pires = receive_premessage_IKpsk2 pmsg pist in
    match pires with
    | Fail e -> Fail DH // ad-hoc error
    | Res ist0 ->
    (* Set the preshared keys at the beginning *)
    let ist = Spec.Noise.Base.set_psk psk ist0 in
    let rst = Spec.Noise.Base.set_psk psk rst0 in
    (* Create initiation *)
    IO.print_string "-- Create initiation\n";
    match create_initiation_IKpsk2 ts ist with
    | Fail e  -> Fail e
    | Res (msg, ist1) ->
      (* Consume initiation *)
      IO.print_string "-- Consume initiation\n";
      if length msg > max_size_t then Fail Input_size else
      match consume_initiation_IKpsk2 msg rst with
      | Fail e -> Fail e
      | Res (ts', rst1) ->
        if not (length ts' = length ts) then Fail Input_size else
        (* TODO: check timestamp *)
        (* Create response *)
        let _ = IO.print_string "-- Create response\n" in
        match create_response_IKpsk2 rst1 with
        | Fail e -> Fail e
        | Res (response, rst2) ->
          (* Consume response *)
          IO.print_string "-- Consume response\n";
          if length response > max_size_t then Fail Input_size else
          match consume_response_IKpsk2 response ist1 with
          | Fail e -> Fail e
          | Res (eps, ist2) ->
            IO.print_string "-- Split\n";
            if length eps > 0 then Fail Input_size else
            (* Split and check that the states are the same *)
            let iciphers = split ist2.sym_state in
            let rciphers = split rst2.sym_state in
            (* Print *)
            let _ = IO.print_string "Initiator cipher state:\n" in
            let _ = print_cipher_states_pair iciphers in
            let _ = IO.print_string "Responder cipher state:\n" in
            let _ = print_cipher_states_pair rciphers in
            (* Compare *)
            let b1 = cipher_states_equal (fst iciphers) (fst rciphers) in
            let b2 = cipher_states_equal (snd iciphers) (snd rciphers) in
            if b1 && b2
            then
              let rciphers_swaped = match rciphers with | k1, k2 -> k2, k1 in
              let res = create_handshake_result_from_states ist2 rst2 iciphers rciphers_swaped in
              Res res
            else Fail DH // this kind of failure is not taken into account in this structure
#pop-options

let perform_IKpsk2_handshake (pis pie prs pre : private_key wgc)
                             (psk : preshared_key)
                             (ts : timestamp) :
  ML (eresult (handshake_result wgc)) =
  (* Generate the public static and ephemeral keys *)
  IO.print_string "-- Public keys computation\n";
  let ois = keypair_from_private pis in
  let oie = keypair_from_private pie in
  let ors = keypair_from_private prs in
  let ore = keypair_from_private pre in
  match ois, oie, ors, ore with
  | Some is, Some ie, Some rs, Some re ->
    perform_IKpsk2_handshake_ is ie rs re psk ts
  | _ -> Fail DH

(* hsk_test1_ispriv = "60C6697351FF4AEC29CDBAABF2FBE3467CC254F81BE8E78D765A2E63339FC95A" *)
let hsk_test1_ispriv_list = List.Tot.map u8_from_UInt8 [
  0x60uy;  0xC6uy;  0x69uy;  0x73uy;  0x51uy;  0xFFuy;  0x4Auy;  0xECuy;  0x29uy;  0xCDuy; 
  0xBAuy;  0xABuy;  0xF2uy;  0xFBuy;  0xE3uy;  0x46uy;  0x7Cuy;  0xC2uy;  0x54uy;  0xF8uy; 
  0x1Buy;  0xE8uy;  0xE7uy;  0x8Duy;  0x76uy;  0x5Auy;  0x2Euy;  0x63uy;  0x33uy;  0x9Fuy; 
  0xC9uy;  0x5Auy ]

let hsk_test1_ispriv : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_ispriv_list = 32);
  of_list hsk_test1_ispriv_list

(* hsk_test1_iepriv = "70E93EA141E1FC673E017E97EADC6B968F385C2AECB03BFB32AF3C54EC18DB5C" *)
let hsk_test1_iepriv_list = List.Tot.map u8_from_UInt8 [
  0x70uy;  0xE9uy;  0x3Euy;  0xA1uy;  0x41uy;  0xE1uy;  0xFCuy;  0x67uy;  0x3Euy;  0x01uy; 
  0x7Euy;  0x97uy;  0xEAuy;  0xDCuy;  0x6Buy;  0x96uy;  0x8Fuy;  0x38uy;  0x5Cuy;  0x2Auy; 
  0xECuy;  0xB0uy;  0x3Buy;  0xFBuy;  0x32uy;  0xAFuy;  0x3Cuy;  0x54uy;  0xECuy;  0x18uy; 
  0xDBuy;  0x5Cuy ]

let hsk_test1_iepriv : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_iepriv_list = 32);
  of_list hsk_test1_iepriv_list

(* hsk_test1_rspriv = "60320DB73158A35A255D051758E95ED4ABB2CDC69BB454110E827441213DDC47" *)
let hsk_test1_rspriv_list = List.Tot.map u8_from_UInt8 [
  0x60uy;  0x32uy;  0x0Duy;  0xB7uy;  0x31uy;  0x58uy;  0xA3uy;  0x5Auy;  0x25uy;  0x5Duy; 
  0x05uy;  0x17uy;  0x58uy;  0xE9uy;  0x5Euy;  0xD4uy;  0xABuy;  0xB2uy;  0xCDuy;  0xC6uy; 
  0x9Buy;  0xB4uy;  0x54uy;  0x11uy;  0x0Euy;  0x82uy;  0x74uy;  0x41uy;  0x21uy;  0x3Duy; 
  0xDCuy;  0x47uy ]

let hsk_test1_rspriv : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_rspriv_list = 32);
  of_list hsk_test1_rspriv_list

(* hsk_test1_repriv = "001AFE43FBFAAA3AFB29D1E6053C7C9475D8BE6189F95CBBA8990F95B1EBF173" *)
let hsk_test1_repriv_list = List.Tot.map u8_from_UInt8 [
  0x00uy;  0x1Auy;  0xFEuy;  0x43uy;  0xFBuy;  0xFAuy;  0xAAuy;  0x3Auy;  0xFBuy;  0x29uy; 
  0xD1uy;  0xE6uy;  0x05uy;  0x3Cuy;  0x7Cuy;  0x94uy;  0x75uy;  0xD8uy;  0xBEuy;  0x61uy; 
  0x89uy;  0xF9uy;  0x5Cuy;  0xBBuy;  0xA8uy;  0x99uy;  0x0Fuy;  0x95uy;  0xB1uy;  0xEBuy; 
  0xF1uy;  0x73uy ]

let hsk_test1_repriv : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_repriv_list = 32);
  of_list hsk_test1_repriv_list

(* hsk_test1_psk = "0000000000000000000000000000000000000000000000000000000000000000" *)
let hsk_test1_psk_list = List.Tot.map u8_from_UInt8 [
  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy; 
  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy; 
  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy;  0x00uy; 
  0x00uy;  0x00uy ]

let hsk_test1_psk : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_psk_list = 32);
  of_list hsk_test1_psk_list

(* hsk_test1_i_sending_key = "6A05292E1F636EF2EC96E758BD89B3D5A840FB2FCCD4BBD672C72EE60C37095A" *)
let hsk_test1_i_sending_key_list = List.Tot.map u8_from_UInt8 [
  0x6Auy;  0x05uy;  0x29uy;  0x2Euy;  0x1Fuy;  0x63uy;  0x6Euy;  0xF2uy;  0xECuy;  0x96uy; 
  0xE7uy;  0x58uy;  0xBDuy;  0x89uy;  0xB3uy;  0xD5uy;  0xA8uy;  0x40uy;  0xFBuy;  0x2Fuy; 
  0xCCuy;  0xD4uy;  0xBBuy;  0xD6uy;  0x72uy;  0xC7uy;  0x2Euy;  0xE6uy;  0x0Cuy;  0x37uy; 
  0x09uy;  0x5Auy ]

let hsk_test1_i_sending_key : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_i_sending_key_list = 32);
  of_list hsk_test1_i_sending_key_list

(* hsk_test1_i_receiving_key = "15E664F84EF940CE55898942941930AE752CA74F43C4010BC56E78D98D2622A1" *)
let hsk_test1_i_receiving_key_list = List.Tot.map u8_from_UInt8 [
  0x15uy;  0xE6uy;  0x64uy;  0xF8uy;  0x4Euy;  0xF9uy;  0x40uy;  0xCEuy;  0x55uy;  0x89uy; 
  0x89uy;  0x42uy;  0x94uy;  0x19uy;  0x30uy;  0xAEuy;  0x75uy;  0x2Cuy;  0xA7uy;  0x4Fuy; 
  0x43uy;  0xC4uy;  0x01uy;  0x0Buy;  0xC5uy;  0x6Euy;  0x78uy;  0xD9uy;  0x8Duy;  0x26uy; 
  0x22uy;  0xA1uy ]

let hsk_test1_i_receiving_key : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_i_receiving_key_list = 32);
  of_list hsk_test1_i_receiving_key_list

(* hsk_test1_final_hash = "9186116A74D8CF2690F6130A032A4AB2306558B9726B4AAC8DE7A9EF3D02E88C" *)
let hsk_test1_final_hash_list = List.Tot.map u8_from_UInt8 [
  0x91uy;  0x86uy;  0x11uy;  0x6Auy;  0x74uy;  0xD8uy;  0xCFuy;  0x26uy;  0x90uy;  0xF6uy; 
  0x13uy;  0x0Auy;  0x03uy;  0x2Auy;  0x4Auy;  0xB2uy;  0x30uy;  0x65uy;  0x58uy;  0xB9uy; 
  0x72uy;  0x6Buy;  0x4Auy;  0xACuy;  0x8Duy;  0xE7uy;  0xA9uy;  0xEFuy;  0x3Duy;  0x02uy; 
  0xE8uy;  0x8Cuy ]

let hsk_test1_final_hash : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_final_hash_list = 32);
  of_list hsk_test1_final_hash_list

(* hsk_test1_final_ck = "871BAB0A31B471AA3FB01F1166C4A8F73FD8FFFD4E3AF4307B4AABF72BE90707" *)
let hsk_test1_final_ck_list = List.Tot.map u8_from_UInt8 [
  0x87uy;  0x1Buy;  0xABuy;  0x0Auy;  0x31uy;  0xB4uy;  0x71uy;  0xAAuy;  0x3Fuy;  0xB0uy; 
  0x1Fuy;  0x11uy;  0x66uy;  0xC4uy;  0xA8uy;  0xF7uy;  0x3Fuy;  0xD8uy;  0xFFuy;  0xFDuy; 
  0x4Euy;  0x3Auy;  0xF4uy;  0x30uy;  0x7Buy;  0x4Auy;  0xABuy;  0xF7uy;  0x2Buy;  0xE9uy; 
  0x07uy;  0x07uy ]

let hsk_test1_final_ck : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_final_ck_list = 32);
  of_list hsk_test1_final_ck_list

(* Test the handshake protocol *)
#push-options "--ifuel 2"
let test_IKpsk2 () : ML bool =
  IO.print_string "*** IKpsk2:\n";
  let psk1 = create preshared_key_size (u8 0) in
  let ts1 = create timestamp_size (u8 0) in
  let res1 = perform_IKpsk2_handshake hsk_test1_ispriv hsk_test1_iepriv
                                      hsk_test1_rspriv hsk_test1_repriv psk1 ts1 in
  match res1 with
  | Fail _ -> IO.print_string "[!] Tests failed\n"; false
  | Res hsk_result ->
    let hsk_expected = create_handshake_result_from_ref hsk_test1_final_hash
                                                        hsk_test1_final_ck
                                                        hsk_test1_i_sending_key
                                                        hsk_test1_i_receiving_key
    in
    print_compare_handshake_results hsk_result hsk_expected
#pop-options

(*** Generic functions *)

(* hsk_test1_rspub = "04EF0E0255A826CDE15A283CD7A1DB51495C9E8D61C7EAC737AE8919A99DB86E" *)
let hsk_test1_rspub_list = List.Tot.map u8_from_UInt8 [
  0x04uy;  0xEFuy;  0x0Euy;  0x02uy;  0x55uy;  0xA8uy;  0x26uy;  0xCDuy;  0xE1uy;  0x5Auy; 
  0x28uy;  0x3Cuy;  0xD7uy;  0xA1uy;  0xDBuy;  0x51uy;  0x49uy;  0x5Cuy;  0x9Euy;  0x8Duy; 
  0x61uy;  0xC7uy;  0xEAuy;  0xC7uy;  0x37uy;  0xAEuy;  0x89uy;  0x19uy;  0xA9uy;  0x9Duy; 
  0xB8uy;  0x6Euy ]

irreducible let hsk_test1_rspub : lbytes 32 =
  assert_norm(FStar.List.length hsk_test1_rspub_list = 32);
  of_list hsk_test1_rspub_list


(* hsk_test1_init_msg = "382B3A36604BDFF54287CCA66F5EE4521A6E204D93F143236BAB9B66BF4F7E6F1965FC6018F10C2ECE6829B4EB30E8B8DFB758B774A62AF4D0BDDAC4E985AABCF971941682C2FCD176B57FD44F45EFF6D920121527846F98ECC217008557C8BBE60D22CBB7A85F8E247028F4" *)
let hsk_test1_init_msg_list = List.Tot.map u8_from_UInt8 [
  0x38uy;  0x2Buy;  0x3Auy;  0x36uy;  0x60uy;  0x4Buy;  0xDFuy;  0xF5uy;  0x42uy;  0x87uy; 
  0xCCuy;  0xA6uy;  0x6Fuy;  0x5Euy;  0xE4uy;  0x52uy;  0x1Auy;  0x6Euy;  0x20uy;  0x4Duy; 
  0x93uy;  0xF1uy;  0x43uy;  0x23uy;  0x6Buy;  0xABuy;  0x9Buy;  0x66uy;  0xBFuy;  0x4Fuy; 
  0x7Euy;  0x6Fuy;  0x19uy;  0x65uy;  0xFCuy;  0x60uy;  0x18uy;  0xF1uy;  0x0Cuy;  0x2Euy; 
  0xCEuy;  0x68uy;  0x29uy;  0xB4uy;  0xEBuy;  0x30uy;  0xE8uy;  0xB8uy;  0xDFuy;  0xB7uy; 
  0x58uy;  0xB7uy;  0x74uy;  0xA6uy;  0x2Auy;  0xF4uy;  0xD0uy;  0xBDuy;  0xDAuy;  0xC4uy; 
  0xE9uy;  0x85uy;  0xAAuy;  0xBCuy;  0xF9uy;  0x71uy;  0x94uy;  0x16uy;  0x82uy;  0xC2uy; 
  0xFCuy;  0xD1uy;  0x76uy;  0xB5uy;  0x7Fuy;  0xD4uy;  0x4Fuy;  0x45uy;  0xEFuy;  0xF6uy; 
  0xD9uy;  0x20uy;  0x12uy;  0x15uy;  0x27uy;  0x84uy;  0x6Fuy;  0x98uy;  0xECuy;  0xC2uy; 
  0x17uy;  0x00uy;  0x85uy;  0x57uy;  0xC8uy;  0xBBuy;  0xE6uy;  0x0Duy;  0x22uy;  0xCBuy; 
  0xB7uy;  0xA8uy;  0x5Fuy;  0x8Euy;  0x24uy;  0x70uy;  0x28uy;  0xF4uy ]

let hsk_test1_init_msg : lbytes 108 =
  assert_norm(FStar.List.length hsk_test1_init_msg_list = 108);
  of_list hsk_test1_init_msg_list

(* hsk_test1_resp_msg = "04C4F17B0BCE6EBBD3ACD07BAE42D8A16E14A2D439B2D9778FCCB1D029DDE255212E51FA570457C5A0C46FBDCEFBEF5D" *)
let hsk_test1_resp_msg_list = List.Tot.map u8_from_UInt8 [
  0x04uy;  0xC4uy;  0xF1uy;  0x7Buy;  0x0Buy;  0xCEuy;  0x6Euy;  0xBBuy;  0xD3uy;  0xACuy; 
  0xD0uy;  0x7Buy;  0xAEuy;  0x42uy;  0xD8uy;  0xA1uy;  0x6Euy;  0x14uy;  0xA2uy;  0xD4uy; 
  0x39uy;  0xB2uy;  0xD9uy;  0x77uy;  0x8Fuy;  0xCCuy;  0xB1uy;  0xD0uy;  0x29uy;  0xDDuy; 
  0xE2uy;  0x55uy;  0x21uy;  0x2Euy;  0x51uy;  0xFAuy;  0x57uy;  0x04uy;  0x57uy;  0xC5uy; 
  0xA0uy;  0xC4uy;  0x6Fuy;  0xBDuy;  0xCEuy;  0xFBuy;  0xEFuy;  0x5Duy ]

let hsk_test1_resp_msg : lbytes 48 =
  assert_norm(FStar.List.length hsk_test1_resp_msg_list = 48);
  of_list hsk_test1_resp_msg_list

let hsk_test1_msgs_vectors : l:list (message_test_vector wgc){List.length l == 2} =
  let l = [
  { payload = create timestamp_size (u8 0);
    ciphertext = hsk_test1_init_msg; };
  { payload = Seq.empty;
    ciphertext = hsk_test1_resp_msg; } ] in
  assert_norm(List.length l == 2);
  l

let hsk_test1_test_vector : handshake_test_vector = {
  nc = wgc;
  pattern = pattern_IKpsk2;
  protocol_str = "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s";
  protocol_name = protocol_IKpsk2_name;
  prologue = protocol_IKpsk2_prologue;
  is = Some hsk_test1_ispriv;
  ie = Some hsk_test1_iepriv;
  rs = Some hsk_test1_rspriv;
  re = Some hsk_test1_repriv;
  irs = Some hsk_test1_rspub;
  rrs = None;
  psk = Some hsk_test1_psk;
  final_hash = hsk_test1_final_hash;
  msgs = hsk_test1_msgs_vectors;
}

#push-options "--ifuel 1"
let test_IKpsk2_gen () : ML bool =
  IO.print_string "*** IKpsk2 (gen):\n";
  let res1 = execute_handshake hsk_test1_test_vector in
  match res1 with
  | Fail e ->
    IO.print_string "[!] Tests failed:\n";
    IO.print_string e;
    IO.print_string "\n\n";
    false
  | Res _ -> IO.print_string "Test succeeded\n\n"; true
#pop-options


(*** All tests *)

let test () : ML bool =
  let b1 = test_IKpsk2 () in
  let b2 = test_IKpsk2_gen () in
  b1 && b2
