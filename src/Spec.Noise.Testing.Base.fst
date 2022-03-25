module Spec.Noise.Testing.Base

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Spec.Noise.Patterns

open Spec.Noise.Utils

open FStar.All
module IO = FStar.IO

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

/// The following file defines testing utilities for the Noise patterns

let swap_pair (#a #b : Type) (p : a & b) : b & a =
  match p with x, y -> y, x

(* TODO: should be moved *)
let bytes_eq (b1 : bytes{length b1 <= max_size_t})
             (b2 : bytes{length b2 <= max_size_t}) :
  b:bool{b <==> b1 == b2} =
  if length b1 <> length b2 then false
  else lbytes_eq #(length b1) b1 b2

let string_of_error (e : error) : string =
  match e with
  | No_key          -> "No_key"
  | Already_key     -> "Already_key"
  | Input_size      -> "Input_size"
  | DH              -> "DH"
  | Decryption      -> "Decryption"
  | Saturated_nonce -> "Saturated_nonce"

type test_error = string

let tresult (a : Type) = result a test_error

noeq type message_test_vector (nc : config) = {
  payload : plain_message nc;
  ciphertext : c:bytes{length c <= max_size_t};
}

noeq type handshake_test_vector = {
  nc : config;
  pattern : wf_handshake_pattern;
  protocol_str : string; // The protocol name
  protocol_name : hashable nc; // The protocol name but interpreted as a sequence of bytes
  prologue : hashable nc;
  is : option (private_key nc);
  ie : option (private_key nc);
  rs : option (private_key nc);
  re : option (private_key nc);
  irs : option (public_key nc); (* initiator remote static - actually not used *)
  rrs : option (public_key nc); (* responder remote static - actually not used *)
  psk : option preshared_key;
  final_hash : hash nc;
  msgs : (msgs:list (message_test_vector nc){List.Tot.length msgs >= List.Tot.length pattern.messages});
}

type handshake_state_pair (nc : config) = handshake_state nc & handshake_state nc

let execute_premessage (nc : config) (hsk : wf_handshake_pattern)
                       (ir : bool) (is rs : handshake_state nc) :
  Tot (tresult (handshake_state_pair nc)) =  
  match (if ir then hsk.premessage_ir else hsk.premessage_ri) with
  | None -> Res (is, rs)
  | Some pre ->
    match csend_premessage nc hsk ir is with
    | Fail _ -> Fail ("send_premessage failed (ir:" ^ (string_of_bool ir) ^ ")")
    | Res (msg1, is1) ->
      if length msg1 > max_size_t then Fail "send_premessage: premessage too long" else
      match creceive_premessage nc hsk ir msg1 rs with
      | Fail _ -> Fail ("receive_premessage failed (ir:" ^ (string_of_bool ir) ^ ")")
      | Res rs1 ->
        Res (is1, rs1)

/// Note that in the case of handshame patterns with only one message, everything
/// goes one way.
#push-options "--fuel 1"
let rec execute_transport_messages (nc : config) (i : nat) (one_way : bool)
                                   (vectors : list (message_test_vector nc))
                                   (is rs : cipher_states_pair) :
  Tot (tresult (cipher_states_pair & cipher_states_pair))
  (decreases vectors) =
  match vectors with
  | [] -> Res (is, rs)
  | v1 :: vectors1 ->
    match encrypt_with_ad nc Seq.empty v1.payload (fst is) with
    | Fail e ->
      Fail ("transport message #" ^ (string_of_int i) ^ ": encrypt_with_ad failed: "
            ^ (string_of_error e))
    | Res (cipher, ics1) ->
      (* Check the cipher text *)
      if length cipher > max_size_t then Fail ("length cipher > max_size_t")
      else if not (bytes_eq cipher v1.ciphertext)
      then Fail ("transport message #" ^ (string_of_int i) ^ ": encrypt_with_ad: " ^
                 "the ciphertext doesn't match the reference") else
      match decrypt_with_ad nc Seq.empty cipher (fst rs) with
      | Fail e ->
        Fail ("transport message #" ^ (string_of_int i) ^ ": decrypt_with_ad failed: "
              ^ (string_of_error e))
      | Res (plain, rcs1) ->
        if length plain > max_size_t then Fail ("length plain > max_size_t")
        else if not (bytes_eq plain v1.payload)
        then Fail ("transport_message #" ^ (string_of_int i) ^
                   ": the deciphered ciphertext doesn't match the original plaintext")
        else
        let is1 = (ics1, snd is) in
        let rs1 = (rcs1, snd rs) in
        (* Take care of the order of the different states: if it is not one-way,
         * we invert the cipher states AND we invert the pairs *)
        let is2, rs2 = if one_way then is1, rs1 else swap_pair rs1, swap_pair is1 in
        match execute_transport_messages nc (i+1) one_way vectors1 (**) is2 rs2 (**) with
        | Fail e -> Fail e
        | Res (is3, rs3) ->
          (* Re-invert to retrieve the original order *)
          let is4, rs4 = if one_way then is3, rs3 else swap_pair rs3, swap_pair is3 in
          Res (swap_pair is4, swap_pair rs4)
#pop-options

/// Note that this function returns the pair of states in the order (init, resp).
/// You need to pay attention to that when chaining it with [execute_transport_messages]
#push-options "--fuel 1"
let rec execute_messages_aux (nc : config) (hsk : handshake_pattern)
                             (i : nat{i <= List.length hsk.messages})
                             (vectors : list (message_test_vector nc){
                               List.length vectors + i == List.length hsk.messages})
                             (is rs : handshake_state nc) :
  Tot (tresult (handshake_state_pair nc))
  (decreases vectors) =
  match vectors with
  | [] -> Res (is, rs)
  | v1::vectors1 ->
    (**) assert(List.length vectors = 1 + List.length vectors1);
    match csend_message nc hsk i v1.payload is with
    | Fail e ->
      Fail ("csend_message #" ^ (string_of_int i) ^ " failed: " ^ (string_of_error e))
    | Res (cipher, is1) ->
      if length cipher > max_size_t then Fail "csend_message: message is too long" else
      (* Check the ciphertext *)
      if not (bytes_eq cipher v1.ciphertext)
      then Fail "csend_message: wrong ciphertext" else
      match creceive_message nc hsk i cipher rs with
      | Fail e ->
        Fail ("creceive_message #" ^ (string_of_int i) ^ " failed: " ^ (string_of_error e))
      | Res (rem, rs1) ->
        if not (bytes_eq rem v1.payload)
        then Fail "creceive_message did not return the original payload" else
        match execute_messages_aux nc hsk (i+1) vectors1 (**) rs1 is1 (**) with
        | Fail e -> Fail e
        | Res (**) (rs2, is2) (**) ->
          Res (**) (is2, rs2) (**)
#pop-options

let execute_messages (v : handshake_test_vector)
                     (is rs : handshake_state v.nc) :
  Tot (tresult (cipher_states_pair & cipher_states_pair)) =
  (* There may be more message test vectors than there are messages in the
   * handshake pattern: in this case we use the first vectors to execute the
   * pattern, then the remaining vectors for transport messages *)
  let num_msgs = List.length v.pattern.messages in
  let hsk_msgs, transport_msgs = List.Tot.splitAt num_msgs v.msgs in
  (**) FStar.List.Pure.Properties.splitAt_length num_msgs v.msgs;
  (**) assert(List.length hsk_msgs == num_msgs);
  match execute_messages_aux v.nc v.pattern 0 hsk_msgs is rs with
  | Fail e -> Fail e
  | Res (is1, rs1) ->
    (* Check the hash *)
    if not (lbytes_eq #(hash_size v.nc) is1.sym_state.h v.final_hash)
       || not (lbytes_eq #(hash_size v.nc) rs1.sym_state.h v.final_hash)
    then Fail "execute_messages: wrong resulting hash" else
    let is2 = split is1.sym_state in
    let rs2 = split rs1.sym_state in
    (* We need to pay attention to the order in which we transmit the states
     * to [execute_transport_messages]. The next sender is the party which
     * received the last handshake message, at the condition that there are
     * at least two messages in the handshake pattern (otherwise all goes one
     * way). Note that we may also need to swap the cipher states in the cipher
     * states pair. *)
    let csp1, csp2, one_way =
      if num_msgs = 1 then is2, rs2, true
      else if is_even num_msgs then is2, rs2, false
      else swap_pair rs2, swap_pair is2, false in
    execute_transport_messages v.nc 0 one_way transport_msgs csp1 csp2

let execute_handshake (v : handshake_test_vector) :
  Tot (tresult (cipher_states_pair & cipher_states_pair)) =
  let is = keypair_from_opt_private v.is in
  let ie = keypair_from_opt_private v.ie in
  let rs = keypair_from_opt_private v.rs in
  let re = keypair_from_opt_private v.re in
  let is0 = initialize_handshake_state v.protocol_name v.prologue is ie None None v.psk in
  let rs0 = initialize_handshake_state v.protocol_name v.prologue rs re None None v.psk in
  match execute_premessage v.nc v.pattern true is0 rs0 with
  | Fail e -> Fail e
  | Res (is1, rs1) ->
    match execute_premessage v.nc v.pattern false (**) rs1 is1 (**) with
    | Fail e -> Fail e
    | Res (rs2, is2) ->
      match execute_messages v is2 rs2 with
      | Fail e -> Fail e
      | Res (is3, rs3) -> Res (is3, rs3)

#push-options "--fuel 1 --ifuel 1"
let rec execute_handshakes_aux (vl : list handshake_test_vector) (i : nat) : ML bool =
  match vl with
  | [] -> true
  | v :: vl' ->
    let r1 = execute_handshake v in
    begin match r1 with
    | Fail e ->
      IO.print_string ("[!] Handshake test #" ^ (string_of_int i) ^
                       " (" ^ v.protocol_str ^ ") failed: " ^ e ^ "\n")
    | Res _ ->
      IO.print_string ("Handshake test #" ^ (string_of_int i) ^
                       " (" ^ v.protocol_str ^ ") succeeded\n")
    end;
    let r2 = execute_handshakes_aux vl' (i+1) in
    Res? r1 && r2
#pop-options

let execute_handshakes (vl : list handshake_test_vector) : ML bool =
  let b = execute_handshakes_aux vl 0 in
  if b then IO.print_string "All tests succeeded!\n"
  else IO.print_string "[!] Some tests failed\n";
  b
