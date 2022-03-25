(* TODO: I would like to change the name of the module (remove the 'Spec')
 * but then we need to create a special build rule in the Makefile, because
 * otherwise no .ml file is generated (and thus the tests can't be run). *)
module Spec.Noise.Utils

open Spec.Noise

open FStar.All
module IO = FStar.IO
module List = FStar.List

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

(* Utility functions for formatting *)
let print_separation () : ML unit = IO.print_string "==================\n\n"

(* Utility functions to print and compare *)
let print_bytes (k : bytes) : ML unit =
  List.iter (fun a -> IO.print_uint8_hex_pad (Lib.RawIntTypes.u8_to_UInt8 a)) (to_list k)

let print_named_bytes (s : string) (k : bytes) : ML unit =
  IO.print_string s;
  IO.print_string ": ";
  print_bytes k;
  IO.print_string "\n"

let print_opt_bytes (#n : size_nat) (ob : option (lbytes n)) : ML unit =
  match ob with
  | None -> IO.print_string "None"
  | Some b -> print_bytes b

let compare_bytes (#n : size_nat) (b1 b2 : lbytes n) : bool =
  lbytes_eq b1 b2

let compare_opt_bytes (#n : size_nat) (ob1 ob2 : option (lbytes n)) : bool =
  match ob1, ob2 with
  | None, None -> true
  | Some b1, Some b2 -> compare_bytes b1 b2
  | _ -> false

let print_compare_bytes (#n : size_nat) (result expected : lbytes n) : ML bool =
  let is_same  = compare_bytes result expected in
  IO.print_string "Result  : ";
  print_bytes result;
  IO.print_string "\nExpected: ";
  print_bytes expected;
  if is_same then IO.print_string "\nSucces: same values\n\n"
             else IO.print_string "\n[!] Failure: different values\n\n";
  is_same

let print_compare_opt_bytes (#n : size_nat) (result expected : option (lbytes n)) : ML bool =
  let is_same  = compare_opt_bytes result expected in
  IO.print_string "Result  : ";
  print_opt_bytes result;
  IO.print_string "\nExpected: ";
  print_opt_bytes expected;
  if is_same then IO.print_string "\nSucces: same values\n\n"
             else IO.print_string "\n[!] Failure: different values\n\n";
  is_same

let print_compare_named_bytes (#n : size_nat) (s : string) (result expected : lbytes n) : ML bool =
  let is_same  = compare_bytes result expected in
  IO.print_string s;
  IO.print_string "\n";
  print_compare_bytes result expected

let print_compare_named_opt_bytes (#n : size_nat) (s : string)
  (result expected : option (lbytes n)) : ML bool =
  let is_same  = compare_opt_bytes result expected in
  IO.print_string s;
  IO.print_string "\n";
  print_compare_opt_bytes result expected

let print_keypair (#nc : config) (kp : keypair nc) : ML unit =
  print_named_bytes "-pub " kp.pub;
  print_named_bytes "-priv" kp.priv;
  IO.print_string "\n"

let print_opt_keypair (#nc : config) (okp : option (keypair nc)) : ML unit =
  match okp with
  | None -> IO.print_string "None"
  | Some kp -> print_keypair kp

let print_cipher_state (st : cipher_state) : ML unit =
  IO.print_string "-key: ";
  (match st.k with
   | None -> IO.print_string "None"
   | Some k' -> print_bytes k');
  IO.print_string "\n-nonce:";
  IO.print_uint64 (FStar.UInt64.uint_to_t (if st.n >= pow2 64 - 1 then pow2 64 - 1 else st.n));
  IO.print_string "\n"

let print_symmetric_state (#nc : config) (st : symmetric_state nc) : ML unit =
  IO.print_string "-- cipher:\n";
  print_cipher_state st.c_state;
  IO.print_string "- keychain: ";
  print_bytes st.ck;
  IO.print_string"\n- hash: ";
  print_bytes st.h;
  IO.print_string "\n"

(* subtype_of a b =/=> subtype_of (option a) (option b) *)
let convert_option (#a : Type) (#b : Type{subtype_of a b}) ($x : option a) : option b =
  match x with
  | None -> None
  | Some x -> Some x

let print_handshake_state (#nc : config) (step : string) (st : handshake_state nc) :
  ML unit =
  IO.print_string "** ";
  IO.print_string step;
  IO.print_string ":\n";
  IO.print_string "[--- symmetric_state:\n";
  print_symmetric_state st.sym_state;
  IO.print_string "---]\n";
  IO.print_string "\n--- static:\n";
  print_opt_keypair st.static;
  IO.print_string "--- ephemeral:\n";
  print_opt_keypair st.ephemeral;
  IO.print_string "\n--- remote_static: ";
  print_opt_bytes st.remote_static;
  IO.print_string "--- remote_ephemeral: ";
  print_opt_bytes st.remote_ephemeral;
  IO.print_string "\n--- preshared: ";
  print_opt_bytes st.preshared;
  IO.print_string "\n\n"

let cipher_states_equal (st1 st2 : cipher_state) : Tot bool =
  let same_keys =
    (match st1.k, st2.k with
     | Some k1, Some k2 -> compare_bytes k1 k2
     | None, None -> true
     | _ -> false)
  in
  same_keys && (st1.n = st2.n)

let print_compare_cipher_states (st1 st2 : cipher_state) : ML bool =
  let same = cipher_states_equal st1 st2 in
  if same
  then IO.print_string "Same cipher states\n"
  else IO.print_string "Different cipher states\n";
  same

let print_cipher_states_pair (p : cipher_states_pair) : ML unit =
  let c1, c2 = p in
  IO.print_string "- cipher state 1:\n";
  print_cipher_state c1;
  IO.print_string "\n- cipher state 2:\n";
  print_cipher_state c2;
  IO.print_string "\n"

let keypair_from_private (#nc : config) (p : private_key nc) : option (keypair nc) =
    let opub = secret_to_public p in
    match opub with
    | None -> None
    | Some pub ->
      Some({ pub = pub; priv = p })

let keypair_from_opt_private (#nc : config) (p : option (private_key nc)) :
  option (keypair nc) =
  match p with
  | None -> None
  | Some priv -> keypair_from_private priv
