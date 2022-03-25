(**
 * Debugging parameter
 *)
let debug = ref false

let print_dbg (s : string) =
  if !debug then print_endline s else ()

(**
 * Conversion from string to F* bytes
 *)
let string_to_bytes (s : string) =
  (* Convert from string to list *)
  let rec split s i =
    if i < String.length s then
      s.[i] :: split s (i+1)
    else []
  in
  split s 0
  (* Convert from char to uint8 *)
  |> List.map (fun c -> FStar_UInt8.int_to_uint8 (Prims.of_int (Char.code c)))
  (* Convert to sequence *)
  |> Lib_Sequence.of_list

(**
 * Conversion of hexadecimal to F* bytes
 *)
let hexa_to_bytes (s : string) =
  if String.length s mod 2 <> 0
  then raise (Failure ("Expected an hexadecimal string but the length is not even: " ^ s));
  (* Convert from string to list of strings (of two characters) *)
  let rec split s i =
    if i+1 < String.length s then
      String.sub s i 2 :: split s (i+2)
    else []
  in
  split s 0
  (* Convert from list of hexa strings (of two characters) to list of int.
   * This is definitely not efficient nor elegant, but I am not looking for
   * efficiency, and I don't want to rely on the Hex module *)
  |> List.map (fun x -> int_of_string ("0x" ^ x))
  (* Convert from char to uint8 *)
  |> List.map (fun x -> FStar_UInt8.int_to_uint8 (Prims.of_int x))
  (* Convert to sequence *)
  |> Lib_Sequence.of_list

(**
 * Exception to filter unsupported algorithms
 *)
exception Unsupported of string

(**
 * Convert one json vector to a Noise vector
 *)
let json_to_vector v =
  print_dbg "[> json_to_vector";
  let open Yojson.Basic.Util in
  (* Utilities *)
  (*  let to_bytes (s : string) : bytes = Hex.to_string (`Hex s) |> Bytes.of_string in *)
  let json_to_bytes js = to_string js |> hexa_to_bytes in
  (* Those values MUST be in the json *)
  print_dbg "- loading the always present values";
  let protocol_name = v |> member "protocol_name" |> to_string in
  let init_prologue = v |> member "init_prologue" |> json_to_bytes in
  let resp_prologue = v |> member "resp_prologue" |> json_to_bytes in
  let handshake_hash = v |> member "handshake_hash" |> json_to_bytes in
  if init_prologue <> resp_prologue
  then raise (Failure "Initiator and responder should use the same prologue.");
  let json_to_message js =
    let open Spec_Noise_Testing_Base in
    let payload = js |> member "payload" |> json_to_bytes in
    let ciphertext = js |> member "ciphertext" |> json_to_bytes in
    { payload = payload; ciphertext = ciphertext }
  in
  print_dbg "- loading the messages";  
  let messages = member "messages" v |> to_list in
  print_dbg (Printf.sprintf "%d messages" (List.length messages));
  let messages = List.map json_to_message messages in
  (* Analyze the pattern name *)
  (* ex.: "protocol_name": "Noise_NN_25519_AESGCM_BLAKE2b" *)
  print_dbg "- analyzing pattern name";
  let pname_substrings = String.split_on_char '_' protocol_name in
  let pattern_name, dh_alg, aead_alg, hash_alg =
    match pname_substrings with
    | [_; pattern_name; dh_alg; aead_alg; hash_alg] ->
      pattern_name, dh_alg, aead_alg, hash_alg
    | _ -> raise (Failure ("Invalid protocol name: " ^ protocol_name))
  in
  let dh_alg = match dh_alg with
    | "25519" -> Spec_Agile_DH.DH_Curve25519
    | "448" -> raise (Unsupported ("Algorithm not supported: Curve448"))
    | _ -> raise (Failure ("Invalid DH algrithm: " ^ dh_alg))
  in
  let aead_alg = match aead_alg with
    | "AESGCM" -> Spec_Agile_AEAD.AES256_GCM
    | "ChaChaPoly" -> Spec_Agile_AEAD.CHACHA20_POLY1305
    | _ -> raise (Failure ("Invalid AEAD algrithm: " ^ aead_alg))
  in
  let hash_alg = match hash_alg with
    | "BLAKE2b" -> Spec_Noise_Agile.KeyedHash Spec_Blake2.Blake2B
    | "BLAKE2s" -> Spec_Noise_Agile.KeyedHash Spec_Blake2.Blake2S
    | "SHA256" -> Spec_Noise_Agile.Hash Spec_Hash_Definitions.SHA2_256
    | "SHA512" -> Spec_Noise_Agile.Hash Spec_Hash_Definitions.SHA2_512
    | _ -> raise (Failure ("Invalid hash algrithm: " ^ hash_alg))
  in
  let pattern =
    let open Spec_Noise_Base in
    match List.find_opt (fun pat -> pat.name = pattern_name) Spec_Noise_Patterns.patterns with
    | Some pattern -> pattern
    | None -> raise (Failure ("Could not find pattern: " ^ pattern_name))
  in
  (* Load the remaining values, which are not necessarily in the vector *)
  let init_ephemeral = ref None in
  let resp_ephemeral = ref None in
  let init_static = ref None in
  let resp_static = ref None in
  let init_remote_static = ref None in
  let resp_remote_static = ref None in
  let psk = ref None in
  let load_value (k,v) =
    match k with
    (* Those values have already been loaded *)
    | "protocol_name" | "init_prologue" | "resp_prologue" | "messages" | "handshake_hash" -> ()
    (* Remaining values *)
    | "init_ephemeral" -> init_ephemeral := Some (json_to_bytes v)
    | "resp_ephemeral" -> resp_ephemeral := Some (json_to_bytes v)
    | "init_static" -> init_static := Some (json_to_bytes v)
    | "resp_static" -> resp_static := Some (json_to_bytes v)
    | "init_remote_static" -> init_remote_static := Some (json_to_bytes v)
    | "resp_remote_static" -> resp_remote_static := Some (json_to_bytes v)
    | "init_psks" | "resp_psks" ->
       (* There should only be one PSK in the list, and the initiator and responder PSKs should
        * be the same *)
       let v = to_list v in
       if List.length v > 1 then raise (Failure "There should be at most one PSK per pattern");
       let psk' = json_to_bytes (List.hd v) in
       begin match !psk with
       | None -> ()
       | Some psk ->
         if psk <> psk' then raise (Failure "Initiator and responder should use the same PSK.")
       end;
       psk := Some psk'
    | _ -> raise (Failure ("Unknown field: " ^ k))
  in
  List.iter load_value (to_assoc v);
  (* Debugging *)
  if !debug then
    begin
      let to_hexa s =
        (* Again, I don't want to rely on Hex *)
        Lib_Sequence.to_list s
        |> List.map (fun x -> Printf.sprintf "%x" x)
        |> String.concat ""
          (* match Bytes.to_string s |> Hex.of_string with | `Hex s -> s *)
      in
      let option_to_hexa opt =
        match opt with
        | None -> ""
        | Some v -> to_hexa v
      in
      let print_msg i msg =
        let open Spec_Noise_Testing_Base in
        Printf.printf "- message %d:\n" i;
        Printf.printf "-- payload: %s\n" (to_hexa msg.payload);
        Printf.printf "-- cipher : %s\n" (to_hexa msg.ciphertext)
      in
      print_endline "-- Loaded vector:";
      Printf.printf "- protocol_name: %s\n" protocol_name;
      Printf.printf "- pattern name: %s\n" pattern_name;
(*      Printf.printf "- DH algorithm: %s\n" dh_alg;
      Printf.printf "- AEAD algorithm: %s\n" aead_alg;
      Printf.printf "- hash algorithm: %s\n" hash_alg;*)
      Printf.printf "- prologue: %s\n" (to_hexa init_prologue);
      Printf.printf "- handshake_hash: %s\n" (to_hexa handshake_hash);
      Printf.printf "- init_ephemeral: %s\n" (option_to_hexa !init_ephemeral);
      Printf.printf "- resp_ephemeral: %s\n" (option_to_hexa !resp_ephemeral);
      Printf.printf "- init_static: %s\n" (option_to_hexa !init_static);
      Printf.printf "- resp_static: %s\n" (option_to_hexa !resp_static);
      List.iteri print_msg messages
    end;
  (* Return a handshake_test_vector *)
  let open Spec_Noise_Testing_Base in
  {
    nc = (dh_alg, aead_alg, hash_alg);
    pattern = pattern;
    protocol_str = protocol_name;
    protocol_name = string_to_bytes protocol_name;
    prologue = init_prologue;
    is = !init_static;
    ie = !init_ephemeral;
    rs = !resp_static;
    re = !resp_ephemeral;
    irs = !init_remote_static;
    rrs = !resp_remote_static;
    psk = !psk;
    final_hash = handshake_hash;
    msgs = messages;
  }

let json_to_opt_vector v =
  print_dbg "[> json_to_opt_vector";
  try Some (json_to_vector v)
  with Unsupported str ->
       print_dbg ("Ignoring a vector because of an error: " ^ str);
       None

(**
 * Filter the vectors.
 * The difference with the filtering performed inside json_to_vector is that
 * in json_to_vector, we raise an error when we need to encode a field for
 * which we don't have a representation (i.e.: Curve448 is not an algorithm
 * defined in HACL* ), while this filtering here prunes the vectors for which
 * we don't have a executable specfication.
 *)
let vector_is_supported v =
  let open Spec_Noise_Testing_Base in
  match v.nc with
  | _, Spec_Agile_AEAD.AES256_GCM, _ -> false
  | _ -> true

(**
 * Convert a json to a list of vectors
 *)
let json_to_vectors json =
  print_dbg "[> json_to_vectors";
  let open Yojson.Basic.Util in
  let vectors = List.map json_to_opt_vector (json |> member "vectors" |> to_list) in
  let vectors = List.filter (fun x -> match x with | Some _ -> true | _ -> false) vectors in
  let vectors = List.map (fun x -> match x with
                                   | Some v -> v
                                   | _ -> raise (Failure ("Inconsistant state"))) vectors
  in
  let vectors = List.filter vector_is_supported vectors in
  Printf.printf "Loaded %d vectors\n" (List.length vectors);
  vectors

(**
 * The function expected by the .ml interface to load the test vectors
 *)
let load_test_vectors () =
  print_dbg "[> load_test_vectors";
  let json = Yojson.Basic.from_file "./vectors/cacophony.txt" in
  let vectors = json_to_vectors json in
  print_endline ("Finished");
  vectors
