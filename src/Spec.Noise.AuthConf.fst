/// This file provides functions to compute the Noise authentication and
/// confidentiality levels listed in the technical paper.

module Spec.Noise.AuthConf

open FStar.Mul
open Spec.Noise.Base
open FStar.List.Tot

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(* TODO: move *)
val zip : l1:list 'a -> l2:list 'b -> Tot (list ('a & 'b)) (decreases l1)
let rec zip l1 l2 =
  match l1, l2 with
  | x1::l1', x2::l2' -> (x1,x2) :: zip l1' l2'
  | _ -> []

val zip_length_lem : l1:list 'a -> l2:list 'b ->
  Lemma (requires True)
  (ensures (
    if length l1 <= length l2 then length (zip l1 l2) = length l1
    else length (zip l1 l2) = length l2))
  (decreases l1)
  [SMTPat (zip l1 l2)]
#push-options "--ifuel 1 --fuel 1"
let rec zip_length_lem l1 l2 =
  match l1, l2 with
  | x1::l1', x2::l2' -> zip_length_lem l1' l2'
  | _ -> ()
#pop-options

val init_length_lem : l:list 'a {Cons? l} ->
  Lemma (requires True) (ensures (length (init l) = length l - 1))
  [SMTPat (init l)]
#push-options "--ifuel 1 --fuel 1"
let rec init_length_lem l =
  match l with
  | [_] -> ()
  | hd :: tl -> init_length_lem tl
#pop-options


(**** Authentication, confidentiality *)

inline_for_extraction noextract
let max_conf_level = 5
inline_for_extraction noextract
let max_auth_level = 2
inline_for_extraction noextract
type conf_level = x:nat{x <= max_conf_level}
inline_for_extraction noextract
type auth_level = x:nat{x <= max_auth_level}

/// Authentication, confidentiality state flags.
/// Pay attention to the fact that in this file, contrary to what is done elsewhere,
/// we always take the point of view of the sender. For instance, 'es' doesn't mean:
/// [> DH initiator_ephemeral responder_static
/// but:
/// [> DH our_ephemeral their_static
type acs_flags = {
  e : bool;
  re : bool;
  ss : bool;
  ee : bool;
  se : bool;
  es : bool;
  psk : bool;
}

let acs_cleared_flags =
  { e = false; re = false; ss = false; ee = false; se = false; es = false; psk = false; }

let set_e (af : acs_flags) : acs_flags =
  { af with e = true }

let set_ss (af : acs_flags) : acs_flags =
  { af with ss = true }

let set_ee (af : acs_flags) : acs_flags =
  { af with ee = true }

let set_se (ir : bool) (af : acs_flags) : acs_flags =
  if ir then { af with se = true } else { af with es = true }

let set_es (ir : bool) (af : acs_flags) : acs_flags =
  if ir then { af with es = true } else { af with se = true }

let set_psk (af : acs_flags) : acs_flags =
  { af with psk = true }

let revert_ir (af : acs_flags) : acs_flags =
  { af with e = af.re; re = af.e; se = af.es; es = af.se; }

/// Update the AC flags over a token
let token_update_acs (ir : bool) (acs : acs_flags) (tk : message_token) :
  Tot acs_flags =
  match tk with
  | E -> set_e acs
  | SE -> set_se ir acs
  | ES -> set_es ir acs
  | EE -> set_ee acs
  | SS -> set_ss acs
  | PSK -> set_psk acs
  | _ -> acs

/// Update the AC flags over a message
let rec message_update_acs (ir : bool) (acs : acs_flags) (pat : list message_token) :
  Tot acs_flags (decreases pat) =
  match pat with
  | [] -> acs
  | tk :: pat' -> message_update_acs ir (token_update_acs ir acs tk) pat'

/// Compute the AC flags for a list of messages
#push-options "--ifuel 1 --fuel 1"
let rec compute_messages_acs (ir : bool) (acs : acs_flags) (msgs : list (list message_token)) :
  Pure (option (list acs_flags))
  (requires True)
  (ensures (fun l -> match l with | None -> True | Some l -> length l = length msgs))
  (decreases msgs) =
  match msgs with
  | [] -> Some []
  | msg :: msgs1 ->
    (* Analyze the current message *)
    let acs1 = message_update_acs ir acs msg in
    (* Invert sender and receiver in the representation before doing
     * the recursion *)
    let ls_opt = compute_messages_acs (not ir) (revert_ir acs1) msgs1 in
    match ls_opt with
    | None -> None
    | Some ls -> Some (acs1 :: ls)
#pop-options

(* Convert a list of messages to a list of lists of tokens *)
#push-options "--ifuel 1 --fuel 1"
let rec convert_messages (ir : bool) (msgs : list message) :
  Pure (option (list (list message_token)))
  (requires True)
  (ensures (fun l -> match l with | None -> True | Some l -> length l = length msgs))
  (decreases msgs) =
  match msgs with
  | [] -> Some []
  | msg :: msgs' ->
    let opt_pat =
      match ir, msg with
      | true, Ir pat -> Some pat
      | false, Ri pat -> Some pat
      | _ -> None
    in
    match opt_pat, convert_messages (not ir) msgs' with
    | Some pat, Some pattern -> Some (pat :: pattern)
    | _ -> None
#pop-options

/// Compute the AC flags for all the messages of a handshake. Once again, pay attention
/// to the fact that the AC flags are computed by taking the point of view of the sender
/// (and the two parties alternate between sender and receiver).
let hsk_acs (hsk : list message) : Tot (option (list acs_flags)) =
  (* Remove the premessages then call the auxiliary function *)
  let msgs =
    match hsk with
    | Pre_ir _ :: Pre_ri _ :: msgs -> msgs
    | Pre_ir _ :: msgs -> msgs
    | Pre_ri _ :: msgs -> msgs
    | _ -> hsk
  in
  match convert_messages true msgs with
  | Some msgs -> compute_messages_acs true acs_cleared_flags msgs
  | _ -> None

/// Compute the authentication level given the current AC flags
let compute_auth_level (acs : acs_flags) : auth_level =
  if acs.se then 2
  else if (acs.psk || acs.ss) && acs.e then 1
  else 0

/// Compute the confidentiality level given the current and previous AC flags
/// (note that in order to compute the confidentiality level we may need to know
/// if some conditions are satisfied after we received a message from the other
/// party, which is why we also need the previous AC flags, which represent the
/// state before the sender sends the current message).
/// Note that we extend the definition given in the technical paper to take
/// into account the PSK patterns.
let compute_conf_level (acs0 acs1 : acs_flags) : conf_level =
  match (acs0.ee, acs0.es, acs0.se, acs0.ss, acs0.psk), (acs1.ee, acs1.es, acs1.psk) with
  | (true, true, _, _, _), _ -> 5                (* ee, es; [msg] *)
  | (_, _, true, true, _), (true, true, _) -> 4  (* se, ss; [msg]; ee, es *)
  | _, (true, true, _) -> 3                      (* ee, es *)
  | _, (_, true, _) -> 2                         (* es *)
  // Level to determine - 3.5
  | (_, _, _, _, true), (true, _, _) -> 1        (* psk; [msg]; ee *)
  // This should have level 2.5 or something
  | _, (true, _, true) ->  1                     (* ee, psk *)
  | _, (true, _, _) -> 1                         (* ee *)
  // This should have level 1.5 or something
  | _, (_, _, true) -> 0                         (* psk *)
  | _, _ -> 0

/// Convert a list of acs flags to a list of authentication levels
let acsl_to_auth_levels (ls : list acs_flags) : list auth_level =
  List.Tot.map compute_auth_level ls

/// Compute the authentication levels for all the messages of a handshake
#push-options "--ifuel 1 --fuel 1"
let hsk_auth_levels (hsk : list message) : Tot (option (list auth_level)) =
  let acsl = hsk_acs hsk in
  match acsl with
  | None -> None
  | Some ls -> Some (acsl_to_auth_levels ls)

/// Convert a list of acs flags to a list of confidentiality levels
#push-options "--ifuel 1 --fuel 1"
let acsl_to_conf_levels (ls : list acs_flags) :
  Tot (l:list conf_level{length l = length ls}) =
  if Nil? ls then [] else
  let shifted_ls = acs_cleared_flags :: (List.Tot.Base.init ls) in
  let conf_level' = (fun (x,y) -> compute_conf_level (revert_ir x) y) in
  let zls = zip shifted_ls ls in
  List.Tot.map conf_level' zls
#pop-options
  
/// Compute the confidentiality levels for all the messages of a handshake
let hsk_conf_levels (hsk : list message) : Tot (option (list conf_level)) =
  let acsl = hsk_acs hsk in
  match acsl with
  | None -> None
  | Some ls -> Some (acsl_to_conf_levels ls)

// TODO: we shouldn't have this monolithic function but rather get_conf_at_step/
// get_auth_at_step functions
/// Same functions as above, but operate on already preocessed message lists
let auth_levels (pattern : list (list message_token)) :
  Pure (option (list auth_level))
  (requires True)
  (ensures (fun l -> match l with | None -> True | Some l -> length l = length pattern)) =
  let acsl = compute_messages_acs true acs_cleared_flags pattern in
  match acsl with
  | None -> None
  | Some ls -> Some (acsl_to_auth_levels ls)

let conf_levels (pattern : list (list message_token)) :
  Pure (option (list conf_level))
  (requires True)
  (ensures (fun l -> match l with | None -> True | Some l -> length l = length pattern)) =
  let acsl = compute_messages_acs true acs_cleared_flags pattern in
  match acsl with
  | None -> None
  | Some ls -> Some (acsl_to_conf_levels ls)

let ac_levels (pattern : list (list message_token)) :
  Pure (option (list (auth_level & conf_level)))
  (requires True)
  (ensures (fun l -> match l with | None -> True | Some l -> length l = length pattern)) =
  let auth = auth_levels pattern in
  let conf = conf_levels pattern in
  match auth, conf with
  | Some auth, Some conf -> Some (zip auth conf)
  | _ -> None

(*** Tests *)
(* IKpsk2 *)
(* auth : 1 2 2 2 *)
private let x1a = hsk_auth_levels [~<<~ [PS]; ~>~ [E; ES; S; SS]; ~<~ [E; EE; SE; PSK]; ~>~ []; ~<~ []]
(* conf : 2 4 5 5 *)
private let x1c = hsk_conf_levels [~<<~ [PS]; ~>~ [E; ES; S; SS]; ~<~ [E; EE; SE; PSK]; ~>~ []; ~<~ []]

private let x1_ac = (x1a = Some [1;2;2;2]) && (x1c = Some [2;4;5;5])

(* KN *)
(* auth : 0 0 2 0 *)
private let x2a = hsk_auth_levels [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE]; ~>~ []; ~<~ []] (* FAILS *)
(* conf : 0 3 1 5 *)
private let x2c = hsk_conf_levels [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE]; ~>~ []; ~<~ []]

private let x2_ac = (x2a = Some [0;0;2;0]) && (x2c = Some [0;3;1;5])

(* KX *)
(* auth : 0 2 2 2 *)
private let x3a = hsk_auth_levels [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE; S; ES]; ~>~ []; ~<~ []]
(* conf : 0 3 5 5  *)
private let x3c = hsk_conf_levels [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE; S; ES]; ~>~ []; ~<~ []]

private let x3_ac = (x3a = Some [0;2;2;2]) && (x3c = Some [0;3;5;5])

(* NK *)
(* auth : 0 2 0 *)
private let x4a = hsk_auth_levels [~<<~ [PS]; ~>~ [E; ES]; ~<~ [E; EE]; ~>~ []]
(* conf : 2 1 5  *)
private let x4c = hsk_conf_levels [~<<~ [PS]; ~>~ [E; ES]; ~<~ [E; EE]; ~>~ []]

private let x4_ac = (x4a = Some [0;2;0]) && (x4c = Some [2;1;5])

(* NN *)
(* auth : 0 0 0 *)
private let x5a = hsk_auth_levels [~>~ [E]; ~<~ [E; EE]; ~>~ []]
(* conf : 0 1 1  *)
private let x5c = hsk_conf_levels [~>~ [E]; ~<~ [E; EE]; ~>~ []]

private let x5_ac = (x5a = Some [0;0;0]) && (x5c = Some [0;1;1])

(* NX *)
(* auth : 0 2 0 *)
private let x6a = hsk_auth_levels [~>~ [E]; ~<~ [E; EE; S; ES]; ~>~ []]
(* conf : 0 1 5  *)
private let x6c = hsk_conf_levels [~>~ [E]; ~<~ [E; EE; S; ES]; ~>~ []]

private let x6_ac = (x6a = Some [0;2;0]) && (x6c = Some [0;1;5])

(* XN *)
(* auth : 0 0 2 0 *)
private let x7a = hsk_auth_levels [~>~ [E]; ~<~ [E; EE]; ~>~ [S; SE]; ~<~ []]
(* conf : 0 1 1 5  *)
private let x7c = hsk_conf_levels [~>~ [E]; ~<~ [E; EE]; ~>~ [S; SE]; ~<~ []]

private let x7_ac = (x7a = Some [0;0;2;0]) && (x7c = Some [0;1;1;5])

(* XK *)
(* auth : 0 2 2 2 *)
private let x8a = hsk_auth_levels [~<<~ [PS]; ~>~ [E; ES]; ~<~ [E; EE]; ~>~ [S; SE]; ~<~ []]
(* conf : 2 1 5 5  *)
private let x8c = hsk_conf_levels [~<<~ [PS]; ~>~ [E; ES]; ~<~ [E; EE]; ~>~ [S; SE]; ~<~ []]

private let x8_ac = (x8a = Some [0;2;2;2]) && (x8c = Some [2;1;5;5])

(* XX *)
(* auth : 0 2 2 2 *)
private let x9a = hsk_auth_levels [~>~ [E]; ~<~ [E; EE; S; ES]; ~>~ [S; SE]; ~<~ []]
(* conf : 0 1 5 5  *)
private let x9c = hsk_conf_levels [~>~ [E]; ~<~ [E; EE; S; ES]; ~>~ [S; SE]; ~<~ []]

private let x9_ac = (x9a = Some [0;2;2;2]) && (x9c = Some [0;1;5;5])

(* KN *)
(* auth : 0 0 2 0 *)
private let x10a = hsk_auth_levels [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE]; ~>~ []; ~<~ []]
(* conf : 0 3 1 5  *)
private let x10c = hsk_conf_levels [~>>~ [PS]; ~>~ [E]; ~<~ [E; EE; SE]; ~>~ []; ~<~ []]

private let x10_ac = (x10a = Some [0;0;2;0]) && (x10c = Some [0;3;1;5])

(* KK *)
(* auth : 1 2 2 2 *)
private let x11a = hsk_auth_levels [~>>~ [PS]; ~<<~ [PS]; ~>~ [E; ES; SS]; ~<~ [E; EE; SE]; ~>~ []; ~<~ []]
(* conf : 2 4 5 5  *)
private let x11c = hsk_conf_levels [~>>~ [PS]; ~<<~ [PS]; ~>~ [E; ES; SS]; ~<~ [E; EE; SE]; ~>~ []; ~<~ []]

private let x11_ac = (x11a = Some [1;2;2;2]) && (x11c = Some [2;4;5;5])

(* NNpsk0 *)
private let x12a = hsk_auth_levels [~>~ [PSK; E]; ~<~ [E; EE]; ~>~ []; ~<~ []]
private let x12c = hsk_conf_levels [~>~ [PSK; E]; ~<~ [E; EE]; ~>~ []; ~<~ []]
private let x12_ac = (x12a = Some [1;1;1;1]) && (x12c = Some [2;4;4;4])

(* NNpsk2 *)
private let x13a = hsk_auth_levels [~>~ [E]; ~<~ [E; EE; PSK]; ~>~ []; ~<~ []]
private let x13c = hsk_conf_levels [~>~ [E]; ~<~ [E; EE; PSK]; ~>~ []; ~<~ []]
private let x13_ac = (x13a = Some [0;1;1;1]) && (x13c = Some [0;3;4;4])

(* NXpsk2 *)
private let x14a = hsk_auth_levels [~>~ [E]; ~<~ [E; EE; S; ES; PSK]; ~>~ []; ~<~ []]
private let x14c = hsk_conf_levels [~>~ [E]; ~<~ [E; EE; S; ES; PSK]; ~>~ []; ~<~ []]
private let x14_ac = (x14a = Some [0;2;1;2]) && (x14c = Some [0;3;5;4])

(** [check_bool b] will not typecheck if [b] normalizes to false *)
let check_bool (b : bool{normalize_term(b) == true}) = ()

private let _ = check_bool x1_ac
private let _ = check_bool x2_ac
private let _ = check_bool x3_ac
private let _ = check_bool x4_ac
private let _ = check_bool x5_ac
private let _ = check_bool x6_ac
private let _ = check_bool x7_ac
private let _ = check_bool x8_ac
private let _ = check_bool x9_ac
private let _ = check_bool x10_ac
private let _ = check_bool x11_ac
// TODO: update the PSK level checks
//private let _ = check_bool x12_ac
//private let _ = check_bool x13_ac
//private let _ = check_bool x14_ac
