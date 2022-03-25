module Spec.Noise.PatternsSecurity

open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Meta.Noise
open Spec.Noise.AuthConf
open Spec.Noise.Patterns
module T = FStar.Tactics
open FStar.List.Tot

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(*** Reference levels *)
/// The following file defines the security (secrecy, authentication, identity hiding)
/// levels for the patterns listed in the Noise technical paper.
/// We just copied the levels listed in the paper.

//type secrecy_level = x:nat{x <= 5}
//type auth_level = x:nat{x <= 2}
type id_hide_level = nat // x:nat{x <= 9}

type pattern_levels = {
  confidentiality : list conf_level;
  authentication : (auth:list auth_level{List.Tot.length auth = List.Tot.length confidentiality});
  init_hide : option id_hide_level;
  resp_hide : option id_hide_level;
}

type auth_conf =
  ls:((list auth_level) & (list conf_level)) {
    let ls1, ls2 = ls in
    List.Tot.length ls1 = List.Tot.length ls2
  }

type id_hide = option id_hide_level & option id_hide_level // (initiator, responder)

let mk_auth_conf(auth : list auth_level) (conf : list conf_level) :
  Pure auth_conf
  (requires (normalize_term (List.Tot.length auth) = normalize_term (List.Tot.length conf)))
  (ensures (fun _ -> True)) =
  normalize_term_spec (List.Tot.length auth);
  normalize_term_spec (List.Tot.length conf);
  auth, conf

let pattern_N_auth_conf_ref : auth_conf = mk_auth_conf [0] [2]
let pattern_K_auth_conf_ref : auth_conf = mk_auth_conf [1] [2]
let pattern_X_auth_conf_ref : auth_conf = mk_auth_conf [1] [2]
let pattern_NN_auth_conf_ref : auth_conf = mk_auth_conf [0;0;0] [0;1;1]
let pattern_NK_auth_conf_ref : auth_conf = mk_auth_conf [0;2;0] [2;1;5]
let pattern_NX_auth_conf_ref : auth_conf = mk_auth_conf [0;2;0] [0;1;5]
let pattern_XN_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;0] [0;1;1;5]
let pattern_XK_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [2;1;5;5]
let pattern_XX_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;1;5;5]
let pattern_KN_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;0] [0;3;1;5]
let pattern_KK_auth_conf_ref : auth_conf = mk_auth_conf [1;2;2;2] [2;4;5;5]
let pattern_KX_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;3;5;5]
let pattern_IN_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;0] [0;3;1;5]
let pattern_IK_auth_conf_ref : auth_conf = mk_auth_conf [1;2;2;2] [2;4;5;5]
let pattern_IX_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;3;5;5]
let pattern_NK1_auth_conf_ref : auth_conf = mk_auth_conf [0;2;0] [0;1;5]
let pattern_NX1_auth_conf_ref : auth_conf = mk_auth_conf [0;0;0;2;0] [0;1;3;1;5]
let pattern_X1N_auth_conf_ref : auth_conf = mk_auth_conf [0;0;0;0;2] [0;1;1;3;1]
let pattern_X1K_auth_conf_ref : auth_conf = mk_auth_conf [0;2;0;2;2;2] [2;1;5;3;5;5]
let pattern_XK1_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;1;5;5]
let pattern_X1K1_auth_conf_ref : auth_conf = mk_auth_conf [0;2;0;2;2;2] [0;1;5;3;5;5]
let pattern_X1X_auth_conf_ref : auth_conf = mk_auth_conf [0;2;0;2;2;2] [0;1;5;3;5;5]
let pattern_XX1_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;2;2] [0;1;3;5;5]
let pattern_X1X1_auth_conf_ref : auth_conf = mk_auth_conf [0;0;0;2;2;2] [0;1;3;3;5;5]
let pattern_K1N_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;0] [0;1;1;5]
let pattern_K1K_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [2;1;5;5]
let pattern_KK1_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;3;5;5]
let pattern_K1K1_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;1;5;5]
let pattern_K1X_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;1;5;5]
let pattern_KX1_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;2;2] [0;3;3;5;5]
let pattern_K1X1_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;2;2] [0;1;3;5;5]
let pattern_I1N_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;0] [0;1;1;5]
let pattern_I1K_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [2;1;5;5]
let pattern_IK1_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;3;5;5]
let pattern_I1K1_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;1;5;5]
let pattern_I1X_auth_conf_ref : auth_conf = mk_auth_conf [0;2;2;2] [0;1;5;5]
let pattern_IX1_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;2;2] [0;3;3;5;5]
let pattern_I1X1_auth_conf_ref : auth_conf = mk_auth_conf [0;0;2;2;2] [0;1;3;5;5]

let pattern_N_id_hide : id_hide = (None, Some 3)
let pattern_K_id_hide : id_hide = (Some 5, Some 5)
let pattern_X_id_hide : id_hide = (Some 4, Some 3)
let pattern_NN_id_hide : id_hide = (None, None)
let pattern_NK_id_hide : id_hide = (None, Some 3)
let pattern_NK1_id_hide : id_hide = (None, Some 9)
let pattern_NX_id_hide : id_hide = (None, Some 1)
let pattern_XN_id_hide : id_hide = (Some 2, None)
let pattern_XK_id_hide : id_hide = (Some 8, Some 3)
let pattern_XK1_id_hide : id_hide = (Some 8, Some 9)
let pattern_XX_id_hide : id_hide = (Some 8, Some 1)
let pattern_KN_id_hide : id_hide = (Some 7, None)
let pattern_KK_id_hide : id_hide = (Some 5, Some 5)
let pattern_KX_id_hide : id_hide = (Some 7, Some 6)
let pattern_IN_id_hide : id_hide = (Some 0, None)
let pattern_IK_id_hide : id_hide = (Some 4, Some 3)
let pattern_IK1_id_hide : id_hide = (Some 0, Some 9)
let pattern_IX_id_hide : id_hide = (Some 0, Some 6)

/// [Spec.Noise.AuthConf] defines functions to compute those security levels.
/// Below, we check that we get the same levels as listed above.
/// This is a bit redundant with what is already done in [Spec.Noise.AuthConf],
/// but we check very thoroughly below.
let check_ac_levels (hsk : handshake_pattern) (ac : auth_conf) : Tot bool =
  let messages = hsk.messages in
  // Append 2 empty messages only if the pattern is two ways
  let messages = if length messages > 1 then append messages [[]; []] else messages in
  // But the Noise spec doesn't always append two messages...
  let messages = fst (splitAt (length (fst ac)) messages) in
  let opt_ac' = ac_levels messages in
  let ac = zip (fst ac) (snd ac) in
  let ac = map (fun (z : auth_level & conf_level) -> let x, y = z in (x, y)) ac in // typing problem due to the refinements
  if Some? opt_ac' then Some?.v opt_ac' = ac else false

let b_N = check_ac_levels pattern_N pattern_N_auth_conf_ref
let b_K = check_ac_levels pattern_K pattern_K_auth_conf_ref
let b_X = check_ac_levels pattern_X pattern_X_auth_conf_ref
let b_NN = check_ac_levels pattern_NN pattern_NN_auth_conf_ref
let b_NK = check_ac_levels pattern_NK pattern_NK_auth_conf_ref
let b_NX = check_ac_levels pattern_NX pattern_NX_auth_conf_ref
let b_XN = check_ac_levels pattern_XN pattern_XN_auth_conf_ref
let b_XK = check_ac_levels pattern_XK pattern_XK_auth_conf_ref
let b_XX = check_ac_levels pattern_XX pattern_XX_auth_conf_ref
let b_KN = check_ac_levels pattern_KN pattern_KN_auth_conf_ref
let b_KK = check_ac_levels pattern_KK pattern_KK_auth_conf_ref
let b_KX = check_ac_levels pattern_KX pattern_KX_auth_conf_ref
let b_IN = check_ac_levels pattern_IN pattern_IN_auth_conf_ref
let b_IK = check_ac_levels pattern_IK pattern_IK_auth_conf_ref
let b_IX = check_ac_levels pattern_IX pattern_IX_auth_conf_ref
let b_NK1 = check_ac_levels pattern_NK1 pattern_NK1_auth_conf_ref
let b_NX1 = check_ac_levels pattern_NX1 pattern_NX1_auth_conf_ref
let b_X1N = check_ac_levels pattern_X1N pattern_X1N_auth_conf_ref
let b_X1K = check_ac_levels pattern_X1K pattern_X1K_auth_conf_ref
let b_XK1 = check_ac_levels pattern_XK1 pattern_XK1_auth_conf_ref
let b_X1K1 = check_ac_levels pattern_X1K1 pattern_X1K1_auth_conf_ref
let b_X1X = check_ac_levels pattern_X1X pattern_X1X_auth_conf_ref
let b_XX1 = check_ac_levels pattern_XX1 pattern_XX1_auth_conf_ref
let b_X1X1 = check_ac_levels pattern_X1X1 pattern_X1X1_auth_conf_ref
let b_K1N = check_ac_levels pattern_K1N pattern_K1N_auth_conf_ref
let b_K1K = check_ac_levels pattern_K1K pattern_K1K_auth_conf_ref
let b_KK1 = check_ac_levels pattern_KK1 pattern_KK1_auth_conf_ref
let b_K1K1 = check_ac_levels pattern_K1K1 pattern_K1K1_auth_conf_ref
let b_K1X = check_ac_levels pattern_K1X pattern_K1X_auth_conf_ref
let b_KX1 = check_ac_levels pattern_KX1 pattern_KX1_auth_conf_ref
let b_K1X1 = check_ac_levels pattern_K1X1 pattern_K1X1_auth_conf_ref
let b_I1N = check_ac_levels pattern_I1N pattern_I1N_auth_conf_ref
let b_I1K = check_ac_levels pattern_I1K pattern_I1K_auth_conf_ref
let b_IK1 = check_ac_levels pattern_IK1 pattern_IK1_auth_conf_ref
let b_I1K1 = check_ac_levels pattern_I1K1 pattern_I1K1_auth_conf_ref
let b_I1X = check_ac_levels pattern_I1X pattern_I1X_auth_conf_ref
let b_IX1 = check_ac_levels pattern_IX1 pattern_IX1_auth_conf_ref
let b_I1X1 = check_ac_levels pattern_I1X1 pattern_I1X1_auth_conf_ref

let _ = check_bool b_N
let _ = check_bool b_K
let _ = check_bool b_X
let _ = check_bool b_NN
let _ = check_bool b_NK
let _ = check_bool b_NX
let _ = check_bool b_XN
let _ = check_bool b_XK
let _ = check_bool b_XX
let _ = check_bool b_KN
let _ = check_bool b_KK
let _ = check_bool b_KX
let _ = check_bool b_IN
let _ = check_bool b_IK
let _ = check_bool b_IX
let _ = check_bool b_NK1
let _ = check_bool b_NX1
let _ = check_bool b_X1N
let _ = check_bool b_X1K
let _ = check_bool b_XK1
let _ = check_bool b_X1K1
let _ = check_bool b_X1X
let _ = check_bool b_XX1
let _ = check_bool b_X1X1
let _ = check_bool b_K1N
let _ = check_bool b_K1K
let _ = check_bool b_KK1
let _ = check_bool b_K1K1
let _ = check_bool b_K1X
let _ = check_bool b_KX1
let _ = check_bool b_K1X1
let _ = check_bool b_I1N
let _ = check_bool b_I1K
let _ = check_bool b_IK1
let _ = check_bool b_I1K1
let _ = check_bool b_I1X
let _ = check_bool b_IX1
let _ = check_bool b_I1X1

(*** Computed levels *)
/// For the API, we need to compute security levels for all the patterns appearing
/// in the Noise technical paper (including the PSK patterns, whose security levels
/// are not given). As our computations are consistent with those from the Noise
/// technical paper, we take the opportunity compute those levels in a more uniform way
/// (for the two-way patterns, we add two transport messages).
/// For the PSK patterns, we treat the PSK as SS. Note that SS requires both S to have been
/// exchanged, meaning that we only consider as valid the patterns in which all the S
/// are exchanged before PSK is processed. This is the case for all the patterns in
/// the technical paper, and is actually a requirement for the Noise* high-level API
/// to be able to implement the pattern (for other reasons).

// TODO: move
val unzip_length_lem: ls:list ('a * 'b) -> Lemma (let l1, l2 = unzip ls in length l1 = length l2)

#push-options "--ifuel 1 --fuel 1"
let rec unzip_length_lem ls =
  match ls with
  | [] -> ()
  | x :: ls' -> unzip_length_lem ls'
#pop-options

[@@ (strict_on_arguments [0])]
let ac_levels (hsk : handshake_pattern) :
  Pure (option (list (auth_level & conf_level)))
  (requires True)
  (ensures (fun l ->
    match l with
    | None -> True
    | Some l ->
      if length hsk.messages > 1 then length l = length hsk.messages + 2
      else length l = length hsk.messages)) =
  let messages = hsk.messages in
  // Append two empty messages if the pattern is two ways
  let messages = if length messages > 1 then append messages [[]; []] else messages in
  (**) List.Tot.Properties.append_length hsk.messages [[]; []];
  (**) assert_norm(length #(list message_token) [[]; []] = 2);
  ac_levels messages

[@@ (strict_on_arguments [0])]
let ac_levels_some (hsk : handshake_pattern{Some? (normalize_term(ac_levels hsk))}) :
  auth_conf =
  let levels = Some?.v (ac_levels hsk) in
  (**) unzip_length_lem levels;
  unzip levels

/// The already known patterns
[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_N_auth_conf : auth_conf = ac_levels_some pattern_N

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K_auth_conf : auth_conf = ac_levels_some pattern_K

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X_auth_conf : auth_conf = ac_levels_some pattern_X

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NN_auth_conf : auth_conf = ac_levels_some pattern_NN

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NK_auth_conf : auth_conf = ac_levels_some pattern_NK

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NX_auth_conf : auth_conf = ac_levels_some pattern_NX

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XN_auth_conf : auth_conf = ac_levels_some pattern_XN

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XK_auth_conf : auth_conf = ac_levels_some pattern_XK

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XX_auth_conf : auth_conf = ac_levels_some pattern_XX

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KN_auth_conf : auth_conf = ac_levels_some pattern_KN

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KK_auth_conf : auth_conf = ac_levels_some pattern_KK

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KX_auth_conf : auth_conf = ac_levels_some pattern_KX

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IN_auth_conf : auth_conf = ac_levels_some pattern_IN

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IK_auth_conf : auth_conf = ac_levels_some pattern_IK

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IX_auth_conf : auth_conf = ac_levels_some pattern_IX

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NK1_auth_conf : auth_conf = ac_levels_some pattern_NK1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NX1_auth_conf : auth_conf = ac_levels_some pattern_NX1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1N_auth_conf : auth_conf = ac_levels_some pattern_X1N

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1K_auth_conf : auth_conf = ac_levels_some pattern_X1K

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XK1_auth_conf : auth_conf = ac_levels_some pattern_XK1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1K1_auth_conf : auth_conf = ac_levels_some pattern_X1K1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1X_auth_conf : auth_conf = ac_levels_some pattern_X1X

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XX1_auth_conf : auth_conf = ac_levels_some pattern_XX1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1X1_auth_conf : auth_conf = ac_levels_some pattern_X1X1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1N_auth_conf : auth_conf = ac_levels_some pattern_K1N

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1K_auth_conf : auth_conf = ac_levels_some pattern_K1K

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KK1_auth_conf : auth_conf = ac_levels_some pattern_KK1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1K1_auth_conf : auth_conf = ac_levels_some pattern_K1K1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1X_auth_conf : auth_conf = ac_levels_some pattern_K1X

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KX1_auth_conf : auth_conf = ac_levels_some pattern_KX1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1X1_auth_conf : auth_conf = ac_levels_some pattern_K1X1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1N_auth_conf : auth_conf = ac_levels_some pattern_I1N

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1K_auth_conf : auth_conf = ac_levels_some pattern_I1K

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IK1_auth_conf : auth_conf = ac_levels_some pattern_IK1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1K1_auth_conf : auth_conf = ac_levels_some pattern_I1K1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1X_auth_conf : auth_conf = ac_levels_some pattern_I1X

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IX1_auth_conf : auth_conf = ac_levels_some pattern_IX1

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1X1_auth_conf : auth_conf = ac_levels_some pattern_I1X1

/// The missing patterns (PSK)

// Custom normalization tactic which also prints the levels
let pp_normalize_print_tac () : T.Tac unit =
  let open FStar.Tactics in
  let g = T.cur_goal () in
  let str1 = begin match T.term_as_formula g with
  | Comp (Eq _) l r -> T.term_to_string l
  | _ -> T.fail ""
  end in
  T.norm [zeta; simplify; primops; delta; iota];
  let g = T.cur_goal () in
  let str2 = begin match T.term_as_formula g with
  | Comp (Eq _) l r -> T.term_to_string l
  | _ -> T.fail ""
  end in
  print (str1 ^ ": " ^ str2);
  T.trefl()

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_Npsk0_auth_conf : auth_conf = ac_levels_some pattern_Npsk0

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_Kpsk0_auth_conf : auth_conf = ac_levels_some pattern_Kpsk0

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_Xpsk1_auth_conf : auth_conf = ac_levels_some pattern_Xpsk1

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_NNpsk0_auth_conf : auth_conf = ac_levels_some pattern_NNpsk0

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_NNpsk2_auth_conf : auth_conf = ac_levels_some pattern_NNpsk2

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_NKpsk0_auth_conf : auth_conf = ac_levels_some pattern_NKpsk0

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_NKpsk2_auth_conf : auth_conf = ac_levels_some pattern_NKpsk2

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_NXpsk2_auth_conf : auth_conf = ac_levels_some pattern_NXpsk2

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_XNpsk3_auth_conf : auth_conf = ac_levels_some pattern_XNpsk3

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_XKpsk3_auth_conf : auth_conf = ac_levels_some pattern_XKpsk3

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_XXpsk3_auth_conf : auth_conf = ac_levels_some pattern_XXpsk3

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_KNpsk0_auth_conf : auth_conf = ac_levels_some pattern_KNpsk0

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_KNpsk2_auth_conf : auth_conf = ac_levels_some pattern_KNpsk2

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_KKpsk0_auth_conf : auth_conf = ac_levels_some pattern_KKpsk0

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_KKpsk2_auth_conf : auth_conf = ac_levels_some pattern_KKpsk2

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_KXpsk2_auth_conf : auth_conf = ac_levels_some pattern_KXpsk2

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_INpsk1_auth_conf : auth_conf = ac_levels_some pattern_INpsk1

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_INpsk2_auth_conf : auth_conf = ac_levels_some pattern_INpsk2

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_IKpsk1_auth_conf : auth_conf = ac_levels_some pattern_IKpsk1

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_IKpsk2_auth_conf : auth_conf = ac_levels_some pattern_IKpsk2

[@(T.postprocess_with pp_normalize_print_tac)]
inline_for_extraction noextract
let pattern_IXpsk2_auth_conf : auth_conf = ac_levels_some pattern_IXpsk2

(*
// TODO: update this
/// Making the result of the normalization visible to the user - for reference
/// and documentation
let _ = assert_norm(pattern_Npsk0_auth_conf = ([1], [2]))
let _ = assert_norm(pattern_Kpsk0_auth_conf = ([1], [2]))
let _ = assert_norm(pattern_Xpsk1_auth_conf = ([1], [2]))
let _ = assert_norm(pattern_NNpsk0_auth_conf = ([1; 1; 1; 1], [2; 4; 4; 4]))
let _ = assert_norm(pattern_NNpsk2_auth_conf = ([0; 1; 1; 1], [0; 3; 4; 4]))
let _ = assert_norm(pattern_NKpsk0_auth_conf = ([1; 2; 1; 2], [2; 4; 5; 4]))
let _ = assert_norm(pattern_NKpsk2_auth_conf = ([0; 2; 1; 2], [2; 3; 5; 4]))
let _ = assert_norm(pattern_NXpsk2_auth_conf = ([0; 2; 1; 2], [0; 3; 5; 4]))
let _ = assert_norm(pattern_XNpsk3_auth_conf = ([0; 0; 2; 1; 2], [0; 1; 3; 5; 4]))
let _ = assert_norm(pattern_XKpsk3_auth_conf = ([0; 2; 2; 2; 2], [2; 1; 5; 5; 5]))
let _ = assert_norm(pattern_XXpsk3_auth_conf = ([0; 2; 2; 2; 2], [0; 1; 5; 5; 5]))
let _ = assert_norm(pattern_KNpsk0_auth_conf = ([1; 1; 2; 1], [2; 4; 4; 5]))
let _ = assert_norm(pattern_KNpsk2_auth_conf = ([0; 1; 2; 1], [0; 3; 4; 5]))
let _ = assert_norm(pattern_KKpsk0_auth_conf = ([1; 2; 2; 2], [2; 4; 5; 5]))
let _ = assert_norm(pattern_KKpsk2_auth_conf = ([1; 2; 2; 2], [2; 4; 5; 5]))
let _ = assert_norm(pattern_KXpsk2_auth_conf = ([0; 2; 2; 2], [0; 3; 5; 5]))
let _ = assert_norm(pattern_INpsk1_auth_conf = ([1; 1; 2; 1], [2; 4; 4; 5]))
let _ = assert_norm(pattern_INpsk2_auth_conf = ([0; 1; 2; 1], [0; 3; 4; 5]))
let _ = assert_norm(pattern_IKpsk1_auth_conf = ([1; 2; 2; 2], [2; 4; 5; 5]))
let _ = assert_norm(pattern_IKpsk2_auth_conf = ([1; 2; 2; 2], [2; 4; 5; 5]))
let _ = assert_norm(pattern_IXpsk2_auth_conf = ([0; 2; 2; 2], [0; 3; 5; 5]))

(*
pattern_N: [0], [2]
pattern_K: [1], [2]
pattern_X: [1], [2]
pattern_NN: [0; 0; 0; 0], [0; 1; 1; 1]
pattern_NK: [0; 2; 0; 2], [2; 1; 5; 1]
pattern_NX: [0; 2; 0; 2], [0; 1; 5; 1]
pattern_XN: [0; 0; 2; 0; 2], [0; 1; 1; 5; 1]
pattern_XK: [0; 2; 2; 2; 2], [2; 1; 5; 5; 5]
pattern_XX: [0; 2; 2; 2; 2], [0; 1; 5; 5; 5]
pattern_KN: [0; 0; 2; 0], [0; 3; 1; 5]
pattern_KK: [1; 2; 2; 2], [2; 4; 5; 5]
pattern_KX: [0; 2; 2; 2], [0; 3; 5; 5]
pattern_IN: [0; 0; 2; 0], [0; 3; 1; 5]
pattern_IK: [1; 2; 2; 2], [2; 4; 5; 5]
pattern_IX: [0; 2; 2; 2], [0; 3; 5; 5]
pattern_NK1: [0; 2; 0; 2], [0; 1; 5; 1]
pattern_NX1: [0; 0; 0; 2; 0], [0; 1; 3; 1; 5]
pattern_X1N: [0; 0; 0; 0; 2; 0], [0; 1; 1; 3; 1; 5]
pattern_X1K: [0; 2; 0; 2; 2; 2], [2; 1; 5; 3; 5; 5]
pattern_XK1: [0; 2; 2; 2; 2], [0; 1; 5; 5; 5]
pattern_X1K1: [0; 2; 0; 2; 2; 2], [0; 1; 5; 3; 5; 5]
pattern_X1X: [0; 2; 0; 2; 2; 2], [0; 1; 5; 3; 5; 5]
pattern_XX1: [0; 0; 2; 2; 2], [0; 1; 3; 5; 5]
pattern_X1X1: [0; 0; 0; 2; 2; 2], [0; 1; 3; 3; 5; 5]
pattern_K1N: [0; 0; 2; 0; 2], [0; 1; 1; 5; 1]
pattern_K1K: [0; 2; 2; 2; 2], [2; 1; 5; 5; 5]
pattern_KK1: [0; 2; 2; 2], [0; 3; 5; 5]
pattern_K1K1: [0; 2; 2; 2; 2], [0; 1; 5; 5; 5]
pattern_K1X: [0; 2; 2; 2; 2], [0; 1; 5; 5; 5]
pattern_KX1: [0; 0; 2; 2; 2], [0; 3; 3; 5; 5]
pattern_K1X1: [0; 0; 2; 2; 2], [0; 1; 3; 5; 5]
pattern_I1N: [0; 0; 2; 0; 2], [0; 1; 1; 5; 1]
pattern_I1K: [0; 2; 2; 2; 2], [2; 1; 5; 5; 5]
pattern_IK1: [0; 2; 2; 2], [0; 3; 5; 5]
pattern_I1K1: [0; 2; 2; 2; 2], [0; 1; 5; 5; 5]
pattern_I1X: [0; 2; 2; 2; 2], [0; 1; 5; 5; 5]
pattern_IX1: [0; 0; 2; 2; 2], [0; 3; 3; 5; 5]
pattern_I1X1: [0; 0; 2; 2; 2], [0; 1; 3; 5; 5]
pattern_Npsk0: [1], [2]
pattern_Kpsk0: [1], [2]
pattern_Xpsk1: [1], [2]
pattern_NNpsk0: [1; 1; 1; 1], [2; 4; 4; 4]
pattern_NNpsk2: [0; 1; 1; 1], [0; 3; 4; 4]
pattern_NKpsk0: [1; 2; 1; 2], [2; 4; 5; 4]
pattern_NKpsk2: [0; 2; 1; 2], [2; 3; 5; 4]
pattern_NXpsk2: [0; 2; 1; 2], [0; 3; 5; 4]
pattern_XNpsk3: [0; 0; 2; 1; 2], [0; 1; 3; 5; 4]
pattern_XKpsk3: [0; 2; 2; 2; 2], [2; 1; 5; 5; 5]
pattern_XXpsk3: [0; 2; 2; 2; 2], [0; 1; 5; 5; 5]
pattern_KNpsk0: [1; 1; 2; 1], [2; 4; 4; 5]
pattern_KNpsk2: [0; 1; 2; 1], [0; 3; 4; 5]
pattern_KKpsk0: [1; 2; 2; 2], [2; 4; 5; 5]
pattern_KKpsk2: [1; 2; 2; 2], [2; 4; 5; 5]
pattern_KXpsk2: [0; 2; 2; 2], [0; 3; 5; 5]
pattern_INpsk1: [1; 1; 2; 1], [2; 4; 4; 5]
pattern_INpsk2: [0; 1; 2; 1], [0; 3; 4; 5]
pattern_IKpsk1: [1; 2; 2; 2], [2; 4; 5; 5]
pattern_IKpsk2: [1; 2; 2; 2], [2; 4; 5; 5]
pattern_IXpsk2: [0; 2; 2; 2], [0; 3; 5; 5]
*)
*)

(*** Extended patterns *)
/// The top API level uses the security levels. For this usage, we define a
/// record for patterns extended with security levels, and instantiate it
/// for all the current patterns.

type sec_handshake_pattern = {
  pattern : hsk:wf_handshake_pattern{Some? (normalize_term(ac_levels hsk))};
  levels : (levels:auth_conf{
    length (fst levels) >= length pattern.messages /\
    levels = ac_levels_some pattern
  }); // security levels
}

let spat_get_pattern (pat : sec_handshake_pattern) : wf_handshake_pattern =
  match pat with
  | Mksec_handshake_pattern pat levels -> pat

let spat_get_levels (pat : sec_handshake_pattern) : auth_conf =
  match pat with
  | Mksec_handshake_pattern pat levels -> levels

let mk_sec_handshake_pattern (pat : wf_handshake_pattern) (levels : auth_conf) :
  Pure sec_handshake_pattern
  (requires (
    Some? (normalize_term(ac_levels pat)) /\
    normalize_term (length (fst levels)) >= normalize_term (length pat.messages) /\
    levels = normalize_term (ac_levels_some pat)))
  (ensures (fun _ -> True)) =
  normalize_term_spec (length (fst levels));
  normalize_term_spec (length pat.messages);
  Mksec_handshake_pattern pat levels

let pattern_N : sec_handshake_pattern = mk_sec_handshake_pattern pattern_N pattern_N_auth_conf
let pattern_K : sec_handshake_pattern = mk_sec_handshake_pattern pattern_K pattern_K_auth_conf
let pattern_X : sec_handshake_pattern = mk_sec_handshake_pattern pattern_X pattern_X_auth_conf
let pattern_NN : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NN pattern_NN_auth_conf
let pattern_NK : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NK pattern_NK_auth_conf
let pattern_NX : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NX pattern_NX_auth_conf
let pattern_XN : sec_handshake_pattern = mk_sec_handshake_pattern pattern_XN pattern_XN_auth_conf
let pattern_XK : sec_handshake_pattern = mk_sec_handshake_pattern pattern_XK pattern_XK_auth_conf
let pattern_XX : sec_handshake_pattern = mk_sec_handshake_pattern pattern_XX pattern_XX_auth_conf
let pattern_KN : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KN pattern_KN_auth_conf
let pattern_KK : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KK pattern_KK_auth_conf
let pattern_KX : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KX pattern_KX_auth_conf
let pattern_IN : sec_handshake_pattern = mk_sec_handshake_pattern pattern_IN pattern_IN_auth_conf
let pattern_IK : sec_handshake_pattern = mk_sec_handshake_pattern pattern_IK pattern_IK_auth_conf
let pattern_IX : sec_handshake_pattern = mk_sec_handshake_pattern pattern_IX pattern_IX_auth_conf
let pattern_NK1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NK1 pattern_NK1_auth_conf
let pattern_NX1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NX1 pattern_NX1_auth_conf
let pattern_X1N : sec_handshake_pattern = mk_sec_handshake_pattern pattern_X1N pattern_X1N_auth_conf
let pattern_X1K : sec_handshake_pattern = mk_sec_handshake_pattern pattern_X1K pattern_X1K_auth_conf
let pattern_XK1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_XK1 pattern_XK1_auth_conf
let pattern_X1K1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_X1K1 pattern_X1K1_auth_conf
let pattern_X1X : sec_handshake_pattern = mk_sec_handshake_pattern pattern_X1X pattern_X1X_auth_conf
let pattern_XX1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_XX1 pattern_XX1_auth_conf
let pattern_X1X1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_X1X1 pattern_X1X1_auth_conf
let pattern_K1N : sec_handshake_pattern = mk_sec_handshake_pattern pattern_K1N pattern_K1N_auth_conf
let pattern_K1K : sec_handshake_pattern = mk_sec_handshake_pattern pattern_K1K pattern_K1K_auth_conf
let pattern_KK1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KK1 pattern_KK1_auth_conf
let pattern_K1K1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_K1K1 pattern_K1K1_auth_conf
let pattern_K1X : sec_handshake_pattern = mk_sec_handshake_pattern pattern_K1X pattern_K1X_auth_conf
let pattern_KX1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KX1 pattern_KX1_auth_conf
let pattern_K1X1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_K1X1 pattern_K1X1_auth_conf
let pattern_I1N : sec_handshake_pattern = mk_sec_handshake_pattern pattern_I1N pattern_I1N_auth_conf
let pattern_I1K : sec_handshake_pattern = mk_sec_handshake_pattern pattern_I1K pattern_I1K_auth_conf
let pattern_IK1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_IK1 pattern_IK1_auth_conf
let pattern_I1K1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_I1K1 pattern_I1K1_auth_conf
let pattern_I1X : sec_handshake_pattern = mk_sec_handshake_pattern pattern_I1X pattern_I1X_auth_conf
let pattern_IX1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_IX1 pattern_IX1_auth_conf
let pattern_I1X1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_I1X1 pattern_I1X1_auth_conf
let pattern_Npsk0 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_Npsk0 pattern_Npsk0_auth_conf
let pattern_Kpsk0 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_Kpsk0 pattern_Kpsk0_auth_conf
let pattern_Xpsk1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_Xpsk1 pattern_Xpsk1_auth_conf
let pattern_NNpsk0 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NNpsk0 pattern_NNpsk0_auth_conf
let pattern_NNpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NNpsk2 pattern_NNpsk2_auth_conf
let pattern_NKpsk0 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NKpsk0 pattern_NKpsk0_auth_conf
let pattern_NKpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NKpsk2 pattern_NKpsk2_auth_conf
let pattern_NXpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_NXpsk2 pattern_NXpsk2_auth_conf
let pattern_XNpsk3 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_XNpsk3 pattern_XNpsk3_auth_conf
let pattern_XKpsk3 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_XKpsk3 pattern_XKpsk3_auth_conf
let pattern_XXpsk3 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_XXpsk3 pattern_XXpsk3_auth_conf
let pattern_KNpsk0 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KNpsk0 pattern_KNpsk0_auth_conf
let pattern_KNpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KNpsk2 pattern_KNpsk2_auth_conf
let pattern_KKpsk0 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KKpsk0 pattern_KKpsk0_auth_conf
let pattern_KKpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KKpsk2 pattern_KKpsk2_auth_conf
let pattern_KXpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_KXpsk2 pattern_KXpsk2_auth_conf
let pattern_INpsk1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_INpsk1 pattern_INpsk1_auth_conf
let pattern_INpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_INpsk2 pattern_INpsk2_auth_conf
let pattern_IKpsk1 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_IKpsk1 pattern_IKpsk1_auth_conf
let pattern_IKpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_IKpsk2 pattern_IKpsk2_auth_conf
let pattern_IXpsk2 : sec_handshake_pattern = mk_sec_handshake_pattern pattern_IXpsk2 pattern_IXpsk2_auth_conf
