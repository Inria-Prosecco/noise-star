module Impl.Noise.PatternMessages.Tactics

module Spec = Spec.Noise
open Spec.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState
open Impl.Noise.SendReceive
open Impl.Noise.RecursivePremessages
open Impl.Noise.RecursiveMessages
open Impl.Noise.FlatStructures
open Impl.Noise.CryptoPrimitives
open Impl.Noise.PatternMessages.Definitions
open Impl.Noise.Extraction

module T = FStar.Tactics
open FStar.Tactics
open FStar.String

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let compile_hski_from_ssdhi (#nc : iconfig) (ssdhi : ssdh_impls nc) :
  Tot (handshake_functions_impls nc) =
  [@inline_let] let hsi = compile_hs_impls ssdhi in
  compile_handshake_functions_impls hsi

#push-options "--ifuel 1"
inline_for_extraction noextract
let generate_hski_declaration (debug : bool) (nc ssdhi : term) (hski_name : string) :
  Tac sigelt =
  let body = `compile_hski_from_ssdhi (`#ssdhi) in
  let ty = `handshake_functions_impls (`#nc) in
  let name = make_cur_module_fv hski_name in
  let params = Some hski_name in
  let lb = pack_lb ({ lb_fv = name; lb_us = []; lb_typ = ty; lb_def = body }) in
  let sg = Sg_Let false [lb] in
  let decl : sigelt = pack_sigelt sg in
  let decl = set_sigelt_quals [ NoExtract; Inline_for_extraction ] decl in
  let decl = set_sigelt_attrs [ `(noextract_to "Karamel") ] decl in
  if debug then print_declaration sg;
  decl
#pop-options

/// The function to be used by the user to generate the declarations of the "basic"
/// Noise functions, used to generate the send/receive (pre) message functions.
noextract
let generate_pattern_declarations
  (debug : bool)
  (#nc : config)
  (impls_params : config_impls_params nc)
  (extract_params : extract_decls_params)
  (iconfig_name handshake_function_impl_name : string) :
  Tac decls =
  let dl, qnc, qssdhi =
    generate_config_declarations debug #nc impls_params extract_params iconfig_name
  in
  let hski_decl =
    generate_hski_declaration debug qnc qssdhi handshake_function_impl_name in
  List.append dl [hski_decl]

(** For debugging [generate_config_declarations]:

let impls_params : config_impls_params Spec.Noise.Instances.wgc =
  ImplCFields.M51, ImplPolyFields.M32, ImplBlake2Core.M32

%splice[dh; aead_encrypt; aead_decrypt; hash; aead_encrypt; aead_decrypt; hski]
(generate_config_declarations true impls_params debug_extract_decls_params "iwgc" "hski")

*)

(**** Normalization *)

let handshake_functions_impls_id = `%handshake_functions_impls

let cimpl_st_ids = [
  `%initialize_st;
  `%initialize_from_lists_st;
  `%csend_premessage_st;
  `%creceive_premessage_st;
  `%csend_message_st;
  `%creceive_message_st;
]

let cimpl_m_ids = [
  `%initialize_m;
  `%initialize_from_lists_m;
  `%csend_premessage_m;
  `%creceive_premessage_m;
  `%csend_message_m;
  `%creceive_message_m
]

(* So far the only match branch we really need is the [Tv_App] *)
noextract
let find_hski_instances (debug : bool) (e : env) (t : term) : Tac (list string) =
  find_typed_instances debug [handshake_functions_impls_id] 1 e t

noextract
let cimpl_getters_ids = [
  `%initialize;
  `%initialize_from_lists;
  `%csend_premessage;
  `%creceive_premessage;
  `%csend_message;
  `%creceive_message;
  `%cset_psk;

  `%compile_hski_from_ssdhi;
  `%compile_hs_impls;
  `%compile_handshake_functions_impls;

  `%hsi_get_ssdhi;
  `%hsi_get_initialize_handshake_state;
  `%hsi_get_send_premessage_tokens;
  `%hsi_get_receive_premessage_tokens;
  `%hsi_get_send_message_tokens_with_payload;
  `%hsi_get_receive_message_tokens_with_payload;
]

noextract
let simplify_hski_impl_getter (debug : bool) () : Tac unit =
  simplify_impl_getter debug handshake_functions_impls_id cimpl_getters_ids ()

noextract
let unfold_impl_function (debug : bool) () : Tac unit =
  print_dbg debug "[> Start: unfold_impl_function";
  let g = cur_goal () in
  let e = cur_env () in
  print_dbg debug (term_to_string g);
  begin match term_as_formula g with
  | Comp (Eq _) l r ->
    (* Unfold the function which should have been revealed by [simplify_impl_getter]
     * so that we can perform additional simplifications (for recursive functions
     * for instance) *)
    let inames = find_typed_instances debug cimpl_st_ids 1 e l in
    let simpl_ids = List.append inames cimpl_m_ids in
    norm [delta_only simpl_ids]
  | _ -> ()
  end;
  print_dbg debug "[> End: unfold_impl_function"

(* The functions which pick the msg pattern from the handshake pattern *)
let msg_pat_getters_ids = [
  `%get_premessage;
  `%opt_list_to_list_or_empty;
  `%get_message;
  `%List.Tot.index;
  `%List.Tot.hd;
  `%List.Tot.tl;
  `%List.Tot.tail
]

let simpl_msg_pat_getters_ids = List.append msg_pat_getters_ids proj_ids

(* The functions meta combinators which we want to unfold so that the extracted
 * code doesn't use recursive functions *)

(* First layer of wrappers - once unfolded, the pattern getters are revealed
 * and need to be normalized *)
let impl_m_nrec_ids1 = [
  `%csend_premessage_cm;
  `%csend_premessage_m;
  `%creceive_premessage_cm;
  `%creceive_premessage_m;
  `%csend_message_cm;
  `%csend_message_m;
  `%creceive_message_cm;
  `%creceive_message_m;
]

(* Second layer of wrappers - once unfolded, the recursive send/receive message
 * functions are revealed  *)
let impl_m_nrec_ids2 = [
  `%csend_premessage_m_aux;
  `%creceive_premessage_m_aux;
  `%csend_message_m_aux;
  `%creceive_message_m_aux;

  `%send_message_tokens_with_payload_m;
  `%receive_message_tokens_with_payload_m;
  `%receive_message_tokens_nout_with_payload_m;
]

(* Recursive functions *)
let impl_m_rec_ids = [
  `%send_premessage_tokens_m;
  `%receive_premessage_tokens_m;
  `%send_message_tokens_m;
  `%receive_message_tokens_nout_m
]

(* The following tactic unfolds the recursive Noise functions we want to make
 * disappear *)
noextract
let unfold_recursive_functions (debug : bool) () : Tac unit =
  print_dbg debug "[> Start: unfold_recursive_functions";

  (* Unfold the first layer of wrappers so as to reveal the pattern getters *)
  print_dbg debug ("[> unfold_recursive_functions: goal 1:\n" ^
                   term_to_string (cur_goal ()));
  print_dbg debug "[> unfold_recursive_functions: T.norm: 1";
  T.norm [delta_only impl_m_nrec_ids1; iota; simplify; primops];

  (* Simplify the pattern getters (functions which pick the message pattern
   * from the handshake pattern *)
  print_dbg debug ("[> unfold_recursive_functions: goal 2:\n" ^
                   term_to_string (cur_goal ()));
  print_dbg debug "[> unfold_recursive_functions: T.norm: 2";
  T.norm [zeta; delta_only simpl_msg_pat_getters_ids; iota; simplify; primops];

  (* Unfold the second layer of wrappers to reveal the recursive send/receive
   * message functions. Note that because of the tuples deconstruction for the
   * mstate, some of the functions to unfold should be inside a match: we thus
   * need to use zeta_full *)
  print_dbg debug ("[> unfold_recursive_functions: goal 3:\n" ^
                   term_to_string (cur_goal ()));
  print_dbg debug "[> unfold_recursive_functions: T.norm: 3";
  T.norm [zeta_full; delta_only impl_m_nrec_ids2; iota; simplify; primops];

  (* Flatten the recursive call *)
  print_dbg debug ("[> unfold_recursive_functions: goal 4:\n" ^
                   term_to_string (cur_goal ()));
  print_dbg debug "[> unfold_recursive_functions: T.norm: 4";
  T.norm [zeta_full; delta_only impl_m_rec_ids; iota; simplify; primops];

  print_dbg debug "[> End: unfold_recursive_functions"

(* Tactic to postprocess an instantiated Noise function *)
noextract
let pp_hsk_def_debug (debug : bool) : Tac unit =
  normalize_pattern debug ();
  simplify_hski_impl_getter debug ();
  unfold_impl_function debug ();
  unfold_recursive_functions debug ();
  trefl ()

noextract
let pp_hsk_def () : Tac unit =
  pp_hsk_def_debug false
