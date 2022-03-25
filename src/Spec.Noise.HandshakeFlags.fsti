module Spec.Noise.HandshakeFlags
open FStar.Mul

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base

/// The following file implements functions, predicates and lemmas to reason about
/// the availability of the different keys in the handshake (and cipher) state at
/// every step of the handshake. On top of that it also builds pattern
/// well-formedness analysis.

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

let opt_list_to_list_or_empty (#a : Type) (ols : option (list a)) : list a =
  match ols with
  | Some ls -> ls
  | None -> []

(*** Handshake pattern flags *)
(**** Definition, initialization *)
// TODO: remove handshake_pattern_flags and replace its use by handshake_state_flags
inline_for_extraction //noextract
type handshake_pattern_flags = {
  hsk_pis : bool;
  hsk_pie : bool;
  hsk_prs : bool;
  hsk_pre : bool;
  hsk_is : bool;
  hsk_ie : bool;
  hsk_rs : bool;
  hsk_re : bool;
  hsk_ss : bool;
  hsk_ee : bool;
  hsk_se : bool;
  hsk_es : bool;
  hsk_psk : bool;
}

inline_for_extraction noextract
let handshake_pattern_cleared_flags = {
  hsk_pis = false; hsk_pie = false; hsk_prs = false; hsk_pre = false;
  hsk_is = false; hsk_ie = false; hsk_rs = false; hsk_re = false;
  hsk_ss = false; hsk_ee = false; hsk_se = false; hsk_es = false; hsk_psk = false;
}

let hsk_flags_same_pre_flags (f1 f2 : handshake_pattern_flags) : bool =
  f2.hsk_pis = f1.hsk_pis && f2.hsk_pie = f1.hsk_pie &&
  f2.hsk_prs = f1.hsk_prs && f2.hsk_pre = f1.hsk_pre

/// Hskf is monotonous
let hskf_less_than (hskf0 hskf1 : handshake_pattern_flags) : Tot bool =  
  (hskf1.hsk_pis || (not hskf0.hsk_pis)) &&
  (hskf1.hsk_pie || (not hskf0.hsk_pie)) &&
  (hskf1.hsk_prs || (not hskf0.hsk_prs)) &&
  (hskf1.hsk_pre || (not hskf0.hsk_pre)) &&
  (hskf1.hsk_is || (not hskf0.hsk_is)) &&
  (hskf1.hsk_ie || (not hskf0.hsk_ie)) &&
  (hskf1.hsk_rs || (not hskf0.hsk_rs)) &&
  (hskf1.hsk_re || (not hskf0.hsk_re)) &&
  (hskf1.hsk_ss || (not hskf0.hsk_ss)) &&
  (hskf1.hsk_ee || (not hskf0.hsk_ee)) &&
  (hskf1.hsk_se || (not hskf0.hsk_se)) &&
  (hskf1.hsk_es || (not hskf0.hsk_es)) &&
  (hskf1.hsk_psk || (not hskf0.hsk_psk))


(**** Compute over premessages *)
let hsk_flags_same_msg_flags (f1 f2 : handshake_pattern_flags) : bool =
  f2.hsk_is = f1.hsk_is && f2.hsk_ie = f1.hsk_ie &&
  f2.hsk_rs = f1.hsk_rs && f2.hsk_re = f1.hsk_re &&
  f2.hsk_ss = f1.hsk_ss && f2.hsk_ee = f1.hsk_ee &&
  f2.hsk_se = f1.hsk_se && f2.hsk_es = f1.hsk_es &&
  f2.hsk_psk = f1.hsk_psk

let compute_hsk_pretoken_flags (ir : bool) (f : handshake_pattern_flags)
                               (tk : premessage_token) :
  Tot (f':handshake_pattern_flags{hsk_flags_same_msg_flags f f'}) =
  match tk with
  | PS -> if ir then { f with hsk_pis = true } else { f with hsk_prs = true }
  | PE -> if ir then { f with hsk_pie = true } else { f with hsk_pre = true }

(* Rk.: initially defined with fold_left. Proved cumbersome later because of
 * the type refinement (see the remark for compute_hsk_msg_flags) *)
[@(strict_on_arguments [2])]
let rec compute_hsk_premessage_flags (ir : bool) (f : handshake_pattern_flags)
                                     (pattern : list premessage_token) :
  Tot (f':handshake_pattern_flags{hsk_flags_same_msg_flags f f'})
  (decreases pattern) =
  match pattern with
  | [] -> f
  | tk :: pattern' ->
    let f' = compute_hsk_pretoken_flags ir f tk in
    compute_hsk_premessage_flags ir f' pattern'

(**** Compute over messages *)
let compute_hsk_token_flags
  (ir : bool)
  (f : handshake_pattern_flags)
  (tk : message_token) :
  (f':handshake_pattern_flags{hsk_flags_same_pre_flags f f'}) =
  begin match tk with
  | S -> if ir then { f with hsk_is = true } else { f with hsk_rs = true }
  | E -> if ir then { f with hsk_ie = true } else { f with hsk_re = true }
  | SS -> { f with hsk_ss = true }
  | EE -> { f with hsk_ee = true }
  | SE -> { f with hsk_se = true }
  | ES -> { f with hsk_es = true }
  | PSK -> { f with hsk_psk = true }
  end

(* Rk.: the initial implementation used [fold_left] and no recursion,
 * but it proved cumbersome to later prove properties about this function.
 * The reason is that we had to cast [compute_hsk_token_flags] to a function
 * with a richer types, forcing us to deal with function equalities later on. *)
// TODO: rewrite using the compute_hsk_msg_flags_at_step...
[@(strict_on_arguments [2])]
let rec compute_hsk_msg_flags (ir : bool) (f : handshake_pattern_flags)
                              (pattern : list message_token) :
  Tot (f':handshake_pattern_flags{hsk_flags_same_pre_flags f f'})
  (decreases pattern) =
  match pattern with
  | [] -> f
  | tk :: pattern' ->
    let f' = compute_hsk_token_flags ir f tk in
    compute_hsk_msg_flags ir f' pattern'

// TODO: if we add strict_on_arguments, [Impl.Noise.API.State.StateMachine.check_pattern]
// doesn't reduce on [Spec.Noise.Patterns.pattern_NNpsk0]
//[@(strict_on_arguments [2])]
let rec compute_hsk_msgs_flags_aux (ir : bool) (f : handshake_pattern_flags)
                                   (msgs : list (list message_token)) :
  Tot (f':handshake_pattern_flags{hsk_flags_same_pre_flags f f'})
  (decreases msgs) =
  match msgs with
  | [] -> f
  | pattern :: msgs' ->
    let f' = compute_hsk_msg_flags ir f pattern in
    compute_hsk_msgs_flags_aux (not ir) f' msgs'

noextract
let compute_hsk_msgs_flags =
    compute_hsk_msgs_flags_aux true

[@(strict_on_arguments [0])]
let compute_hsk_pre_msgs_flags (hsk : handshake_pattern) :
  (f:handshake_pattern_flags{hsk_flags_same_msg_flags f handshake_pattern_cleared_flags}) =
  let hskf0 = handshake_pattern_cleared_flags in
  let hskf1 = match hsk.premessage_ir with
              Some pre -> compute_hsk_premessage_flags true hskf0 pre | None -> hskf0 in
  let hskf2 = match hsk.premessage_ri with
              Some pre -> compute_hsk_premessage_flags false hskf1 pre | None -> hskf1 in
  hskf2

// TODO: test with [0;1]: sometimes strict on a nat causes problems
[@(strict_on_arguments [0])]
let rec compute_hsk_flags_at_step
  (hsk : handshake_pattern) (i : nat{i <= List.Tot.length hsk.messages}) :
  Tot handshake_pattern_flags =
  if i = 0 then compute_hsk_pre_msgs_flags hsk
  else
    let ir = ((i-1)%2=0) in
    let f0 = compute_hsk_flags_at_step hsk (i-1) in
    let tokens = List.Tot.index hsk.messages (i-1) in
    compute_hsk_msg_flags ir f0 tokens

[@(strict_on_arguments [0])]
let compute_hsk_flags (hsk : handshake_pattern) : handshake_pattern_flags =
  let hskf = compute_hsk_pre_msgs_flags hsk in
  compute_hsk_msgs_flags hskf hsk.messages

(**** Facility functions *)
//[@(strict_on_arguments [0])]
let hskf_uses_is (hskf : handshake_pattern_flags) : bool =
  hskf.hsk_pis || hskf.hsk_is || hskf.hsk_ss || hskf.hsk_se

//[@(strict_on_arguments [0])]
let hskf_uses_ie (hskf : handshake_pattern_flags) : bool =
  hskf.hsk_pie || hskf.hsk_ie || hskf.hsk_es || hskf.hsk_ee

//[@(strict_on_arguments [0])]
let hskf_uses_rs (hskf : handshake_pattern_flags) : bool =
  hskf.hsk_prs || hskf.hsk_rs || hskf.hsk_ss || hskf.hsk_es

//[@(strict_on_arguments [0])]
let hskf_uses_re (hskf : handshake_pattern_flags) : bool =
  hskf.hsk_pre || hskf.hsk_re || hskf.hsk_se || hskf.hsk_ee

// Did the operations observed so far lead to the derivation of a symmetric key
let hskf_has_sk (is_psk : bool) (hskf : handshake_pattern_flags) : bool =
  hskf.hsk_ee || hskf.hsk_ss || hskf.hsk_se || hskf.hsk_es
  || (is_psk && hskf.hsk_ie) || (is_psk && hskf.hsk_re)

(**** Consistency lemmas *)
val compute_hsk_msg_flags_psk_exists_lem
  (ir : bool) (f : handshake_pattern_flags)
  (msg : list message_token) :
  Lemma
  (ensures (
    compute_hsk_msg_flags ir f msg).hsk_psk <==>
      (f.hsk_psk \/ List.Tot.mem PSK msg))
  (decreases msg)

val compute_hsk_msg_flags_aux_psk_exists_lem
  (ir : bool) (f : handshake_pattern_flags)
  (msgs : list(list message_token)) :
  Lemma
  (ensures (compute_hsk_msgs_flags_aux ir f msgs).hsk_psk <==>
      (f.hsk_psk \/ List.existsb (List.Tot.mem PSK) msgs))
  (decreases msgs)

val compute_hsk_flags_consistent_with_check_hsk_is_psk_lem
  (hsk : handshake_pattern) :
  Lemma((compute_hsk_flags hsk).hsk_psk == Spec.Noise.Base.check_hsk_is_psk hsk)

(**** Monotonicity lemmas *)
val compute_hsk_token_flags_is_increasing (ir : bool)
                                          (hskf0 : handshake_pattern_flags)
                                          (tk : message_token) :
  Lemma
  (requires True)
  (ensures(
    let hskf1 = compute_hsk_token_flags ir hskf0 tk in
    hskf0 `hskf_less_than` hskf1))

val compute_hsk_msg_flags_is_increasing (ir : bool)
                                        (hskf0 : handshake_pattern_flags)
                                        (msg : list message_token) :
  Lemma
  (requires True)
  (ensures(
    let hskf1 = compute_hsk_msg_flags ir hskf0 msg in
    hskf0 `hskf_less_than` hskf1))
  (decreases msg)

val compute_hsk_msgs_flags_aux_is_increasing (ir : bool)
                                             (hskf0 : handshake_pattern_flags)
                                             (msgs : list (list message_token)) :
  Lemma
  (requires True)
  (ensures(
    let hskf1 = compute_hsk_msgs_flags_aux ir hskf0 msgs in
    hskf0 `hskf_less_than` hskf1))
  (decreases msgs)

(**** Check if is psk (version 2) *)
[@(strict_on_arguments [0])]
let chskf_check_is_psk (hsk : handshake_pattern) : b:bool{b = check_hsk_is_psk hsk} =
  let hskf = compute_hsk_flags hsk in
  (**) compute_hsk_flags_consistent_with_check_hsk_is_psk_lem hsk;
  hskf.hsk_psk

(*** Symmetric key flag *)
(**** Definitions *)
inline_for_extraction noextract
let token_update_sym_key_flag (has_sym_key is_psk : bool) (tk : message_token) :
  Tot (b:bool{b || not has_sym_key}) =
  match tk with
  | S -> has_sym_key
  | E -> has_sym_key || is_psk
  | _ -> true

[@(strict_on_arguments [2])]
inline_for_extraction noextract
let rec tokens_update_sym_key_flag
  (has_sym_key : bool) (is_psk : bool)
  (pattern : list message_token) :
  Tot (b:bool{b || not has_sym_key}) (decreases pattern) =
  match pattern with
  | [] -> has_sym_key
  | tk :: pattern' ->
    let has_sym_key' = token_update_sym_key_flag has_sym_key is_psk tk in
    tokens_update_sym_key_flag has_sym_key' is_psk pattern'

(**** Update lemmas *)
val send_message_token_has_sym_key_lem (#nc : config)
                                       (initiator is_psk : bool)
                                       (tk : message_token)
                                       (st : handshake_state nc) :
  Lemma(
    match send_message_token initiator is_psk tk st with
    | Fail _ -> True
    | Res (_, st') ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = Some? st'.sym_state.c_state.k in
      has_sym_key' == token_update_sym_key_flag has_sym_key is_psk tk)

val send_message_tokens_has_sym_key_lem
  (#nc : config) (initiator is_psk : bool) (pattern : list message_token)
  (st : handshake_state nc) :
  Lemma(
    match send_message_tokens initiator is_psk pattern st with
    | Fail _ -> True
    | Res (_, st') ->
      let has_sym_key = Some? st.sym_state.c_state.k in
      let has_sym_key' = Some? st'.sym_state.c_state.k in
      has_sym_key' == tokens_update_sym_key_flag has_sym_key is_psk pattern)

val tokens_update_sym_key_flag_decompose_lem (has_sym_key is_psk : bool)
                                             (tokens1 tokens2 : list message_token) :
  Lemma
  (requires True)
  (ensures (
    let sk1 = tokens_update_sym_key_flag has_sym_key is_psk tokens1 in
    let sk2 = tokens_update_sym_key_flag sk1 is_psk tokens2 in
    let sk2' = tokens_update_sym_key_flag has_sym_key is_psk (List.Tot.append tokens1 tokens2) in
    sk2' = sk2))
  (decreases tokens1)

(*** Handshake state flags *)
(* The [handshake_state_flags] structure is used to reason about the keys
 * stored in a handshake_state. *)
inline_for_extraction //noextract
type handshake_state_flags = {
  sk : bool;
  s : bool;
  e : bool;
  rs : bool;
  re : bool;
  psk : bool;
}

inline_for_extraction //noextract
let handshake_state_cleared_flags = {
  sk = false; s = false; e = false; rs = false; re = false; psk = false;
}

inline_for_extraction //noextract
let hsf_from_initialize (s e psk : bool) =
  { sk = false; s = s; e = e; rs = false; re = false; psk = psk; }

/// [handshake_state_flags] is monotonous over a handshake execution
noextract
let less_than (hsf1 hsf2 : handshake_state_flags) : Tot bool =
  (hsf2.sk || not hsf1.sk) && (hsf2.s || not hsf1.s) && (hsf2.e || not hsf1.e) &&
  (hsf2.rs || not hsf1.rs) && (hsf2.re || not hsf1.re) && (hsf2.psk || not hsf1.psk)

inline_for_extraction noextract
type greater_hsf (hsf0:handshake_state_flags) =
  hsf1:handshake_state_flags{less_than hsf0 hsf1}

noextract
let has_pretoken (f : handshake_state_flags) (tk : premessage_token) : Tot bool =
  match tk with
  | PS -> f.s
  | PE -> f.e

let has_pretokens (f : handshake_state_flags) (pattern : list premessage_token) :
  Tot bool =
  List.Tot.for_all (has_pretoken f) pattern


(**** Compute over premessage *)
noextract
let receive_pretoken_update_hsf (tk : premessage_token) (hsf : handshake_state_flags) :
  handshake_state_flags =
  match tk with
  | PS -> { hsf with rs = true }
  | PE -> { hsf with re = true }

//[@(strict_on_arguments [0])] // TODO: check
noextract
let rec receive_premessage_update_hsf (pattern : list premessage_token)
                                      (hsf : handshake_state_flags) :
  hsf':greater_hsf hsf {
    hsf'.sk == hsf.sk /\ hsf'.s == hsf.s /\ hsf'.e == hsf.e /\ hsf'.psk == hsf.psk} =
  match pattern with
  | [] -> hsf
  | tk :: pattern' ->
    let hsf' = receive_pretoken_update_hsf tk hsf in
    receive_premessage_update_hsf pattern' hsf'

noextract
let send_pretoken_update_hsf (tk : premessage_token) (hsf : handshake_state_flags) :
  handshake_state_flags =
  match tk with
  | PS -> { hsf with s = true }
  | PE -> { hsf with e = true }

//[@(strict_on_arguments [0])] // TODO: check
noextract
let rec send_premessage_update_hsf (pattern : list premessage_token)
                                   (hsf : handshake_state_flags) :
  hsf':greater_hsf hsf {
    hsf'.sk == hsf.sk /\ hsf'.rs == hsf.rs /\ hsf'.re == hsf.re /\ hsf'.psk == hsf.psk} =
  match pattern with
  | [] -> hsf
  | tk :: pattern' ->
    let hsf' = send_pretoken_update_hsf tk hsf in
    send_premessage_update_hsf pattern' hsf'

/// Compute the smi corresponding to the key consumption in the premessages
// TODO: move
let compute_consume_premessages_hsf (hsk : handshake_pattern) (initiator : bool) :
  handshake_state_flags =
  let hsf0 = handshake_state_cleared_flags in
  let hsf1 =
    match hsk.premessage_ir with
    | None -> hsf0
    | Some pre ->
      if initiator then send_premessage_update_hsf pre hsf0
      else receive_premessage_update_hsf pre hsf0
  in
  let hsf2 =
    match hsk.premessage_ri with
    | None -> hsf0
    | Some pre ->
      if initiator then receive_premessage_update_hsf pre hsf1
      else send_premessage_update_hsf pre hsf1
  in
  hsf2

(**** Compute over message *)
inline_for_extraction noextract
let send_token_update_hsf (is_psk : bool) (tk : message_token)
                          (hsf : handshake_state_flags) :
  Tot (greater_hsf hsf) =
  { hsf with sk = token_update_sym_key_flag hsf.sk is_psk tk }

inline_for_extraction noextract
let receive_token_update_hsf (is_psk : bool) (tk : message_token)
                             (hsf : handshake_state_flags) :
  Tot (greater_hsf hsf) =
  match tk with
  | S -> { hsf with rs = true }
  | E -> { hsf with sk = hsf.sk || is_psk; re = true }
  | _ -> { hsf with sk = true }

inline_for_extraction noextract
let token_update_hsf (is_psk sender : bool) (tk : message_token)
                     (hsf : handshake_state_flags) :
  Tot (greater_hsf hsf) =
  if sender then send_token_update_hsf is_psk tk hsf
            else receive_token_update_hsf is_psk tk hsf

// Don't put strict_on_arguments here: it causes type inference to
// loop in [Impl.Noise.RecursiveMessages.send_message_tokens_m]
inline_for_extraction noextract
let send_tokens_update_hsf (is_psk : bool) (pattern : list message_token)
                           (hsf : handshake_state_flags) :
  greater_hsf hsf =
  let sk1 = tokens_update_sym_key_flag hsf.sk is_psk pattern in
  { hsf with sk = sk1 }

[@(strict_on_arguments [1])]
inline_for_extraction noextract
let rec receive_tokens_update_hsf
  (is_psk : bool) (pattern : list message_token) (hsf : handshake_state_flags) :
  Tot
  (hsf':greater_hsf hsf {
    hsf'.s == hsf.s /\ hsf'.e == hsf.e /\ hsf'.psk == hsf.psk})
  (decreases pattern) =
  match pattern with
  | [] -> hsf
  | tk :: pattern' ->
    let hsf' = receive_token_update_hsf is_psk tk hsf in
    receive_tokens_update_hsf is_psk pattern' hsf'

val updt_sk_consistent_with_receive_tokens_update_hsf_lem
  (is_psk : bool) (pattern : list message_token) (hsf : handshake_state_flags) :
  Lemma(let hsf' = receive_tokens_update_hsf is_psk pattern hsf in
        tokens_update_sym_key_flag hsf.sk is_psk pattern == hsf'.sk)

(**** Decomposition lemmas *)
val receive_tokens_update_hsf_decompose_lem (is_psk : bool)
                                            (tokens1 tokens2 : list message_token)
                                            (hsf : handshake_state_flags) :
  Lemma
  (requires True)
  (ensures (
    let hsf1 = receive_tokens_update_hsf is_psk tokens1 hsf in
    let hsf2 = receive_tokens_update_hsf is_psk tokens2 hsf1 in
    let hsf2' = receive_tokens_update_hsf is_psk (List.Tot.append tokens1 tokens2) hsf in
    hsf2' = hsf2))
  (decreases tokens1)

(**** Frame lemmas *)
(** We can set the psk later than initialization with no influence on
  * handshake_state_flags (besides the psk field) *)
val receive_pretoken_update_hsf_frame_lem (tk : premessage_token)
                                          (hsf : handshake_state_flags) :
  Lemma(forall sk s e psk.
          receive_pretoken_update_hsf tk ({ hsf with sk = sk; s = s; e = e; psk = psk }) ==
            { receive_pretoken_update_hsf tk hsf with sk = sk; s = s; e = e; psk = psk })

val receive_premessage_update_hsf_frame_lem (pattern : list premessage_token)
                                            (hsf : handshake_state_flags) :
  Lemma(forall sk s e psk.
          receive_premessage_update_hsf pattern
                              ({ hsf with sk = sk; s = s; e = e; psk = psk }) ==
            { receive_premessage_update_hsf pattern hsf
              with sk = sk; s = s; e = e; psk = psk })

val receive_token_update_hsf_frame_lem (is_psk : bool) (tk : message_token)
                                       (hsf : handshake_state_flags) :
  Lemma(
    forall s e psk.
    receive_token_update_hsf is_psk tk ({ hsf with s = s; e = e; psk = psk; }) ==
      { receive_token_update_hsf is_psk tk hsf with s = s; e = e; psk = psk; })

val receive_tokens_update_hsf_frame_lem (is_psk : bool)
                                        (pattern : list message_token)
                                        (hsf : handshake_state_flags) :
  Lemma(
    forall s e psk.
    receive_tokens_update_hsf is_psk pattern ({ hsf with s = s; e = e; psk = psk; }) ==
      { receive_tokens_update_hsf is_psk pattern hsf with s = s; e = e; psk = psk; })

(**** PSK flag equality lemmas *)
val send_receive_tokens_update_hsf_same_sk_lem
  (is_psk : bool)
  (shsf rhsf : handshake_state_flags)
  (msg : list message_token) :
  Lemma
  (requires (shsf.sk == rhsf.sk))
  (ensures(
   let shsf1 = send_tokens_update_hsf is_psk msg shsf in
   let rhsf1 = receive_tokens_update_hsf is_psk msg rhsf in
   shsf1.sk == rhsf1.sk))
  (decreases msg)
