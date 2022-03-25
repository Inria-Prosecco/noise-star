module Impl.Noise.HandshakeState

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence
open Lib.ByteSequence

module B = LowStar.Buffer
open Lib.Buffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Meta.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF
open Impl.Noise.SymmetricState
open Impl.Noise.TypeOrUnit

friend Spec.Noise.Base.Definitions

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

(* Align the .fst and the .fsti *)
let _align_beg = ()

(*** Initialization *)
// TODO: move. Note that there are functions with the same name in Impl.Noise.Types (those from Impl.Noise.Types will be removed)
inline_for_extraction noextract
val update_sub_opt :
  #a : Type0 ->
  (* Warning: len must be valid for extraction *)
  #len : size_t ->
  #b : bool ->
  dst : lbuffer_or_null a len ->
  src : type_or_unit (lbuffer a len) b ->
  Stack unit
  (requires (fun h ->
    live h dst /\ lbuffer_or_unit_live h src /\
    B.(loc_disjoint (loc_buffer (dst <: buffer a)) (lbuffer_or_unit_loc src)) /\
    (b ==> not (g_is_null dst))))
  (ensures (fun h0 _ h1 ->
    (if not b then modifies0 h0 h1 else modifies1 dst h0 h1) /\
    (if not b then
      (if g_is_null dst then True else h1.[|dst <: lbuffer_t MUT a len|] `S.equal`
                                    h0.[|dst <: lbuffer_t MUT a len|])
     else h1.[|dst <: lbuffer_t MUT a len|] `S.equal` lbuffer_or_unit_to_seq h0 src)))
let update_sub_opt #a #len #b dst src =
  if b then update_sub (dst <: lbuffer_t MUT a len) 0ul len (src <: lbuffer_t MUT a len)
  else ()

inline_for_extraction noextract
val update_keypair_opt :
  #nc : iconfig ->
  #b : bool ->
  dst : keypair_m nc ->
  src_priv : private_key_t_or_unit nc b ->
  src_pub : public_key_t_or_unit nc b ->
  Stack unit
  (requires (fun h ->
    live_kpm h dst /\
    lbuffer_or_unit_live h src_priv /\ lbuffer_or_unit_live h src_pub /\
    disjoint_kpm dst /\
    kpm_loc_disjoint dst (B.loc_union (lbuffer_or_unit_loc src_priv)
                                      (lbuffer_or_unit_loc src_pub)) /\
    ((g_is_null (kpm_get_priv dst) || g_is_null (kpm_get_pub dst)) ==> not b)
    ))
  (ensures (fun h0 _ h1 ->
    (if not b then modifies0 h0 h1
     else modifies (B.loc_union (loc (kpm_get_priv dst)) (loc (kpm_get_pub dst))) h0 h1) /\
    begin
    if b
    then eval_keypair_m h1 dst == Some?.v (keys_t_or_unit_to_keypair h0 src_priv src_pub)
    else True
    end))

let update_keypair_opt #nc #b dst src_priv src_pub =
  if b then
    begin
    update_sub ((kpm_get_priv dst) <: private_key_t nc) 0ul (private_key_vs nc)
               (src_priv <: private_key_t nc);
    update_sub ((kpm_get_pub dst) <: public_key_t nc) 0ul (public_key_vs nc)
               (src_pub <: public_key_t nc)
    end
  else ()

#push-options "--z3rlimit 200 --ifuel 1"
let initialize_handshake_state_m
  #nc ssi pname_len pname prlg_len prlg
  #s_b spriv spub #e_b epriv epub #rs_b rs #re_b re #psk_b psk st =
  [@inline_let] let st_sym_state = hsm_get_sym_state st in
  [@inline_let] let st_static = hsm_get_static st in
  [@inline_let] let st_ephemeral = hsm_get_ephemeral st in
  [@inline_let] let st_remote_static = hsm_get_remote_static st in
  [@inline_let] let st_remote_ephemeral = hsm_get_remote_ephemeral st in
  [@inline_let] let st_preshared = hsm_get_preshared st in
  (**) let h0 = HST.get () in
  (**) let pname_v : Ghost.erased _ = h0.[|pname|] in
  (**) let prologue_v : Ghost.erased _ = h0.[|prlg|] in
  let _ = ssi_get_initialize_symmetric ssi pname_len pname st_sym_state in
  (**) let h1 = HST.get () in
  let _ = ssi_get_mix_hash ssi false prlg_len prlg st_sym_state 0 in
  (**) let h2 = HST.get () in
  (**) assert(ssm_modifies0 st_sym_state h0 h2);
  (**) assert(
  (**)   let sym_st1 = Spec.initialize_symmetric pname_v in
  (**)   let sym_st2 = Spec.mix_hash prologue_v sym_st1 in
  (**)   sym_st2 == eval_symmetric_state_m h2 st_sym_state false 0);
  update_keypair_opt st_static spriv spub;
  update_keypair_opt st_ephemeral epriv epub;
  update_sub_opt st_remote_static rs;
  update_sub_opt st_remote_ephemeral re;
  update_sub_opt st_preshared psk;
  (**) let hf = HST.get () in
  (**) assert(hsm_modifies0 st h0 hf);
  success hash_return_type
#pop-options

(*** Premessages *)
(**** Send premessage *)
inline_for_extraction noextract
val send_premessage_S :
  (#nc : iconfig) ->
  (ssi : ss_impls nc) ->
  (smi : Ghost.erased meta_info) ->
  (st : valid_hsm nc smi) ->
  (out : public_key_t nc) -> 
  Stack (rtype hash_return_type)
  (requires (fun h -> hsm_inv h st smi /\ live h out /\ hsm_disjoint st out /\
                    (**) smi.hsf.s == true (**) /\ get_hash_pre nc))
  (ensures (send_premessage_token_post smi PS st out))

let send_premessage_S #nc ssi smi st out =
  [@inline_let] let k = kpm_get_pub (hsm_get_static st) in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  update_sub out 0ul (public_key_vs nc) k;
  (**) hash_max_input_norm_lem (get_config nc);
  ssi_get_mix_hash ssi smi.hsf.sk (public_key_vs nc) k sym_st smi.nonce

inline_for_extraction noextract
val send_premessage_E :
  (#nc : iconfig) ->
  (ssi : ss_impls nc) ->
  (smi : Ghost.erased meta_info) ->
  (st : valid_hsm nc smi) ->
  (out : public_key_t nc) ->
  Stack (rtype unit_return_type)
  (requires (fun h -> hsm_inv h st smi /\ live h out /\ hsm_disjoint st out /\
                    (**) smi.hsf.e == true (**) ))
  (ensures (send_premessage_token_post smi PE st out))

let send_premessage_E #nc ssi smi st out =
  [@inline_let] let k = kpm_get_pub (hsm_get_ephemeral st) in
  [@inline_let] let sym_st = (hsm_get_sym_state st) in
  update_sub out 0ul (public_key_vs nc) k;
  convert_subtype #unit ()

#push-options "--ifuel 1"
let send_premessage_token_m #nc ssi smi tk st out =
  match tk with
  | PS -> send_premessage_S ssi smi st out
  | PE -> (send_premessage_E ssi smi st out <: rtype unit_return_type)
#pop-options

(**** Receive premessage *)
inline_for_extraction noextract
val receive_premessage_S :
  (#nc : iconfig) ->
  (ssi : ss_impls nc) ->
  (smi : Ghost.erased meta_info) ->
  (st : valid_receive_pretoken_hsm nc PS smi) ->
  (input : public_key_t nc) ->
  Stack (rtype hash_return_type)
  (requires (fun h -> hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
                    (**) smi.hsf.rs == false (**) /\ get_hash_pre nc))
  (ensures (receive_premessage_token_post smi PS st input))

let receive_premessage_S #nc ssi smi st input =
  [@inline_let] let k = hsm_get_remote_static st in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  update_nn k input;
  (**) hash_max_input_norm_lem (get_config nc);
  let _ = ssi_get_mix_hash ssi smi.hsf.sk (public_key_vs nc) input sym_st smi.nonce in
  convert_subtype #unit ()

inline_for_extraction noextract
val receive_premessage_E :
  (#nc : iconfig) ->
  (ssi : ss_impls nc) ->
  (smi : Ghost.erased meta_info) ->
  (st : valid_receive_pretoken_hsm nc PE smi) ->
  (input : public_key_t nc) ->
  Stack (rtype unit_return_type)
  (requires (fun h -> hsm_inv h st smi /\ live h input /\ hsm_disjoint st input /\
                    (**) smi.hsf.re == false (**)))
  (ensures (receive_premessage_token_post smi PE st input))

let receive_premessage_E #nc ssi smi st input =
  [@inline_let] let k = hsm_get_remote_ephemeral st in
  [@inline_let] let sym_st = hsm_get_sym_state st in
  update_nn k input;
  convert_subtype #unit ()  

#push-options "--ifuel 1"
let receive_premessage_token_m #nc ssi smi tk st input =
  match tk with
  | PS -> receive_premessage_S ssi smi st input
  | PE -> (receive_premessage_E ssi smi st input <: rtype unit_return_type)
#pop-options

(*** DH *)
/// Auxiliary function which mixes the key if [r] is equal to zero. Prevents
/// proof explosion in [dh_update].
inline_for_extraction noextract
let dh_update_sym_state_mix_key_ (#nc : iconfig)
                                 (ssi : ss_impls nc)
                                 (has_sym_key : Ghost.erased bool)
                                 (r : rtype dh_return_type)
                                 (k : public_key_t nc)
                                 (sym_st : symmetric_state_m nc)
                                 (nonce : Ghost.erased nat) :
  Stack (rtype dh_hash_return_type)
  (requires (fun h -> ssm_inv h sym_st true /\ live h k /\ ssm_disjoint sym_st k /\
                    get_hash_pre nc))
  (ensures (fun h0 r1 h1 ->
    ssm_modifies0 sym_st h0 h1 /\
    begin
    let sym_st0_v = eval_symmetric_state_m h0 sym_st has_sym_key nonce in
    let sym_st1_v = eval_symmetric_state_m h1 sym_st true 0 in
    match to_prim_error_code r, to_prim_error_code r1 with
    | CSuccess, CSuccess -> sym_st1_v == Spec.mix_key h0.[|k|] sym_st0_v
    | CDH_error, CDH_error -> ss_unchanged sym_st h0 h1
    | _ -> False
    end)) =
  if is_success r then
    let r1 = ssi_get_mix_key ssi has_sym_key k sym_st nonce in
    hash_rtype_to_dh_hash r1
  else dh_rtype_to_dh_hash r

/// For the implementation of dh_update, we use an auxiliary function to prevent
/// proof explosion (because of the dynamic allocation)
inline_for_extraction noextract
val dh_update_sym_state_ :
  #nc : iconfig ->
  ssi : ss_impls nc ->
  msg : Ghost.erased bytes ->
  has_sk : Ghost.erased bool ->
  priv_sec : private_key_t nc ->
  priv_pub : Ghost.erased (public_key_t nc) ->
  pub : public_key_t nc ->
  st : symmetric_state_m nc ->
  nonce : Ghost.erased nat ->
  dh_key : public_key_t nc -> (* destination of the DH product *)
  Stack (rtype dh_hash_return_type)
  (requires (fun h -> dh_update_sym_state_pre msg has_sk priv_sec priv_pub pub st nonce h /\
                    live h dh_key /\ ssm_disjoint st dh_key /\
                    disjoint priv_sec dh_key /\
                    disjoint priv_pub dh_key /\
                    disjoint pub dh_key))
  (ensures (fun h0 r h1 ->
              let priv : keypair_m nc = mk_keypair_m priv_sec priv_pub in
              ssm_modifies1 st dh_key h0 h1 /\
              begin
              let st0_v = eval_symmetric_state_m h0 st has_sk nonce in
              let st1_v = eval_symmetric_state_m h1 st (**) true 0 (**) in
              let r_v = dh_update_sym_state msg (Some (eval_keypair_m h0 priv))
                                           (Some (eval_public_key h0 pub)) st0_v in
              match to_prim_error_code r, r_v with
              | CSuccess, Res (_, st1'_v) -> st1_v == st1'_v
              | CDH_error, Fail DH -> eval_symmetric_state_m h1 st has_sk nonce == st0_v
              | _ -> False
              end))

let dh_update_sym_state_ #nc ssi msg has_sk priv_sec priv_pub pub st nonce dh_key =
  (**) let h0 = HST.get () in
  (* The DH product *)
  let r1 : rtype dh_return_type = idh (ssi_get_prims ssi) dh_key priv_sec pub in
  (**) let h2 = HST.get () in
  (**) assert(
  (**)   match to_prim_error_code r1, Spec.dh #(get_config nc) h0.[|priv_sec|] h0.[|pub|]  with
  (**)   | CSuccess, Some dh_res -> dh_res `S.equal` h2.[|dh_key|]
  (**)   | CDH_error, None -> True
  (**)   | _ -> False
  (**) );
  (* Mix key - we use an auxiliary function to prevent proof explosion *)
  let r2 : rtype dh_hash_return_type =
    dh_update_sym_state_mix_key_ ssi has_sk r1 dh_key st nonce in
  (**) let h3 = HST.get () in
  (**) assert(
  (**)   let sym_st0_v = eval_symmetric_state_m h2 st has_sk nonce in
  (**)   let sym_st1_v = eval_symmetric_state_m h3 st true 0 in
  (**)   match to_prim_error_code r1, to_prim_error_code r2 with
  (**)   | CSuccess, CSuccess -> sym_st1_v == Spec.mix_key h2.[|dh_key|] sym_st0_v
  (**)   | CDH_error, CDH_error -> ss_unchanged st h0 h3);
  (**) assert(
  (**)   eval_symmetric_state_m h2 st has_sk nonce ==
  (**)   eval_symmetric_state_m h0 st has_sk nonce);
  (**) assert(to_prim_error_code r2 == CSuccess \/ to_prim_error_code r2 == CDH_error);
  (**) assert(ssm_modifies1 st dh_key h0 h3);
  r2

let dh_update_sym_state_fm #nc ssi =
  fun msg has_sk sec priv_pub pub cipher_key ck hash nonce ->
  [@inline_let] let st = mk_ssm cipher_key ck hash in
  (**) let h0 = HST.get () in
  push_frame();
  (* Destination for the DH product *)
  let dh_key : public_key_t nc = create (public_key_vs nc) (u8 0) in
  let r = dh_update_sym_state_ ssi msg has_sk sec priv_pub pub st nonce dh_key in
  (* Don't leave any sensitive information on the stack *)
  Lib.Memzero0.memzero #uint8 dh_key (public_key_vs nc);
  pop_frame();
  r

let dh_update_m (#nc : iconfig) (dh_update_impl : dh_update_sym_state_fst nc) :
  dh_update_st nc =
  fun msg smi priv pub st ->
  [@inline_let] let sym_state = hsm_get_sym_state st in
  [@inline_let] let k = csm_get_k (ssm_get_c_state sym_state) in
  dh_update_impl msg smi.hsf.sk (kpm_get_priv priv) (kpm_get_pub priv)
                 pub k (ssm_get_ck sym_state)
                 (ssm_get_h sym_state) smi.nonce
