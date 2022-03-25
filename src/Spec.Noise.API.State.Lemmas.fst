module Spec.Noise.API.State.Lemmas

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Spec.Noise.HandshakeFlags
open Spec.Noise.Lengths
open Lib.ByteSequence
open FStar.Mul
friend Spec.Noise.Base.Definitions
friend Spec.Noise.API.State.Definitions
open Spec.Noise.API.State.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** Premessages *)
// TODO: prove link betwen synthesize_premessage and send_message_tokens
val synthesize_premessage_aux_lem :
     #nc : config
  -> tks:list premessage_token
  -> st:handshake_state nc ->
  Lemma
  (requires True)
  (ensures (
    let s = match st.static with | None -> None | Some kp -> Some kp.pub in
    let e = match st.ephemeral with | None -> None | Some kp -> Some kp.pub in
    match synthesize_premessage_aux #nc s e tks, send_premessage_tokens tks st with
    | None, Fail _ -> True
    | Some msg, Res (msg', _) -> Seq.equal msg msg'
    | _ -> False))
  (decreases tks)

#push-options "--fuel 1"
let rec synthesize_premessage_aux_lem #nc tks st =
  match tks with
  | [] -> ()
  | tk :: tks' ->
    match send_premessage_token tk st with
    | Fail _ -> ()
    | Res (msg, st') ->
      synthesize_premessage_aux_lem #nc tks' st';
      begin match tk with
      | PS ->
        assert(Some? st.static);
        assert(msg == ((Some?.v st.static).pub <: bytes))
      | PE ->
        assert(Some? st.ephemeral);
        assert(msg == ((Some?.v st.ephemeral).pub <: bytes))
      end;
      match send_premessage_tokens tks' st' with
      | Fail _ -> ()
      | Res (msg', st'') ->
        assert(Res? (send_premessage_tokens tks st));
        assert(fst (Res?.v (send_premessage_tokens tks st)) == Seq.append msg msg');
        let s = match st.static with | None -> None | Some kp -> Some kp.pub in
        let e = match st.ephemeral with | None -> None | Some kp -> Some kp.pub in
        let smsg0 = synthesize_premessage_aux #nc s e tks in
        let smsg1 = synthesize_premessage_aux #nc s e tks' in
        assert(Some? smsg1 /\ Some?.v smsg1 == msg');
        assert(Some? smsg0);
        assert(Some?.v smsg0 == Seq.append msg (Some?.v smsg1))
#pop-options

/// Unfolding lemmas for the premessages.
/// For now, we don't support premessages which contain ephemerals.

val process_send_premessage_none (#nc : config) (st : handshake_state nc) : option (handshake_state nc)
let process_send_premessage_none #nc st = Some st

val process_send_premessage_none_lem :
     #nc:config
  -> st:handshake_state nc ->
  Lemma (process_send_premessage None st == process_send_premessage_none st)

#push-options "--fuel 1"
let process_send_premessage_none_lem #nc st = ()
#pop-options

val process_send_premessage_s (#nc : config) (st : handshake_state nc) :
  option (handshake_state nc)
let process_send_premessage_s #nc st =
  match st.static with
  | None -> None
  | Some s ->
    (**) hash_max_input_norm_lem nc;
    Some ({ st with sym_state = mix_hash s.pub st.sym_state })

val process_send_premessage_s_lem :
     #nc:config
  -> st:handshake_state nc ->
  Lemma (process_send_premessage #nc (Some [PS]) st == process_send_premessage_s st)

#push-options "--fuel 2 --ifuel 2"
let process_send_premessage_s_lem #nc st = ()
#pop-options

val process_receive_premessage_none
  (#nc:config) (rs:option (public_key nc)) (re:option (public_key nc))
  (st:handshake_state nc) : option (handshake_state nc)
let process_receive_premessage_none #nc rs re st = Some st

val process_receive_premessage_none_lem :
     #nc:config
  -> rs:option (public_key nc)
  -> re:option (public_key nc)
  -> st:handshake_state nc ->
  Lemma (
    process_receive_premessage #nc None rs re st ==
      process_receive_premessage_none rs re st)

#push-options "--fuel 1"
let process_receive_premessage_none_lem #nc rs re st = ()
#pop-options

val process_receive_premessage_s
  (#nc:config) (rs:option (public_key nc)) (re:option (public_key nc))
  (st:handshake_state nc) : option (handshake_state nc)
let process_receive_premessage_s #nc rs re st =
  match st.remote_static, rs with
  | Some _, _ -> None
  | _, None -> None
  | None, Some rs ->
    (**) hash_max_input_norm_lem nc;
    Some ({ st with sym_state = mix_hash rs st.sym_state; remote_static = Some rs })

val process_receive_premessage_s_lem :
     #nc:config
  -> rs:option (public_key nc)
  -> re:option (public_key nc)
  -> st:handshake_state nc ->
  Lemma (
    process_receive_premessage #nc (Some [PS]) rs re st ==
      process_receive_premessage_s rs re st)

#push-options "--fuel 2 --ifuel 2"
let process_receive_premessage_s_lem #nc opt_rs opt_re st =
  match opt_rs with
  | None -> ()
  | Some rs ->
    assert(Some? (synthesize_premessage opt_rs opt_re [PS]));
    let msg = Some?.v (synthesize_premessage opt_rs opt_re [PS]) in
    assert(Seq.equal msg rs);
    assert(Seq.Base.length msg = List.Tot.length [PS] * public_key_size nc)
#pop-options


(*** State *)
(**** Misc *)
/// We need a framing lemma for initialize_handshake_state because in the implementation,
/// the local static and the psk will not be directly owned by the state.
val initialize_handshake_state_s_psk_frame_lem :
     #nc : config
  -> protocol_name : hashable nc
  -> prologue : hashable nc
  -> s : option (keypair nc)
  -> e : option (keypair nc)
  -> rs : option (public_key nc)
  -> re : option (public_key nc)
  -> psk : option preshared_key ->
  Lemma (
    // We do all the combinations
    let st0 = initialize_handshake_state protocol_name prologue None e rs re None in
    let st1 = initialize_handshake_state protocol_name prologue s e rs re None in
    let st2 = initialize_handshake_state protocol_name prologue None e rs re psk in
    let st3 = initialize_handshake_state protocol_name prologue s e rs re psk in
    st0.static == None /\ st0.preshared == None /\
    st1 == { st0 with static = s } /\
    st2 == { st0 with preshared = psk } /\
    st3 == { st0 with static = s; preshared = psk })

let initialize_handshake_state_s_psk_frame_lem #nc pname prlg s e rs re psk = ()  


(*** Handshake *)

val receive_lookup_message_tokens_with_payload_no_S_no_vst :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> st:state sc{IS_Handshake? st.st_hs_state} ->
  Pure (s_result (hashable (sc_get_config sc) & state sc))
  (requires True)
  (ensures (fun res ->
    match res with
    | Fail _ -> True
    | Res (msg, st') ->
      IS_Handshake? st'.st_hs_state))

let receive_lookup_message_tokens_with_payload_no_S_no_vst #sc msg tokens st =
//  if not (is_hashable sc.sc_config msg) then Fail Input_size else
  let is_psk = check_hsk_is_psk st.st_pattern in
  let hs_st = IS_Handshake?.st st.st_hs_state in
  let initiator = st.st_initiator in
  (* If S appears, we split at the first S and use it to perform a lookup *)
  let res =
    match receive_message_tokens_with_payload initiator is_psk tokens msg hs_st with
    | Fail e -> Fail (error_to_s_error e)
    | Res (msg', hs_st') -> Res (msg', hs_st')
  in
  (* Update the state *)
  match res with
  | Fail e -> Fail e
  | Res (plain, hs_st') ->
    Res (plain, {st with st_hs_state = internal_state_update_hs_st st.st_hs_state hs_st' })

val receive_lookup_message_tokens_with_payload_no_S :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> st:state sc{IS_Handshake? st.st_hs_state}
  -> vst:sc_get_vstate sc ->
  Pure (s_result (option (sc_get_pinfo sc) & hashable (sc_get_config sc) & state sc))
  (requires True)
  (ensures (fun res ->
    match res with
    | Fail _ -> True
    | Res (pi, msg, st') ->
      IS_Handshake? st'.st_hs_state))

let receive_lookup_message_tokens_with_payload_no_S #sc msg tokens st vst =
  match receive_lookup_message_tokens_with_payload_no_S_no_vst #sc msg tokens st with
  | Fail e -> Fail e
  | Res (plain, st') -> Res (None, plain, st')

val receive_lookup_message_tokens_with_payload_no_S_lem_eq :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token{not (List.Tot.mem S tokens)}
  -> st:state sc{IS_Handshake? st.st_hs_state}
  -> vst:sc_get_vstate sc ->
  Lemma (
    receive_lookup_message_tokens_with_payload #sc msg tokens st vst ==
    receive_lookup_message_tokens_with_payload_no_S #sc msg tokens st vst)

let receive_lookup_message_tokens_with_payload_no_S_lem_eq #sc msg tokens st vst = ()

val hs_state_receive_lookup_message_tokens_with_payload_with_S :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> initiator:bool
  -> is_psk:bool
  -> st:handshake_state (sc.sc_config)
  -> vst:sc_get_vstate sc ->
  Tot (s_result (option (sc_get_pinfo sc) & hashable (sc_get_config sc) & handshake_state sc.sc_config))

let hs_state_receive_lookup_message_tokens_with_payload_with_S #sc msg tokens initiator is_psk st vst =
  let tokens_beg, tokens_end = splitAtFirstElem S tokens in
  (* Execute on the beginning of the message pattern *)
  match receive_message_tokens initiator is_psk tokens_beg msg st with
  | Fail e -> Fail (error_to_s_error e)
  | Res (msg', hs_st') ->
    (* Validate the key *)
    match check_remote_static sc.sc_validate vst hs_st' with
    | Fail e -> Fail e
    | Res (hs_st'', pinfo) ->
      (* Execute on the end of the message pattern *)
      match receive_message_tokens_with_payload initiator is_psk tokens_end msg' hs_st'' with
      | Fail e -> Fail (error_to_s_error e)
      | Res (msg'', hs_st''') -> Res (Some pinfo, msg'', hs_st''')

val receive_lookup_message_tokens_with_payload_with_S :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> st:state sc{IS_Handshake? st.st_hs_state}
  -> vst:sc_get_vstate sc ->
  Pure (s_result (option (sc_get_pinfo sc) & hashable (sc_get_config sc) & state sc))
  (requires True)
  (ensures (fun res ->
    match res with
    | Fail _ -> True
    | Res (pi, msg, st') ->
      IS_Handshake? st'.st_hs_state))

let receive_lookup_message_tokens_with_payload_with_S #sc msg tokens st vst =
//  if not (is_hashable sc.sc_config msg) then vst, Fail Input_size else
  let is_psk = check_hsk_is_psk st.st_pattern in
  let hs_st = IS_Handshake?.st st.st_hs_state in
  let initiator = st.st_initiator in
  (* If S appears, we split at the first S and use it to perform a lookup *)
  let res =
    hs_state_receive_lookup_message_tokens_with_payload_with_S #sc msg tokens initiator is_psk hs_st vst
  in
  (* Update the state *)
  match res with
  | Fail e -> Fail e
  | Res (pinfo, plain, hs_st') ->
    Res (pinfo, plain, {st with st_hs_state = internal_state_update_hs_st st.st_hs_state hs_st' })

val receive_lookup_message_tokens_with_payload_with_S_eq :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token{List.Tot.mem S tokens}
  -> st:state sc{IS_Handshake? st.st_hs_state}
  -> vst:sc_get_vstate sc ->
  Lemma(
    receive_lookup_message_tokens_with_payload #sc msg tokens st vst ==
    receive_lookup_message_tokens_with_payload_with_S #sc msg tokens st vst)

let receive_lookup_message_tokens_with_payload_with_S_eq #sc msg tokens st vst = ()

val hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_end :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> initiator:bool
  -> is_psk:bool
  -> st:handshake_state (sc.sc_config)
  -> vst:sc_get_vstate sc ->
  Pure (s_result (option (sc_get_pinfo sc) & hashable (sc_get_config sc) & handshake_state sc.sc_config))
  (requires (
    let nc = sc.sc_config in
    let has_sym_key = Some? st.sym_state.c_state.k in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    Seq.length msg >=
      tokens_message_size nc has_sym_key is_psk tokens
      + opt_encrypt_size has_sym_key' 0 /\
    is_hashable_size nc (Seq.length msg - tokens_message_size nc has_sym_key is_psk tokens)))
  (ensures (fun _ -> True))

let hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_end #sc msg tokens initiator is_psk st vst =
  let nc = sc.sc_config in
  let has_sym_key = Some? st.sym_state.c_state.k in
  (* Validate the key *)
  match check_remote_static sc.sc_validate vst st with
  | Fail e -> Fail e
  | Res (hs_st'', pinfo) ->
    (* Execute on the end of the message pattern *)
    match receive_message_tokens_with_payload initiator is_psk tokens msg hs_st'' with
    | Fail e -> Fail (error_to_s_error e)
    | Res (msg'', hs_st''') -> Res (Some pinfo, msg'', hs_st''')

val hs_state_receive_lookup_message_tokens_nout_with_payload_with_S :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> initiator:bool
  -> is_psk:bool
  -> st:handshake_state (sc.sc_config)
  -> vst:sc_get_vstate sc ->
  Pure (s_result (option (sc_get_pinfo sc) & hashable (sc_get_config sc) & handshake_state sc.sc_config))
  (requires (
    let nc = sc.sc_config in
    let has_sym_key = Some? st.sym_state.c_state.k in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    Seq.length msg <= Lib.IntTypes.max_size_t /\
    Seq.length msg >=
      tokens_message_size nc has_sym_key is_psk tokens
      + opt_encrypt_size has_sym_key' 0 /\
    is_hashable_size nc (Seq.length msg - tokens_message_size nc has_sym_key is_psk tokens)))
  (ensures (fun _ -> True))

let hs_state_receive_lookup_message_tokens_nout_with_payload_with_S #sc msg tokens initiator is_psk st vst =
  let nc = sc.sc_config in
  let has_sym_key = Some? st.sym_state.c_state.k in
  let tokens_beg, tokens_end = splitAtFirstElem S tokens in
  (**) splitAtFirstElem_append_lem S tokens;
  (**) assert(tokens = List.Tot.append tokens_beg tokens_end);
  (**) tokens_message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end;
  let msg1, msg2 = Seq.split msg (tokens_message_size nc has_sym_key is_psk tokens_beg) in
  (* Execute on the beginning of the message pattern *)
  match receive_message_tokens_nout initiator is_psk tokens_beg #(Seq.length msg1) msg1 st with
  | Fail e -> Fail (error_to_s_error e)
  | Res hs_st' ->
    (* Validate the key *)
    match check_remote_static sc.sc_validate vst hs_st' with
    | Fail e -> Fail e
    | Res (hs_st'', pinfo) ->
      (* Execute on the end of the message pattern *)
      let has_sym_key1 = tokens_update_sym_key_flag has_sym_key is_psk tokens_beg in
      (**) receive_message_tokens_nout_has_sym_key_lem initiator is_psk tokens_beg #(Seq.length msg1) msg1 st;
      let has_sym_key2 = tokens_update_sym_key_flag has_sym_key1 is_psk tokens_end in
      let has_sym_key3 = tokens_update_sym_key_flag has_sym_key is_psk tokens in
      (**) tokens_update_sym_key_flag_decompose_lem has_sym_key is_psk tokens_beg tokens_end;
      (**) assert(has_sym_key3 = has_sym_key2);
      match receive_message_tokens_with_payload initiator is_psk tokens_end msg2 hs_st'' with
      | Fail e -> Fail (error_to_s_error e)
      | Res (msg'', hs_st''') -> Res (Some pinfo, msg'', hs_st''')

val hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_eq :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> initiator:bool
  -> is_psk:bool
  -> st:handshake_state (sc.sc_config)
  -> vst:sc_get_vstate sc ->
  Lemma
  (requires (
    let nc = sc.sc_config in
    let has_sym_key = Some? st.sym_state.c_state.k in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    Seq.length msg <= Lib.IntTypes.max_size_t /\
    Seq.length msg >=
      tokens_message_size nc has_sym_key is_psk tokens
      + opt_encrypt_size has_sym_key' 0 /\
    is_hashable_size nc (Seq.length msg - tokens_message_size nc has_sym_key is_psk tokens)))
  (ensures (
    hs_state_receive_lookup_message_tokens_nout_with_payload_with_S #sc msg tokens initiator is_psk st vst ==
    hs_state_receive_lookup_message_tokens_with_payload_with_S #sc msg tokens initiator is_psk st vst))

let hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_eq #sc msg tokens initiator is_psk st vst =
  let nc = sc.sc_config in
  let has_sym_key = Some? st.sym_state.c_state.k in
  let tokens_beg, tokens_end = splitAtFirstElem S tokens in
  (**) splitAtFirstElem_append_lem S tokens;
  (**) assert(tokens = List.Tot.append tokens_beg tokens_end);
  (**) tokens_message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end;
  let msg1, msg2 = Seq.split msg (tokens_message_size nc has_sym_key is_psk tokens_beg) in
  (* Execute on the beginning of the message pattern *)
  let res1 = receive_message_tokens_nout initiator is_psk tokens_beg #(Seq.length msg1) msg1 st in
  let res1' = receive_message_tokens initiator is_psk tokens_beg msg st in
  assert(Seq.equal msg (Seq.append msg1 msg2));
  receive_message_tokens_eq #nc initiator is_psk tokens_beg #(Seq.length msg1) msg1
                            #(Seq.length msg2) msg2 st;
  match res1, res1' with
  | Fail _, Fail _ -> ()
  | Res _, Fail _ -> ()
  | Fail _, Res _ -> ()
  | Res hs_st1, Res (msg2', hs_st1') ->
    assert(hs_st1 == hs_st1');
    assert(msg2' == msg2);
    (* Validate the key *)
    match check_remote_static sc.sc_validate vst hs_st1 with
    | Fail e -> ()
    | Res (hs_st2, pinfo) ->
      (* Execute on the end of the message pattern *)
      let has_sym_key1 = tokens_update_sym_key_flag has_sym_key is_psk tokens_beg in
      (**) receive_message_tokens_nout_has_sym_key_lem initiator is_psk tokens_beg #(Seq.length msg1) msg1 st;
      let has_sym_key2 = tokens_update_sym_key_flag has_sym_key1 is_psk tokens_end in
      let has_sym_key3 = tokens_update_sym_key_flag has_sym_key is_psk tokens in
      (**) tokens_update_sym_key_flag_decompose_lem has_sym_key is_psk tokens_beg tokens_end;
      (**) assert(has_sym_key3 = has_sym_key2)


val hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> initiator:bool
  -> is_psk:bool
  -> st:handshake_state (sc.sc_config)
  -> vst:sc_get_vstate sc ->
  Pure (s_result (option (sc_get_pinfo sc) & hashable (sc_get_config sc) & handshake_state sc.sc_config))
  (requires (
    let nc = sc.sc_config in
    let has_sym_key = Some? st.sym_state.c_state.k in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    Seq.length msg <= Lib.IntTypes.max_size_t /\
    Seq.length msg >=
      tokens_message_size nc has_sym_key is_psk tokens
      + opt_encrypt_size has_sym_key' 0 /\
    is_hashable_size nc (Seq.length msg - tokens_message_size nc has_sym_key is_psk tokens)))
  (ensures (fun _ -> True))

let hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end #sc msg tokens initiator is_psk st vst =
  let nc = sc.sc_config in
  let has_sym_key = Some? st.sym_state.c_state.k in
  let tokens_beg, tokens_end = splitAtFirstElem S tokens in
  (**) splitAtFirstElem_append_lem S tokens;
  (**) assert(tokens = List.Tot.append tokens_beg tokens_end);
  (**) tokens_message_size_decompose_lem nc has_sym_key is_psk tokens_beg tokens_end;
  let msg1, msg2 = Seq.split msg (tokens_message_size nc has_sym_key is_psk tokens_beg) in
  (* Execute on the beginning of the message pattern *)
  match receive_message_tokens_nout initiator is_psk tokens_beg #(Seq.length msg1) msg1 st with
  | Fail e -> Fail (error_to_s_error e)
  | Res hs_st' ->
    let has_sym_key1 = tokens_update_sym_key_flag has_sym_key is_psk tokens_beg in
    (**) receive_message_tokens_nout_has_sym_key_lem initiator is_psk tokens_beg #(Seq.length msg1) msg1 st;
    let has_sym_key2 = tokens_update_sym_key_flag has_sym_key1 is_psk tokens_end in
    let has_sym_key3 = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    (**) tokens_update_sym_key_flag_decompose_lem has_sym_key is_psk tokens_beg tokens_end;
    (**) assert(has_sym_key3 = has_sym_key2);
    (* Validate the key *)
    hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_end #sc msg2 tokens_end
                                                                        initiator is_psk
                                                                        hs_st' vst

val hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end_eq :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> initiator:bool
  -> is_psk:bool
  -> st:handshake_state (sc.sc_config)
  -> vst:sc_get_vstate sc ->
  Lemma
  (requires (
    let nc = sc.sc_config in
    let has_sym_key = Some? st.sym_state.c_state.k in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    Seq.length msg <= Lib.IntTypes.max_size_t /\
    Seq.length msg >=
      tokens_message_size nc has_sym_key is_psk tokens
      + opt_encrypt_size has_sym_key' 0 /\
    is_hashable_size nc (Seq.length msg - tokens_message_size nc has_sym_key is_psk tokens)))
  (ensures (
    hs_state_receive_lookup_message_tokens_nout_with_payload_with_S #sc msg tokens initiator is_psk st vst ==
    hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end #sc msg tokens initiator is_psk st vst))

let hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_beg_end_eq #sc msg tokens initiator is_psk st vst = ()

val receive_lookup_message_tokens_nout_with_payload_with_S :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> st:state sc{IS_Handshake? st.st_hs_state}
  -> vst:sc_get_vstate sc ->
  Pure (s_result (option (sc_get_pinfo sc) & hashable (sc_get_config sc) & state sc))
  (requires (
    let nc = sc.sc_config in
    let is_psk = check_hsk_is_psk st.st_pattern in
    let hs_st = IS_Handshake?.st st.st_hs_state in
    let initiator = st.st_initiator in
    let has_sym_key = Some? hs_st.sym_state.c_state.k in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    Seq.length msg <= Lib.IntTypes.max_size_t /\
    Seq.length msg >=
      tokens_message_size nc has_sym_key is_psk tokens
      + opt_encrypt_size has_sym_key' 0 /\
    is_hashable_size nc (Seq.length msg - tokens_message_size nc has_sym_key is_psk tokens)))
  (ensures (fun res ->
    match res with
    | Fail _ -> True
    | Res (pi, msg, st') ->
      IS_Handshake? st'.st_hs_state))

let receive_lookup_message_tokens_nout_with_payload_with_S #sc msg tokens st vst =
  let is_psk = check_hsk_is_psk st.st_pattern in
  let hs_st = IS_Handshake?.st st.st_hs_state in
  let initiator = st.st_initiator in
  (* If S appears, we split at the first S and use it to perform a lookup *)
  let res =
    hs_state_receive_lookup_message_tokens_nout_with_payload_with_S #sc msg tokens initiator is_psk hs_st vst
  in
  (* Update the state *)
  match res with
  | Fail e -> Fail e
  | Res (pinfo, plain, hs_st') ->
    Res (pinfo, plain, {st with st_hs_state = internal_state_update_hs_st st.st_hs_state hs_st' })

val receive_lookup_message_tokens_nout_with_payload_with_S_eq :
     #sc:sconfig
  -> msg:bytes
  -> tokens:list message_token
  -> st:state sc{IS_Handshake? st.st_hs_state}
  -> vst:sc_get_vstate sc ->
  Lemma
  (requires (
    let nc = sc.sc_config in
    let is_psk = check_hsk_is_psk st.st_pattern in
    let hs_st = IS_Handshake?.st st.st_hs_state in
    let initiator = st.st_initiator in
    let has_sym_key = Some? hs_st.sym_state.c_state.k in
    let has_sym_key' = tokens_update_sym_key_flag has_sym_key is_psk tokens in
    Seq.length msg <= Lib.IntTypes.max_size_t /\
    Seq.length msg >=
      tokens_message_size nc has_sym_key is_psk tokens
      + opt_encrypt_size has_sym_key' 0 /\
    is_hashable_size nc (Seq.length msg - tokens_message_size nc has_sym_key is_psk tokens)))
  (ensures (
    receive_lookup_message_tokens_nout_with_payload_with_S #sc msg tokens st vst ==
    receive_lookup_message_tokens_with_payload_with_S #sc msg tokens st vst))

let receive_lookup_message_tokens_nout_with_payload_with_S_eq #sc msg tokens st vst =
  let is_psk = check_hsk_is_psk st.st_pattern in
  let hs_st = IS_Handshake?.st st.st_hs_state in
  let initiator = st.st_initiator in
  hs_state_receive_lookup_message_tokens_nout_with_payload_with_S_eq #sc msg tokens initiator is_psk hs_st vst
