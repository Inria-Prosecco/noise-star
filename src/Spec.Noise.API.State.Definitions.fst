module Spec.Noise.API.State.Definitions

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.Lengths
open Spec.Noise.WellFormedness
open Lib.ByteSequence
open FStar.Mul
open FStar.List.Tot
module L = LowStar.Literal

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

#push-options "--fuel 2 --ifuel 2"
let rec splitAtFirstElem_append_lem #a x l =
  match l with
  | [] -> ()
  | x' :: l' -> splitAtFirstElem_append_lem x l'
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec splitAtFirstElem_mem_beg #a x l =
  match l with
  | [] -> ()
  | x' :: l' -> if x = x' then () else splitAtFirstElem_mem_beg x l'
#pop-options

noeq type internal_state (nc : config) =
| IS_Handshake :
     status:status
  -> st:handshake_state nc
  -> internal_state nc
| IS_Transport :
     hash:hash nc
  // Have we received a transport message? The security level may
  // not be the same if we haven't - in other words: we may want
  // to wait before sending a message.
  -> receive_message:bool
  -> cs_send:option cipher_state
  -> cs_receive:option cipher_state
  -> internal_state nc

noeq type state (sc : sconfig) = {
  st_pattern : wf_handshake_pattern;
  st_initiator : bool;
  st_hs_state : internal_state (sc_get_config sc);
}

(* Some functions to retrieve information from the state *)
let state_get_pattern #sc st = st.st_pattern
let state_get_status #sc st =
  match st.st_hs_state with
  | IS_Handshake status _ -> status
  | _ -> Transport

let internal_state_get_hash #nc st =
  match st with
  | IS_Handshake _ st -> st.sym_state.h
  | IS_Transport h _ _ _ -> h

let state_get_internal_state #sc st = st.st_hs_state

let state_is_initiator #sc st = st.st_initiator
let state_is_handshake #sc st = IS_Handshake? st.st_hs_state

let state_received_transport_message #sc st =
  match st.st_hs_state with
  | IS_Handshake _ _ -> false
  | IS_Transport _ recv _ _ -> recv

let state_get_s #sc st =
  (IS_Handshake?.st st.st_hs_state).static
let state_get_rs #sc st =
  (IS_Handshake?.st st.st_hs_state).remote_static
let state_get_psk #sc st =
  (IS_Handshake?.st st.st_hs_state).preshared

let rec synthesize_premessage_aux (#nc : config) (s e : option (public_key nc))
                                  (premsg : list premessage_token) :
  option bytes =
  match premsg with
  | [] -> Some lbytes_empty
  | tk :: premsg' ->
    let opt_tk_msg =
      match tk with
      | PS -> s
      | PE -> e
    in
    match opt_tk_msg, synthesize_premessage_aux s e premsg' with
    | Some msg1, Some msg2 -> Some (Seq.append msg1 msg2)
    | _ -> None

let synthesize_premessage (#nc : config) (s e : option (public_key nc))
                          (premsg : list premessage_token) :
  option bytes =
  match synthesize_premessage_aux s e premsg with
  | None -> None
  | Some premsg ->
    if Seq.length premsg > Lib.IntTypes.max_size_t then None else Some premsg

val compute_protocol_name_bytes_list
  (pattern_name : string{check_pattern_name pattern_name})
  (nc : config) :
  l:list Lib.IntTypes.uint8{List.Tot.length l == protocol_name_length (String.length pattern_name) nc}

let compute_protocol_name_bytes_list pattern_name nc =
  (**) protocol_name_ascii_lem pattern_name nc;
  (**) protocol_name_length_eq pattern_name nc;
  (**) protocol_name_length_lem (String.length pattern_name) nc;
  (**) hash_max_input_norm_lem nc;
  (**) normalize_term_spec(Lib.IntTypes.max_size_t);
  (**) assert(String.length (compute_protocol_name pattern_name nc) <= String.length pattern_name + 31);
  (**) assert(is_hashable_size nc (String.length pattern_name + 31));
  let s = compute_protocol_name pattern_name nc in
  let cs = List.Tot.map L.u8_of_ascii_char (L.ascii_chars_of_ascii_string s) in
  let cs = List.Tot.map (fun x -> Lib.IntTypes.secret #Lib.IntTypes.U8 x) cs in
  (**) assert(List.Tot.length cs == protocol_name_length (String.length pattern_name) nc);
  cs

val compute_protocol_name_byteseq
  (pattern_name : string{check_pattern_name pattern_name})
  (nc : config) :
  s:hashable nc{Seq.length s == protocol_name_length (String.length pattern_name) nc}

let compute_protocol_name_byteseq pattern_name nc =
  (**) hash_max_input_norm_lem nc;
  (**) normalize_term_spec(Lib.IntTypes.max_size_t);
  (**) assert(is_hashable_size nc (String.length pattern_name + 31));
  Seq.seq_of_list (compute_protocol_name_bytes_list pattern_name nc)

/// We assume that, whenever the pattern uses premessages, we should be able to
/// process them at state creation (which implies that if there is a premessage
/// from the remote to us, we need to know the remote).
let process_send_premessage #nc premsg (st : handshake_state nc) :
  option (handshake_state nc) =
  match premsg with
  | None -> Some st
  | Some pre ->
    match send_premessage_tokens pre st with
    | Fail _ -> None
    | Res (_, st') -> Some st'

let process_receive_premessage #nc premsg (rs re : option (public_key nc))
                               (st : handshake_state nc) :
  option (handshake_state nc) =
  match premsg with
  | None -> Some st
  | Some pre ->
    let msg = synthesize_premessage rs re pre in
    match msg with
    | None -> None
    | Some msg ->
      match receive_premessage_tokens pre msg st with
      | Fail _ -> None
      | Res st' -> Some st'

val process_initiator_premessages :
     #nc:config
  -> pattern:wf_handshake_pattern
  -> rs:option (public_key nc)
  -> re:option (public_key nc)
  -> hs_st:handshake_state nc ->
  Tot (s_result (handshake_state nc))

let process_initiator_premessages #nc pattern rs re hs_st0 =
  (* Premessage I -> R *)
  match process_send_premessage pattern.premessage_ir hs_st0 with
  | None -> Fail Premessage
  | Some hs_st1 ->
    (* Premessage R -> I *)
    match process_receive_premessage pattern.premessage_ri rs re hs_st1 with
    | None -> Fail Premessage
    | Some hs_st2 ->
      Res hs_st2

val process_responder_premessages :
     #nc:config
  -> pattern:wf_handshake_pattern
  -> rs:option (public_key nc)
  -> re:option (public_key nc)
  -> hs_st:handshake_state nc ->
  Tot (s_result (handshake_state nc))

let process_responder_premessages #nc pattern rs re hs_st0 =
  (* Premessage I -> R *)
  match process_receive_premessage pattern.premessage_ir rs re hs_st0 with
  | None -> Fail Premessage
  | Some hs_st1 ->
    (* Premessage R -> I *)
    match process_send_premessage pattern.premessage_ri hs_st1 with
    | None -> Fail Premessage
    | Some hs_st2 ->
      Res hs_st2

val process_premessages :
     #nc:config
  -> pattern:wf_handshake_pattern
  -> initiator:bool
  -> rs:option (public_key nc)
  -> re:option (public_key nc)
  -> hs_st:handshake_state nc ->
  Tot (s_result (handshake_state nc))

let process_premessages #nc pattern initiator rs re hs_st =
  if initiator then process_initiator_premessages #nc pattern rs re hs_st
  else process_responder_premessages #nc pattern rs re hs_st

let create_state #sc pattern prologue initiator s e rs psk =
  (* Initialize *)
  let protocol_name = compute_protocol_name_byteseq pattern.name (sc_get_config sc) in
  let hs_st0 =
    initialize_handshake_state protocol_name prologue
                               s e
                               None None psk
  in
  (* Premessages *)
  match process_premessages pattern initiator rs None hs_st0 with
  | Fail e -> Fail e
  | Res hs_st1 ->
    let status = if initiator then Handshake_send 0 else Handshake_receive 0 in
    Res ({
      st_pattern = pattern;
      st_initiator = initiator;
      st_hs_state = IS_Handshake status hs_st1;
    })

let error_to_s_error (e : Spec.Noise.Base.error) : s_error =
  match e with
  | Spec.Noise.Base.No_key -> No_key
  | Spec.Noise.Base.Already_key -> Already_key
  | Spec.Noise.Base.Input_size -> Input_size
  | Spec.Noise.Base.DH -> DH_error
  | Spec.Noise.Base.Decryption -> Decryption
  | Spec.Noise.Base.Saturated_nonce -> Saturated_nonce

/// We need to rewrite the receive functions to take keys validation and lookup into account
let internal_state_update_hs_st (#nc : config) (ist : internal_state nc{IS_Handshake? ist})
                                (hs_st : handshake_state nc) :
  Tot (internal_state nc) =
  let IS_Handshake step _ = ist in
  IS_Handshake step hs_st

let internal_state_update_status (#nc : config) (ist : internal_state nc{IS_Handshake? ist})
                                 (status : status) :
  Tot (internal_state nc) =
  let IS_Handshake _ hs_st = ist in
  IS_Handshake status hs_st

/// A helper to validate a remote static key
val check_remote_static :
     #nc:config
  -> #vstate:Type0
  -> #pinfo:Type0
  -> validate:validation_function nc vstate pinfo
  -> vst:vstate
  -> hs_st:handshake_state nc ->
  s_result (handshake_state nc & pinfo)

let check_remote_static #nc #vstate #pinfo validate vst hs_st =
  (* Check that there is a key *)
  match hs_st.remote_static with
  | None -> Fail No_key
  | Some rs ->
    (* Validate *)
    let res = validate vst rs in
    match res with
    | Some (info, psk) ->
      begin match hs_st.preshared, psk with
      | None, _ -> Res ({hs_st with preshared = psk}, info)
      // We shouldn't be able to replace the preshared key with a new one
      | Some _, Some _ -> Fail Already_key
      // This one is trickier and is more of a design choice:
      // usually, we should not receive a remote static key
      // if we already know a preshared key (it doesn't really
      // make sense, because it implies we already know the remote).
      // So we make this one invalid. We could make
      // it valid and simply return the current state if we find
      // a use case. Note that for now, we really need the remote
      // static check to behave this way for the DY proofs (otherwise
      // we get a situation where we already know the remote peer
      // identity, then learn a new remote identity - at which point
      // we are stuck unless we add assumptions).
      | Some _, None -> Fail Already_key
      end
    | None -> Fail Rs_not_valid

val receive_lookup_message_tokens_with_payload :
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
      IS_Handshake? st'.st_hs_state /\
      (List.Tot.mem S tokens <==> Some? pi)))

let receive_lookup_message_tokens_with_payload #sc msg tokens st vst =
  let is_psk = check_hsk_is_psk st.st_pattern in
  let hs_st = IS_Handshake?.st st.st_hs_state in
  let initiator = st.st_initiator in
  (* If S appears, we split at the first S and use it to perform a lookup *)
  let res =
    if List.Tot.mem S tokens then
      let tokens_beg, tokens_end = splitAtFirstElem S tokens in
      (* Execute on the beginning of the message pattern *)
      match receive_message_tokens initiator is_psk tokens_beg msg hs_st with
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
    else
      match receive_message_tokens_with_payload initiator is_psk tokens msg hs_st with
      | Fail e -> Fail (error_to_s_error e)
      | Res (msg', hs_st') -> Res (None, msg', hs_st')
  in
  (* Update the state *)
  match res with
  | Fail e -> Fail e
  | Res (pinfo, plain, hs_st') ->
    Res (pinfo, plain, {st with st_hs_state = internal_state_update_hs_st st.st_hs_state hs_st' })

(* Process the handshake messages *)
let handshake_write #sc payload st =
  (* Sanity checks *)
  if not (IS_Handshake? st.st_hs_state) then Fail Incorrect_transition else
  match state_get_status st with
  | Handshake_send i ->
    let pat = st.st_pattern.messages in
    if i >= List.Tot.length pat then Fail Incorrect_transition
    else if not (is_plain_message_length sc.sc_config (Seq.length payload)) then Fail Input_size
    else
      let message_pat = List.Tot.index pat i in
      let is_psk = check_hsk_is_psk st.st_pattern in
      let status' = Handshake_receive (i+1) in
      let hs_st = IS_Handshake?.st st.st_hs_state in
      let res =
        send_message_tokens_with_payload st.st_initiator is_psk
                                         message_pat payload hs_st
      in
      begin match res with
      | Fail e ->
        (**) send_message_tokens_with_payload_error_lem st.st_initiator is_psk
                                                        message_pat payload hs_st;
        Fail (error_to_s_error e)
      | Res (msg, hs_st1) ->
        let st1 = {st with st_hs_state = IS_Handshake status' hs_st1} in
        Res (msg, st1)
      end
  | _ ->
    Fail Incorrect_transition

let handshake_read #sc msg st vst =
  (* Sanity check *)
  if not (IS_Handshake? st.st_hs_state) then Fail Incorrect_transition else
  match state_get_status st with
  | Handshake_receive i ->
    let pat = st.st_pattern.messages in
    if i >= List.Tot.length pat then Fail Incorrect_transition
    else if Seq.length msg > Lib.IntTypes.max_size_t then Fail Input_size
    else
      let message_pat = List.Tot.index pat i in
      let is_psk = check_hsk_is_psk st.st_pattern in
      let status' = Handshake_send (i+1) in
      let res = receive_lookup_message_tokens_with_payload msg message_pat st vst in
      begin match res with
      | Fail e -> Fail e
      | Res (pinfo, payload, st1) ->
        let st2 = { st1 with st_hs_state = internal_state_update_status st1.st_hs_state status' } in
        Res (pinfo, payload, st2)
      end
  | _ -> Fail Incorrect_transition

(* Split - we make a disjoint function so that it is possible to perform checks
 * (with the remote static and the payload, for example) before splitting *)
let split #sc st =
  if not (IS_Handshake? st.st_hs_state) then Fail Incorrect_transition else
  match state_get_status st with
  | Transport -> Fail Incorrect_transition
  | Handshake_send i | Handshake_receive i ->
    let pat = st.st_pattern.messages in
    if i < List.Tot.length pat then Fail Incorrect_transition
    else
      let hs_st = IS_Handshake?.st st.st_hs_state in
      let final_hash = hs_st.sym_state.h in
      let cs1, cs2 = Spec.Noise.Base.split hs_st.sym_state in
      let cs1, cs2 = if st.st_initiator then cs1, cs2 else cs2, cs1 in
      let cs1 = if can_send st.st_initiator st.st_pattern then Some cs1 else None in
      let cs2 = if can_receive st.st_initiator st.st_pattern then Some cs2 else None in
      let hs_st' : internal_state sc.sc_config = IS_Transport final_hash false cs1 cs2 in
      Res ({ st with st_hs_state = hs_st' })  

(* Transport phase: read and write functions *)
let transport_write #sc st msg =
  match st.st_hs_state with
  | IS_Transport final_hash recv_msg (Some cs_send) cs_receive ->
    if Seq.length msg > Lib.IntTypes.max_size_t then Fail Input_size else
      begin match encrypt_with_ad sc.sc_config Seq.empty msg cs_send with
      | Fail e ->
        (**) encrypt_with_ad_error_lem sc.sc_config Seq.empty msg cs_send;
        Fail (error_to_s_error e)
      | Res (plain, cs_send') ->
        Res (plain, { st with st_hs_state = IS_Transport final_hash recv_msg (Some cs_send') cs_receive })
      end
  | _ -> Fail Incorrect_transition

let transport_read #sc st cipher =
  match st.st_hs_state with
  | IS_Transport final_hash _ cs_send (Some cs_receive) ->
    if Seq.length cipher > Lib.IntTypes.max_size_t then Fail Input_size else
      begin match decrypt_with_ad sc.sc_config Seq.empty cipher cs_receive with
      | Fail e ->
        (**) decrypt_with_ad_error_lem sc.sc_config Seq.empty cipher cs_receive;
        Fail (error_to_s_error e)
      | Res (plain, cs_receive') ->
        Res (plain, { st with st_hs_state = IS_Transport final_hash true cs_send (Some cs_receive') })
      end
  | _ -> Fail Incorrect_transition
