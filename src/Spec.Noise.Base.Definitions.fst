module Spec.Noise.Base.Definitions

open FStar.Mul

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.Noise.CryptoPrimitives

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

/// Small helper for the proofs


(*** Cipher state *)

let initialize_key k = { k = k; n = 0; }

let has_key st =
  match st.k with
  | None -> false
  | Some _ -> true

let set_nonce n st = ({ st with n = n; })

let encrypt_with_ad nc aad plain st =
  match st.k with
  | None -> Res (plain, st)
  | Some k' ->
    if st.n >= saturated_nonce_value then Fail Saturated_nonce else
    if length aad > aead_max_input nc then Fail Input_size else
    if length plain > aead_max_input nc then Fail Input_size else
    let cipher = aead_encrypt nc k' st.n aad plain in
    Res (cipher, {st with n = st.n + 1})

let decrypt_with_ad nc aad c st =
  match st.k with
  | None -> Res (c, st)
  | Some k' ->
    if st.n >= saturated_nonce_value then Fail Saturated_nonce else
    if length aad > aead_max_input nc then Fail Input_size else
    if length c < aead_tag_size then Fail Input_size else
    if length c > aead_max_input nc + aead_tag_size  then Fail Input_size else
    let r = aead_decrypt nc k' st.n aad c in
    match r with
    | None -> Fail Decryption
    | Some decrypted ->
      Res (decrypted, {st with n = st.n + 1})

(*** Symmetric state *)

let initialize_symmetric #nc pname =
  let pname_len : size_nat = length pname in
  let h : hash nc =
  begin
    if pname_len <= hash_size nc
    then
      begin
      let pad_size = (hash_size nc - pname_len) in
      let zeros = create pad_size (u8 0) in
      concat #uint8 #pname_len #pad_size pname zeros
      end
    else do_hash nc pname
  end in
  { c_state = initialize_key None; ck = h; h = h }


(** Facility function not in the Noise technical paper: if the hash size is 64,
  * truncates a hash to so that it can be used as a key *)
val key_from_hash : #nc:config -> hash nc -> aead_key
let key_from_hash #nc h = if hash_size nc = 64 then Seq.slice h 0 32 else h

let mix_key #nc key st =
  let ck, temp_k = kdf2 st.ck key in
  let temp_k' = key_from_hash temp_k in
  let c_st = initialize_key (Some temp_k') in
  { st with ck = ck; c_state = c_st }

let mix_hash #nc data st =
  let cs = concat #uint8 #(hash_size nc) #(length data) st.h data in
  { st with h = do_hash nc cs }

let mix_key_and_hash #nc key st =
  let ck, temp_h, temp_k = kdf3 st.ck key in
  let temp_k' = key_from_hash temp_k in
  let st1 = { st with ck = ck } in
  (**) hash_max_input_norm_lem nc;
  let st2 = mix_hash temp_h st1 in
  let c_st = initialize_key (Some temp_k') in
  { st2 with c_state = c_st }

let encrypt_and_hash #nc plain st =
  let temp = encrypt_with_ad nc st.h plain st.c_state in
  match temp with
  | Fail x -> Fail x
  | Res (cipher, c_st') -> 
    let st1 = { st with c_state = c_st' } in
    let st2 = mix_hash cipher st1 in
    Res (cipher, st2)

let decrypt_and_hash #nc cipher st =
  let temp = decrypt_with_ad nc st.h cipher st.c_state in
  match temp with
  | Fail x -> Fail x
  | Res (plain, c_st') ->
    let st1 = { st with c_state = c_st' } in
    let st2 = mix_hash cipher st1 in
    Res (plain, st2)

let split st =  
  let temp_k1, temp_k2 = kdf2_no_key st.ck in
  let temp_k1_1 = key_from_hash temp_k1 in
  let temp_k2_1 = key_from_hash temp_k2 in
  let c1 = initialize_key (Some temp_k1_1) in
  let c2 = initialize_key (Some temp_k2_1) in
  (c1, c2)

(*** Handshake state *)

let initialize_handshake_state protocol_name prologue s e rs re psk =
  (* initialize the symmetric state with the protocol name *)
  let sym_st1 = initialize_symmetric protocol_name in
  (* mix hash the prologue *)
  let sym_st2 = mix_hash prologue sym_st1 in
  (* return state *)
  {
    sym_state = sym_st2;
    static = s;
    ephemeral = e;
    remote_static = rs;
    remote_ephemeral = re;
    preshared = psk;
  }

let send_premessage_token #nc pk st =
  match pk with
  | PS ->
    begin
    match st.static with
    | None -> Fail PE_no_key
    | Some k ->
      (**) hash_max_input_norm_lem nc;
      Res (k.pub, { st with sym_state = mix_hash k.pub st.sym_state; })
    end
  | PE ->
    begin
    match st.ephemeral with
    | None -> Fail PE_no_key
    | Some k -> Res (k.pub, st)
    end

let receive_premessage_token #nc pk msg st =
  match pk with
  | PS ->
    begin
    match st.remote_static with
    | Some k -> Fail PE_already_key
    | None ->
      (**) hash_max_input_norm_lem nc;
      Res ({ st with sym_state = mix_hash msg st.sym_state; remote_static = Some msg; })
    end
  | PE ->
    begin
    match st.remote_ephemeral with
    | Some k -> Fail PE_already_key
    | None -> Res ({ st with remote_ephemeral = Some msg })
    end

let rec send_premessage_tokens #nc pattern st =
  match pattern with
  | [] -> Res (lbytes_empty, st)
  | tk::pattern' ->
    match send_premessage_token tk st with
    | Fail e -> Fail e
    | Res (msg1, st1) ->
      match send_premessage_tokens pattern' st1 with
      | Fail e -> Fail e
      | Res (msg2, st2) ->
        Res (Seq.append msg1 msg2, st2)

#push-options "--fuel 1"
let rec receive_premessage_tokens #nc pattern msg st =
  if length msg <> List.Tot.length pattern * public_key_size nc then Fail PE_input_size else
  match pattern with
  | [] -> Res st
  | tk::pattern' ->
    let msg1, msg2 = split_bytes msg (public_key_size nc) in
    match receive_premessage_token tk msg1 st with
    | Fail e -> Fail e
    | Res st' -> receive_premessage_tokens pattern' msg2 st'
#pop-options

let dh_update #nc msg opt_priv opt_pub st =
  match opt_priv, opt_pub with
  | Some priv, Some pub ->
    (match dh priv.priv pub with
     | Some k -> Res (msg, { st with sym_state = mix_key k st.sym_state })
     | None -> Fail DH)
  | _ -> Fail No_key

(* For the send_message_token function, we always output an empty string *)
let dh_update_send #nc = dh_update #nc lbytes_empty

let send_message_token #nc initiator is_psk tk st =
  match tk with
  | S ->
    begin
    match st.static with
    | None -> Fail No_key
    | Some k ->
      (**) hash_max_input_norm_lem nc;
      begin match encrypt_and_hash k.pub st.sym_state with
      | Fail x -> Fail x
      | Res (cipher, sym_st') ->
        Res (cipher, { st with sym_state = sym_st'; })
      end
    end
  | E ->
    begin
    match st.ephemeral with
    | None -> Fail No_key
    | Some k ->
      (**) hash_max_input_norm_lem nc;
      let sym_st1 = mix_hash k.pub st.sym_state in
      let sym_st2 =
        if is_psk
        then mix_key k.pub sym_st1
        else sym_st1
      in
      Res (k.pub, { st with sym_state = sym_st2; })
    end
  | SS -> dh_update_send st.static st.remote_static st
  | EE -> dh_update_send st.ephemeral st.remote_ephemeral st
  | SE ->
    let opt_priv = if initiator then st.static
                                   else st.ephemeral in
    let opt_pub = if initiator then st.remote_ephemeral
                                  else st.remote_static in
    dh_update_send opt_priv opt_pub st
  | ES ->
    let opt_priv = if initiator then st.ephemeral
                                   else st.static in
    let opt_pub = if initiator then st.remote_static
                                  else st.remote_ephemeral in
    dh_update_send opt_priv opt_pub st
  | PSK ->
    begin
    match st.preshared with
    | None -> Fail No_key
    | Some k ->
      let st' = { st with sym_state = mix_key_and_hash k st.sym_state; } in
      Res (lbytes_empty, st')
    end

let receive_message_token #nc initiator is_psk tk msg st =
  match tk with
  | S ->
    if Some? st.remote_static then Fail Already_key else
    let numbytes : size_nat =
        if has_key st.sym_state.c_state then public_key_size nc + aead_tag_size
                                        else public_key_size nc in
    if length msg < numbytes then Fail Input_size else
    let temp, msg' = split_bytes msg numbytes in
    (**) hash_max_input_norm_lem nc;
    let temp' = decrypt_and_hash temp st.sym_state in
    begin
    match temp' with
    | Res (rs, sym_st') ->
      Res (msg', { st with remote_static = Some rs; sym_state = sym_st' })
    | Fail e -> Fail e
    end
  | E ->
    if Some? st.remote_ephemeral then Fail Already_key else
    if length msg < public_key_size nc then Fail Input_size else
    let re, msg' = split_bytes msg (public_key_size nc) in
    (**) hash_max_input_norm_lem nc;
    let sym_st1 = mix_hash re st.sym_state in
    let sym_st2 =
      if is_psk
      then mix_key re sym_st1
      else sym_st1
    in
    Res (msg', { st with sym_state = sym_st2; remote_ephemeral = Some re})
  | SS -> dh_update msg st.static st.remote_static st
  | EE -> dh_update msg st.ephemeral st.remote_ephemeral st
  | SE ->
    let opt_priv = if initiator then st.static else st.ephemeral in
    let opt_pub = if initiator then st.remote_ephemeral
                                  else st.remote_static in
    dh_update msg opt_priv opt_pub st
  | ES ->
    let opt_priv = if initiator then st.ephemeral else st.static in
    let opt_pub = if initiator then st.remote_static
                                  else st.remote_ephemeral in
    dh_update msg opt_priv opt_pub st
  | PSK ->
    begin
    match st.preshared with
    | None -> Fail No_key
    | Some k ->
      Res (msg, { st with sym_state = mix_key_and_hash k st.sym_state; })
    end

let rec send_message_tokens #nc initiator is_psk pattern st =
  match pattern with
  | [] ->
    Res (lbytes_empty, st)
  | tk::pattern' ->
    match send_message_token initiator is_psk tk st with
    | Fail e -> Fail e
    | Res (msg, st') ->
      match send_message_tokens initiator is_psk pattern' st' with
      | Fail e -> Fail e
      | Res (msg', st'') ->
        Res (Seq.append msg msg', st'')

let send_message_tokens_with_payload initiator is_psk pattern payload st =
  match send_message_tokens initiator is_psk pattern st with
  | Fail e -> Fail e
  | Res (msg1, st1) ->
    match encrypt_and_hash payload st1.sym_state with
    | Fail x -> Fail x
    | Res (msg2, sym_st1) ->
      Res (Seq.append msg1 msg2, {st1 with sym_state = sym_st1})

let rec receive_message_tokens #nc initiator is_psk pattern msg st =
  match pattern with
  | [] ->
    Res (msg, st)
  | tk::pattern' ->
    match receive_message_token initiator is_psk tk msg st with
    | Fail e -> Fail e
    | Res (msg', st') ->
      match receive_message_tokens initiator is_psk pattern' msg' st' with
      | Fail e -> Fail e
      | Res (msg'', st'') ->
        Res (msg'', st'')

let receive_message_tokens_with_payload #nc initiator is_psk pattern msg st =
  match receive_message_tokens initiator is_psk pattern msg st with
  | Fail e -> Fail e
  | Res (msg1, st1) ->
    if not (is_hashable nc msg1) then Fail Input_size else
    begin match decrypt_and_hash msg1 st1.sym_state with
    | Fail e -> Fail e
    | Res (plain, sym_state1) ->
      Res (plain, {st1 with sym_state = sym_state1})
    end

let initialize #nc protocol_name prologue s e psk =
  initialize_handshake_state protocol_name prologue s e None None psk
