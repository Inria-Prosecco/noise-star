module Impl.Noise.SymmetricState

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence

module B = LowStar.Buffer
module LB = Lib.Buffer
open Lib.Buffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Meta.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.HKDF

friend Spec.Noise.Base.Definitions

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"
let _ = allow_inversion return_type

inline_for_extraction noextract
let hash_is_64 (nc : iconfig) =
  if with_norm(hash_size (get_config nc)) = 64 then true else false

(*** State transition functions *)
(* Some auxiliary functions used in the correctness proof of [initialize_symmetric] *)
noextract
let initialize_symmetric_hash_v_ (nc : config) (pname : hashable nc) : hash nc =
  let pname_len = S.length pname in
  if pname_len <= hash_size nc
    then
      begin
      let pad_size = (hash_size nc - pname_len) in
      let zeros = S.create pad_size (u8 0) in
      S.concat #uint8 #pname_len #pad_size pname zeros
      end
    else do_hash nc pname

inline_for_extraction noextract
val initialize_symmetric_hash_ :
  #nc : iconfig ->
  nci : config_impls nc ->
  protocol_name_len : hashable_size_t nc ->
  protocol_name : hashable_t nc protocol_name_len ->
  hashb : hash_t nc ->
  Stack (rtype hash_return_type)
  (requires (fun h -> live h protocol_name /\ live h hashb /\ disjoint protocol_name hashb /\
                    begin
                    if size_v protocol_name_len <= hash_vsv nc then
                      S.equal h.[|hashb|] (S.create (hash_vsv nc) (u8 0))
                    else
                      get_hash_pre nc
                    end))
  (ensures (fun h0 r h1 ->
              modifies (loc hashb) h0 h1 /\
              begin
              let r_v = initialize_symmetric_hash_v_ (get_config nc) h0.[|protocol_name|] in
              eval_hash h1 hashb == r_v
              end))

#push-options "--z3rlimit 50"
let initialize_symmetric_hash_ #nc nci pname_len pname hashbuf =
  let h0 = HST.get () in
  if pname_len <=. hash_vs nc
  then
    begin
    (**) let pname_len_v : Ghost.erased size_nat = size_v pname_len in
    (**) assert(pname_len_v <= hash_vsv nc);
    (**) let hash_begin : Ghost.erased _ = gsub hashbuf 0ul pname_len in
    (**) let hash_end_len_v : Ghost.erased size_nat = hash_vsv nc - (size_v pname_len) in
    (**) let hash_end_len : Ghost.erased size_t = size hash_end_len_v in
    (**) let hash_end : Ghost.erased (lbuffer uint8 hash_end_len) =
    (**)                      gsub hashbuf pname_len hash_end_len in
    update_sub hashbuf 0ul pname_len pname;
    (**) let h1 = HST.get () in
    (**) let hash_v1 : Ghost.erased (lseq uint8 (hash_vsv nc)) = h1.[|hashbuf|] in
    (**) assert(S.sub hash_v1 0 pname_len_v `S.equal` h0.[|pname|]);
    (**) assert(S.sub hash_v1 pname_len_v hash_end_len_v `S.equal`
                      (S.create hash_end_len_v (u8 0)));
    (**) calc (S.equal) {
    (**)   Ghost.reveal hash_v1;
    (**) (S.equal) { lemma_slice hash_v1 (size_v pname_len) }
    (**)   (slice hash_v1 0 (size_v pname_len)) @|
    (**)          (slice hash_v1 (size_v pname_len) (S.length hash_v1));
    (**) (S.equal) {}
    (**)   h0.[|pname|] @| (S.create hash_end_len_v (u8 0));
    (**) };
    (**) assert(eval_hash h1 hashbuf ==
    (**)          initialize_symmetric_hash_v_ (get_config nc) (LB.as_seq h0 pname));
    success hash_return_type
    end
  else
    ido_hash nci hashbuf pname_len pname
#pop-options

let initialize_symmetric_fm #nc nci pname_len pname st_cs_k st_ck st_h =
  let h0 = HST.get () in
  (* Initialize the hash *)
  let _ = initialize_symmetric_hash_ nci pname_len pname st_h in
  (* Copy to the chaining key *)
  [@inline_let] let ck : chaining_key_t nc = st_ck in
  update_sub ck 0ul (chaining_key_vs nc) st_h;
  (* Postcondition *)
  let h2 = HST.get () in
  (**) let st : Ghost.erased (symmetric_state_m nc) = mk_ssm st_cs_k st_ck st_h in
  (**) initialized_cipher_state_no_key_lem h2 st_cs_k;
  (**) assert(LB.(ssm_modifies0 st h0 h2));
  (**) assert((eval_symmetric_state_m h2 st false 0).c_state == initialize_key None);
  (**) assert((eval_symmetric_state_m h2 st false 0).h `S.equal`
                                      (eval_symmetric_state_m h2 st false 0).ck);
  success hash_return_type

#push-options "--z3rlimit 50"
let mix_key_fm #nc csi has_sk key st_cs_k st_ck st_h n =
  if hash_is_64 nc then
    begin
    push_frame();
    let temp_k : lbuffer uint8 64ul = create 64ul (u8 0) in
    let _ = kdf2 (csi_get_kdf csi) st_ck (public_key_vs nc) key st_ck temp_k in
    update_sub (st_cs_k <: aead_key_t) 0ul 32ul (sub temp_k 0ul 32ul);
    (* Leave no sensitive information on the stack *)
    Lib.Memzero0.memzero #uint8 temp_k 64ul;
    pop_frame();
    success _
    end
  else kdf2 (csi_get_kdf csi) st_ck (public_key_vs nc) key st_ck st_cs_k
#pop-options

let mix_hash_fm #nc csi has_sk input_len input st_cs_k st_ck st_h n =
  ido_hash2 (csi_get_prims csi) st_h input_len input

#push-options "--z3rlimit 100 --ifuel 1"
inline_for_extraction noextract
let mix_key_and_hash_fm_
    (#nc : iconfig)
    (csi : cs_impls nc)
    (mix_hash_impl : mix_hash_fst nc)
    (has_sk : Ghost.erased bool)
    (psk : preshared_key_t)
    (st_cs_k : opt_aead_key_t{not (g_is_null st_cs_k)})
    (st_ck : chaining_key_t nc)
    (st_h : hash_t nc)
    (nonce : Ghost.erased nat)
    (temp_h : hash_t nc) :
    Stack (rtype hash_return_type)
    (requires (fun h ->
      let st = mk_ssm st_cs_k st_ck st_h in
      ssm_inv h st true /\ live h psk /\ live h temp_h /\
      ssm_disjoint st psk /\
      ssm_disjoint st temp_h /\ disjoint temp_h psk /\
      get_hash_pre nc
    ))
    (ensures (fun h0 r h1 ->
      let st = mk_ssm st_cs_k st_ck st_h in
      ssm_modifies1 st temp_h h0 h1 /\
      begin match is_success r with
      | true ->
        eval_symmetric_state_m h1 st (**) true (**) 0 ==
          Spec.mix_key_and_hash h0.[|psk|]
                                (eval_symmetric_state_m h0 st has_sk nonce)
      | false -> True
      end)) =
  [@inline_let] let st = mk_ssm st_cs_k st_ck st_h in
  (**) let h0 = HST.get () in
  let _ =
    if hash_is_64 nc then
      begin
      push_frame ();
      let temp_k : lbuffer uint8 64ul = create 64ul (u8 0) in
      let _ = kdf3 (csi_get_kdf csi) (ssm_get_ck st) preshared_key_vs psk (ssm_get_ck st) temp_h temp_k in
      update_sub ((csm_get_k (ssm_get_c_state st)) <: aead_key_t) 0ul 32ul (sub temp_k 0ul 32ul);
      (* Leave no sensitive information on the stack *)
      Lib.Memzero0.memzero #uint8 temp_k 64ul;
      pop_frame();
      convert_subtype #unit #(rtype hash_return_type) ()
      end
    else
      kdf3 (csi_get_kdf csi) (ssm_get_ck st) preshared_key_vs psk (ssm_get_ck st) temp_h
           (csm_get_k (ssm_get_c_state st))
  in
  (**) let h2 = HST.get () in
  (**) hash_max_input_norm_lem (get_config nc);
  let _ = mix_hash_impl true (hash_vs nc) temp_h st_cs_k st_ck st_h nonce in
  (**) let h3 = HST.get () in
  (**)assert(
  (**)  let st0 = eval_symmetric_state_m h0 st has_sk nonce in
  (**)  let ck, temp_h, temp_k =
  (**)    Spec.kdf3 h0.[|ssm_get_ck st|] h0.[|psk|] in
  (**)  let temp_k' = key_from_hash temp_k in
  (**)  let st1 = { st0 with ck = ck } in
  (**)  let st2 = Spec.mix_hash temp_h st1 in
  (**)  eval_symmetric_state_m h3 st true nonce ==
  (**)    { st2 with c_state = {st0.c_state with k = Some temp_k'}});
  success _
#pop-options

#push-options "--z3rlimit 100 --ifuel 1"
let mix_key_and_hash_fm #nc csi mix_hash_impl has_sk psk st_cs_k st_ck st_h nonce =
  push_frame ();
  let temp_hash : hash_t nc = create (hash_vs nc) (u8 0) in
  let _ = mix_key_and_hash_fm_ csi mix_hash_impl has_sk psk st_cs_k st_ck st_h nonce temp_hash in
  (* Don't leave any sensitive information on the stack *)
  Lib.Memzero0.memzero #uint8 temp_hash (hash_vs nc);
  pop_frame ();
  convert_subtype #unit #(rtype hash_return_type) ()
#pop-options

(**** encrypt_and_hash *)
let encrypt_and_hash_no_key_fm #nc mix_hash_impl =
  fun msg_len msg cipher st_cs_k st_ck st_h nonce ->
  update_sub cipher 0ul msg_len msg;
  (**) hash_max_input_norm_lem (get_config nc);
  mix_hash_impl false msg_len cipher st_cs_k st_ck st_h
                (v (Ghost.reveal nonce) <: nat)

let encrypt_and_hash_with_key_fm #nc csi mix_hash_impl =
  fun msg_len msg cipher st_cs_k st_ck st_h nonce ->
  let r1 =
    csi_get_encrypt_with_ad_with_key csi (hash_vs nc) st_h msg_len msg cipher
                                     st_cs_k nonce in
  if is_success r1 then
    let cipher_len = msg_len +! aead_tag_vs in
    (**) hash_max_input_norm_lem (get_config nc);
    let r2 = mix_hash_impl true cipher_len cipher st_cs_k st_ck st_h (v nonce + 1) in
    hash_rtype_to_encrypt_hash r2
  else
    r1

let encrypt_and_hash_fm #nc encrypt_and_hash_no_key_impl
                        encrypt_and_hash_with_key_impl =
  fun has_sk msg_len msg cipher st_cs_k st_ck st_h nonce ->
  if with_norm(has_sk)
  then encrypt_and_hash_with_key_impl msg_len msg cipher st_cs_k st_ck st_h nonce
  else
    let r = encrypt_and_hash_no_key_impl msg_len msg cipher st_cs_k st_ck st_h nonce in
    hash_rtype_to_encrypt_hash r

(**** decrypt_and_hash *)

let decrypt_and_hash_no_key_fm #nc mix_hash_impl =
  fun msg_len msg cipher st_cs_k st_ck st_h nonce ->
  update_sub msg 0ul msg_len cipher;
  (**) hash_max_input_norm_lem (get_config nc);
  mix_hash_impl false msg_len cipher st_cs_k st_ck st_h (v nonce)

let decrypt_and_hash_with_key_fm #nc csi mix_hash_impl =
  fun msg_len msg cipher st_cs_k st_ck st_h nonce ->
  (**) let st : Ghost.erased (symmetric_state_m nc) = mk_ssm st_cs_k st_ck st_h in
  (**) let h0 = HST.get () in
  let r1 =
    csi_get_decrypt_with_ad_with_key csi (hash_vs nc) st_h msg_len msg cipher
                                     st_cs_k nonce in
  if is_success r1 then
    begin
    (**) let h1 = HST.get () in
    (**) let st0_v : Ghost.erased _  = eval_symmetric_state_m h0 st true (v nonce) in
    (**) let res_v : Ghost.erased (eresult (Lib.ByteSequence.bytes & (symmetric_state (get_config nc)))) =
             Spec.decrypt_and_hash h0.[|cipher|] st0_v in
    (**) assert(Res? res_v);
    (**) let msg_v : Ghost.erased _ = match Ghost.reveal res_v with | Res (x, _) -> x in
    (**) decrypt_and_hash_output_len_lemma msg_v st0_v;
    (**) hash_max_input_norm_lem (get_config nc);
    let _ = mix_hash_impl true (msg_len +! aead_tag_vs) cipher st_cs_k st_ck st_h
                          (v nonce + 1) in
    success _
    end
  else
    begin
    (**) let h1 = HST.get () in
    (**) assert(ssm_modifies1 st msg h0 h1);
    decrypt_rtype_to_decrypt_hash r1
    end

#push-options "--z3rlimit 25 --ifuel 1"
let decrypt_and_hash_fm #nc decrypt_and_hash_no_key_impl
                        decrypt_and_hash_with_key_impl =
  fun has_sk msg_len msg cipher st_cs_k st_ck st_h nonce ->
  if with_norm(has_sk) then
    decrypt_and_hash_with_key_impl msg_len msg cipher st_cs_k st_ck st_h nonce
  else
    decrypt_and_hash_no_key_impl msg_len msg cipher st_cs_k st_ck st_h nonce
#pop-options

#push-options "--z3rlimit 100 --ifuel 1"
let split_fm #nc kdf_impl st_cs_k st_ck st_h k1 k2 =
  if hash_is_64 nc then
    begin
    push_frame();
    let temp_k1 : lbuffer uint8 64ul = create 64ul (u8 0) in
    let temp_k2 : lbuffer uint8 64ul = create 64ul (u8 0) in
    let _ = kdf2_no_key kdf_impl st_ck temp_k1 temp_k2 in
    update_sub k1 0ul 32ul (sub temp_k1 0ul 32ul);
    update_sub k2 0ul 32ul (sub temp_k2 0ul 32ul);
    (* Leave no sensitive information on the stack *)
    Lib.Memzero0.memzero #uint8 temp_k1 64ul;
    Lib.Memzero0.memzero #uint8 temp_k2 64ul;
    pop_frame();
    success _
    end
  else
    kdf2_no_key kdf_impl st_ck k1 k2
#pop-options
