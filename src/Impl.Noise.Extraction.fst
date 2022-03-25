module Impl.Noise.Extraction

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
//open Impl.Noise.PatternMessages.Definitions

module T = FStar.Tactics
open FStar.Tactics
open FStar.String
module String = FStar.String

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(*** Configuration implementation *)
module Crypto = Impl.Noise.CryptoPrimitives

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module KeyedHash = Spec.Blake2

module ImplCFields = Hacl.Impl.Curve25519.Fields.Core
module ImplC64 = Hacl.Curve25519_64
module ImplPolyFields = Hacl.Impl.Poly1305.Fields
module ImplBlake2Core = Hacl.Impl.Blake2.Core

inline_for_extraction noextract
type config_impls_params (nc : config) =
  dh_field_spec (get_dh_alg nc) &
  aead_field_spec (get_aead_alg nc) &
  hash_field_spec (get_hash_alg nc)

inline_for_extraction noextract
let cip_get_dh_fs (#nc : config) (cip : config_impls_params nc) :
  dh_field_spec (get_dh_alg nc) =
  match cip with dh_fs, aead_fs, hash_fs -> dh_fs

inline_for_extraction noextract
let cip_get_aead_fs (#nc : config) (cip : config_impls_params nc) :
  aead_field_spec (get_aead_alg nc) =
  match cip with dh_fs, aead_fs, hash_fs -> aead_fs

inline_for_extraction noextract
let cip_get_hash_fs (#nc : config) (cip : config_impls_params nc) :
  hash_field_spec (get_hash_alg nc) =
  match cip with dh_fs, aead_fs, hash_fs -> hash_fs

inline_for_extraction noextract
let compile_iconfig (#nc : config) (cpi : config_impls_params nc) :
  Tot iconfig =
  match cpi with dh_fs, aead_fs, hash_fs ->
  [@inline_let] let dh_pre = dh_pre #(get_dh_alg nc) dh_fs in
  [@inline_let] let aead_pre = aead_pre #(get_aead_alg nc) aead_fs in
  [@inline_let] let hash_pre = hash_pre #(get_hash_alg nc) hash_fs in
  IConfig nc dh_pre aead_pre hash_pre

/// We sometimes need to help type inference
inline_for_extraction noextract
let convert_type (#a1 : Type) (#a2 : Type{a1 == a2}) (x : a1) : y:a2{x === y} =
  x

#push-options "--ifuel 1"
inline_for_extraction noextract
let compile_config_impls (#nc : config) (cip : config_impls_params nc) :
  config_impls (compile_iconfig cip) =
  (* Below, we don't write [let dh_fs, aead_fs, hash_fs = cip in] because it
   * doesn't normalize correctly at extraction *)
  [@inline_let] let dh_fs = cip_get_dh_fs cip in
  [@inline_let] let aead_fs = cip_get_aead_fs cip in
  [@inline_let] let hash_fs = cip_get_hash_fs cip in
  (* DH *)
  [@inline_let] let dh_alg = get_dh_alg nc in
  [@inline_let] let dh_sp_impl = dh_sp_m #(get_dh_alg nc) dh_fs in
  [@inline_let] let dh_impl = dh_m #(get_dh_alg nc) dh_fs in
  (* AEAD *)
  [@inline_let] let aead_alg = get_aead_alg nc in
  [@inline_let] let aead_enc_impl = aead_encrypt_m #aead_alg aead_fs in
  [@inline_let] let aead_dec_impl = aead_decrypt_m #aead_alg aead_fs in
  (* Hash *)
  [@inline_let] let hash_alg = get_hash_alg nc in
  [@inline_let] let do_hash_impl = do_hash_m #hash_alg hash_fs in
  [@inline_let] let do_hash2_impl = do_hash2_m #hash_alg hash_fs in
  [@inline_let] let hmac_impl = hmac_m #hash_alg hash_fs in
  (* Return *)
  Config_impls dh_sp_impl dh_impl aead_enc_impl aead_dec_impl do_hash_impl do_hash2_impl hmac_impl
#pop-options


(*** Tactics *)

(**** Top-level declarations (splice) *)
/// The following tactics use a [config_impls_params] to choose
/// the proper cryptographic primitives implementations for extraction, and
/// use them to generate the "basic" Noise functions (i.e.: the cipher/symmetric/
/// handshake states functions) so that the user doesn't have to do it by hand.
let print_dbg (debug : bool) (s : string) : Tac unit =
  if debug then print s

type extract_decl_params = option string & bool (* name, inline_for_extraction *)

noextract
let get_extract_bool (p : extract_decl_params) : bool =
  Some? (fst p)

noextract
let get_name (p : extract_decl_params{Some? (fst p)}) : string =
  Some?.v (fst p)

noextract
let get_inline_for_extraction (p : extract_decl_params) : bool =
  snd p

noextract
let make_cur_module_fv (x : string) : Tac fv =
  pack_fv (List.snoc (cur_module(), x))

noextract
type extract_decls_params = {
  (* Primitives *)
  dh_sp : extract_decl_params;
  dh : extract_decl_params;
  aead_encrypt : extract_decl_params;
  aead_decrypt : extract_decl_params;
  do_hash : extract_decl_params;
  do_hash2 : extract_decl_params;
  hmac : extract_decl_params;
  ci : extract_decl_params; (* instance of [config_impls (compile_iconfig nc cip)] *)
  (* KDF and cipher state *)
  kdf : extract_decl_params;
  encrypt_with_ad_with_key : extract_decl_params;
  decrypt_with_ad_with_key : extract_decl_params;
  csi : extract_decl_params; (* instance of [cs_impls (compile_iconfig nc cip)] *)
  (* Symmetric state *)
  initialize_symmetric : extract_decl_params;
  mix_key : extract_decl_params;
  mix_hash : extract_decl_params;
  mix_key_and_hash : extract_decl_params;
  encrypt_and_hash_no_key : extract_decl_params;
  encrypt_and_hash_with_key : extract_decl_params;
  encrypt_and_hash : extract_decl_params;
  decrypt_and_hash_no_key : extract_decl_params;
  decrypt_and_hash_with_key : extract_decl_params;
  decrypt_and_hash : extract_decl_params;
  split : extract_decl_params;
  ssi : extract_decl_params; (* instance of [ss_impls (compile_iconfig nc cip)] *)
  dh_update_sym_state : extract_decl_params;
  (* Handshake state *)
  ssdhi : extract_decl_params; (* instance of [ssdh_impls (compile_iconfig nc cip)] *)
}

noextract
let extract_decl_params_add_prefix_suffix (p : extract_decl_params)
                                          (prefix suffix : string) :
  extract_decl_params =
  match p with
  | Some s, b -> Some (String.concat "" [prefix; s; suffix]), b
  | None, b -> None, b

noextract
let extract_decls_params_add_prefix_suffix (p : extract_decls_params)
                                           (prefix suffix : string) :
  extract_decls_params =
  let Mkextract_decls_params dh_sp dh enc dec h h2 hmac ci kdf enc_ad dec_ad csi init_sym mix_k mix_h
                             mix_kh enc_nk enc_wk enc_h dec_nk dec_wk dec_h split
                             ssi dh_update ssdhi = p in
  let f = (fun x -> extract_decl_params_add_prefix_suffix x prefix suffix) in
  Mkextract_decls_params (f dh_sp) (f dh) (f enc) (f dec) (f h) (f h2) (f hmac) (f ci) (f kdf)
                         (f enc_ad) (f dec_ad) (f csi)
                         (f init_sym) (f mix_k) (f mix_h) (f mix_kh)
                         (f enc_nk) (f enc_wk) (f enc_h)
                         (f dec_nk) (f dec_wk) (f dec_h) (f split)
                         (f ssi) (f dh_update) (f ssdhi)

/// The default extraction parameters. Are defined by using Jason Donenfeld's IKpsk2
/// implementation as model (https://git.zx2c4.com/wireguard-linux-compat) and so that
/// the output is pretty and concise.
noextract
type default_extract_decls_params = {
  dh_sp = Some "dh_secret_to_public", false;
  dh = Some "dh", false;
  ci = Some "ci", true;
  aead_encrypt = Some "aead_encrypt", false;
  aead_decrypt = Some "aead_decrypt", false;
  do_hash = Some "hash", false;
  do_hash2 = Some "mix_hash", false;
  hmac = Some "hmac", false;
  kdf = Some "kdf", false;
  encrypt_with_ad_with_key = None, false;
  decrypt_with_ad_with_key = None, false;
  csi = Some "csi", true;
  initialize_symmetric = None, false;
  mix_key = None, false;
  mix_hash = None, false;
  mix_key_and_hash = Some "mix_psk", false;
  encrypt_and_hash_no_key = None, false;
  encrypt_and_hash_with_key = Some "encrypt_and_hash", false;
  encrypt_and_hash = None, false;
  decrypt_and_hash_no_key = None, false;
  decrypt_and_hash_with_key = Some "decrypt_and_hash", false;
  decrypt_and_hash = None, false;
  split = None, false;
  ssi = Some "ssi", true;
  dh_update_sym_state = Some "mix_dh", false;
  ssdhi = Some "ssdhi", true;
}

/// The extraction parameters for debugging: generate top-level declarations for
/// all the functions and data structures. One advantage is that if something is
/// ill-typed, we fail early.
noextract
type debug_extract_decls_params = {
  dh_sp = Some "dh_secret_to_public", false;
  dh = Some "dh", false;
  ci = Some "ci", true;
  aead_encrypt = Some "aead_encrypt", false;
  aead_decrypt = Some "aead_decrypt", false;
  do_hash = Some "hash", false;
  do_hash2 = Some "hash2", false;
  hmac = Some "hmac", false;
  kdf = Some "kdf", false;
  encrypt_with_ad_with_key = Some "encrypt_with_ad_with_key", false;
  decrypt_with_ad_with_key = Some "decrypt_with_ad_with_key", false;
  csi = Some "csi", true;
  initialize_symmetric = Some "initialize_symmetric", false;
  mix_key = Some "mix_key", false;
  mix_hash = Some "mix_hash", false;
  mix_key_and_hash = Some "mix_key_and_hash", false;
  encrypt_and_hash_no_key = Some "encrypt_and_hash_no_key", false;
  encrypt_and_hash_with_key = Some "encrypt_and_hash_with_key", false;
  encrypt_and_hash = Some "encrypt_and_hash", false;
  decrypt_and_hash_no_key = Some "decrypt_and_hash_no_key", false;
  decrypt_and_hash_with_key = Some "decrypt_and_hash_with_key", false;
  decrypt_and_hash = Some "decrypt_and_hash", false;
  split = Some "split", false;
  ssi = Some "ssi", true;
  dh_update_sym_state = Some "mix_dh", false;
  ssdhi = Some "ssdhi", true;
}

noextract
let print_declaration (sg : sigelt_view{Sg_Let? sg}) : Tac unit =
  let Sg_Let _ lb = sg in
  // There should be only one declaration, really
  match lb with
  | [lb] ->
    let Mklb_view name _ ty body = inspect_lb lb in
  //  let Sg_Let _ name _ ty body = sg in
    let msg = String.concat "\n" [
      "[> Generated declaration:";
      "--name:";
      implode_qn (inspect_fv name);
      "--body:";
      term_to_string body;
      "--type:";
      term_to_string ty;
      "]"] in
    print msg
  | _ -> fail "Invalid case in print_declaration"

/// Optionnally generates a declaration for the term given by [body].
/// If it generates a declaration: it returns an updated declarations list together
/// with an fvar representing the top-level declaration.
/// Otherwise, doesn't update the declarations list and returns [body].
/// The returned term allows to use [body] in later declarations (by using the
/// new fvar if a new declaration was generated, or by using the body directly
/// otherwise).
#push-options "--ifuel 1"
noextract
let generate_declaration (debug : bool)
                         (params : extract_decl_params)
                         (body ty : term)
                         (dl : decls) :
  Tac (decls & term) =
  if get_extract_bool params then
    let name = make_cur_module_fv (get_name params) in
    let lb = pack_lb ({lb_fv = name;
                       lb_us = [];
                       lb_typ = ty;
                       lb_def = body}) in
    let sg : sigelt_view = Sg_Let false [lb] in
    let decl : sigelt = pack_sigelt sg in
    let decl =
      if get_inline_for_extraction params then
        let decl = set_sigelt_quals [ NoExtract; Inline_for_extraction ] decl in
        let decl = set_sigelt_attrs [ `(noextract_to "Kremlin") ] decl in
        decl
      else decl
    in
    let tm = pack (Tv_FVar name) in
    if debug then print_declaration sg;
    decl :: dl, tm
  else dl, body
#pop-options

(* Returns a list of declarations and a term embedding a [config_impls (compile_iconfig nc cip)] *)
noextract
let generate_crypto_declarations (debug : bool)
                                 (#nc : config)
                                 (impls_params : config_impls_params nc)
                                 (extract_params : extract_decls_params) :
  Tac (decls & term) =
  let dl : decls = [] in
  (* Compiled configuration *)
  (* Note that if we don't quote the two following terms now, they get evaluated,
   * leading to very big terms at quotation time later - preventing F* to
   * typecheck in a reasonable time *)
  let qnci = quote (compile_iconfig impls_params) in
  let qimpls = quote (compile_config_impls impls_params) in
  (* DH *)
  let dl, dh_sp_impl =
    generate_declaration debug extract_params.dh_sp
                         (`(idh_sp (`#qimpls)))
                         (`(idh_sp_type (`#qnci))) dl in
  let dl, dh_impl =
    generate_declaration debug extract_params.dh
                         (`(idh (`#qimpls)))
                         (`(idh_type (`#qnci))) dl in
  (* AEAD encrypt *)
  let dl, aead_encrypt_impl =
    generate_declaration debug extract_params.aead_encrypt
                         (`(iaead_encrypt (`#qimpls)))
                         (`(iaead_encrypt_type (`#qnci))) dl in
  (* AEAD decrypt *)
  let dl, aead_decrypt_impl =
    generate_declaration debug extract_params.aead_decrypt
                         (`(iaead_decrypt (`#qimpls)))
                         (`(iaead_decrypt_type (`#qnci))) dl in
  (* Hash *)
  let dl, do_hash_impl =
    generate_declaration debug extract_params.do_hash
                         (`(ido_hash (`#qimpls)))
                         (`(ido_hash_type (`#qnci))) dl in
  let dl, do_hash2_impl =
    generate_declaration debug extract_params.do_hash2
                         (`(ido_hash2 (`#qimpls)))
                         (`(ido_hash2_type (`#qnci))) dl in
  let dl, hmac_impl =
    generate_declaration debug extract_params.hmac
                         (`(ihmac (`#qimpls)))
                         (`(ihmac_type (`#qnci))) dl in
  (* Generate the embedded [config_impls] instance by replacing the functions
   * by their (potential) declarations *)
  // let impls_tm =
  //   `((`#dh_impl),
  //     (`#aead_encrypt_impl),
  //     (`#aead_decrypt_impl),
  //     (`#do_hash_impl))
  let impls_tm =
    `(Config_impls
      (`#dh_sp_impl)
      (`#dh_impl)
      (`#aead_encrypt_impl)
      (`#aead_decrypt_impl)
      (`#do_hash_impl)
      (`#do_hash2_impl)
      (`#hmac_impl))
  in
  let impls_ty = quote (config_impls (compile_iconfig #nc impls_params)) in
  let dl, impls_tm =
    generate_declaration debug extract_params.ci impls_tm impls_ty dl in
  List.Tot.rev dl, impls_tm

(** For debugging [generate_crypto_declarations]:
module Spec = Spec.Noise.Instances

let impls_params : config_impls_params Spec.Noise.Instances.wgc =
  ImplCFields.M51, ImplPolyFields.M32, ImplBlake2Core.M32

let generate_ #nc impls_params extract_params =
  let dl, _ = generate_crypto_declarations true #nc impls_params extract_params in dl

%splice[(* dh; aead_encrypt; aead_decrypt; hash *)]
(generate_ impls_params debug_extract_decls_params)

 --- End of debugging *)

(* Returns a list of declarations and a term embedding a [ssdh_impls nc] *)
noextract
let generate_intermediate_declarations (debug : bool)
                                       (qnc : term) (* embeds a [iconfig] *)
                                       (qimpls : term) (* embeds a [config_impls nc] *)
                                       (params : extract_decls_params) :
  Tac (decls & term) =
  let dl : decls = [] in
  (** KDF and cipher state *)
  (* KDF *)
  let dl, kdf_impl =
    generate_declaration debug params.kdf (`(kdf_m (`#qimpls))) (`(kdf_st (`#qnc))) dl in
  (* Encrypt with ad *)
  let dl, encrypt_with_ad_with_key_impl =
    generate_declaration debug params.encrypt_with_ad_with_key
                         (`(encrypt_with_ad_with_key_m (`#qimpls)))
                         (`(encrypt_with_ad_with_key_st (`#qnc))) dl in
  (* Decrypt with ad *)
  let dl, decrypt_with_ad_with_key_impl =
    generate_declaration debug params.decrypt_with_ad_with_key
                         (`(decrypt_with_ad_with_key_m (`#qimpls)))
                         (`(decrypt_with_ad_with_key_st (`#qnc))) dl in
  (* cs_impls - no declaration - note that we can't unquote it so far, because
   * it may rely on declarations not yet added to the context *)
  let csi : term = `((`#qimpls, `#kdf_impl,
              `#encrypt_with_ad_with_key_impl,
              `#decrypt_with_ad_with_key_impl) <: cs_impls (`#qnc)) in
  let dl, csi =
    generate_declaration debug params.csi csi (`cs_impls (`#qnc)) dl in
  (** Symmetric state *)
  (* Initialize symmetric *)
  let dl, initialize_symmetric_impl =
    generate_declaration debug params.initialize_symmetric
                         (`(initialize_symmetric_m (initialize_symmetric_fm (`#qimpls))))
                         (`(initialize_symmetric_st (`#qnc))) dl in
  (* Mix key *)
  let dl, mix_key_impl =
    generate_declaration debug params.mix_key
                         (`(mix_key_fm (`#csi)))
                         (`(mix_key_fst (`#qnc))) dl in
  (* Mix hash *)
  let dl, mix_hash_impl =
    generate_declaration debug params.mix_hash
                         (`(mix_hash_fm (`#csi)))
                         (`(mix_hash_fst (`#qnc))) dl in
  (* Mix key and hash *)
  let dl, mix_key_and_hash_impl =
    generate_declaration debug params.mix_key_and_hash
                         (`(mix_key_and_hash_fm (`#csi) (`#mix_hash_impl)))
                         (`(mix_key_and_hash_fst (`#qnc))) dl in
  (* Encrypt and hash no key *)
  let dl, encrypt_and_hash_no_key_impl =
    generate_declaration debug params.encrypt_and_hash_no_key
                         (`(encrypt_and_hash_no_key_fm (`#mix_hash_impl)))
                         (`(encrypt_and_hash_no_key_fst (`#qnc))) dl in
  (* Encrypt and hash with key *)
  let dl, encrypt_and_hash_with_key_impl =
    generate_declaration debug params.encrypt_and_hash_with_key
                         (`(encrypt_and_hash_with_key_fm (`#csi) (`#mix_hash_impl)))
                         (`(encrypt_and_hash_with_key_fst (`#qnc))) dl in
  (* Encrypt and hash *)
  let dl, encrypt_and_hash_impl =
    generate_declaration debug params.encrypt_and_hash
      (`(encrypt_and_hash_m (encrypt_and_hash_fm (`#encrypt_and_hash_no_key_impl)
                                                 (`#encrypt_and_hash_with_key_impl))))
      (`(encrypt_and_hash_st (`#qnc))) dl in
  (* Decrypt and hash no key *)
  let dl, decrypt_and_hash_no_key_impl =
    generate_declaration debug params.decrypt_and_hash_no_key
                         (`(decrypt_and_hash_no_key_fm (`#mix_hash_impl)))
                         (`(decrypt_and_hash_no_key_fst (`#qnc))) dl in
  (* Decrypt and hash with key *)
  let dl, decrypt_and_hash_with_key_impl =
    generate_declaration debug params.decrypt_and_hash_with_key
                         (`(decrypt_and_hash_with_key_fm (`#csi) (`#mix_hash_impl)))
                         (`(decrypt_and_hash_with_key_fst (`#qnc))) dl in
  (* Decrypt and hash *)
  let dl, decrypt_and_hash_impl =
    generate_declaration debug params.decrypt_and_hash
      (`(decrypt_and_hash_m (decrypt_and_hash_fm (`#decrypt_and_hash_no_key_impl)
                                                 (`#decrypt_and_hash_with_key_impl))))
      (`(decrypt_and_hash_st (`#qnc))) dl in
  (* Split *)
  let dl, split_impl =
    generate_declaration debug params.split
      (`(split_m (split_fm (`#kdf_impl))))
      (`(split_st (`#qnc))) dl in
  (* ss_impls *)
  let ssi : term = `((`#csi), (`#initialize_symmetric_impl),
                     (mix_key_m (`#mix_key_impl)),
                     (mix_hash_m (`#mix_hash_impl)),
                     (mix_key_and_hash_m (`#mix_key_and_hash_impl)),
                     (`#encrypt_and_hash_impl),
                     (`#decrypt_and_hash_impl),
                     (`#split_impl)) in
  let dl, ssi =
    generate_declaration debug params.ssi ssi (`ss_impls (`#qnc)) dl in
  (** Handshake state *)
  (* DH update *)
  let dl, dh_update_impl =
    generate_declaration debug params.dh_update_sym_state
      (`(dh_update_sym_state_fm (`#ssi)))
      (`(dh_update_sym_state_fst (`#qnc))) dl in
  (* ssdh_impls *)
  let ssdhi : term = `((`#ssi), (dh_update_m (`#dh_update_impl))) in
  let dl, ssdhi =
    generate_declaration debug params.ssdhi ssdhi (`ssdh_impls (`#qnc)) dl in
  (* The new declarations were added at the beginning of the list, so we need
   * to reverse it *)
  List.Tot.rev dl, ssdhi

/// The function to be used by the user to generate the declarations of the "basic"
/// Noise functions, used to generate the send/receive (pre) message functions.
/// Returns: (declarations, qnc, qssdhi)
noextract
let generate_config_declarations (debug : bool)
                                 (#nc : config)
                                 (impls_params : config_impls_params nc)
                                 (extract_params : extract_decls_params)
                                 (iconfig_name : string) :
  Tac (decls & term & term) =
  let dl1, qimpls = generate_crypto_declarations debug #nc impls_params extract_params in
  let dl2, qnc =
    generate_declaration debug (Some iconfig_name, true)
                               (quote (compile_iconfig #nc impls_params))
                               (`iconfig) [] in
  let dl3, qssdhi =
    generate_intermediate_declarations debug qnc qimpls extract_params in
  List.append dl1 (List.append dl2 dl3), qnc, qssdhi


(**** Normalization *)

noextract
let proj_ids = [
  `%__proj__Mkmeta_info__item__hsf;
  `%__proj__Mkmeta_info__item__nonce;
  `%__proj__Mkhandshake_state_flags__item__sk;
  `%__proj__Mkhandshake_state_flags__item__s;
  `%__proj__Mkhandshake_state_flags__item__e;
  `%__proj__Mkhandshake_state_flags__item__rs;
  `%__proj__Mkhandshake_state_flags__item__re;
  `%__proj__Mkhandshake_state_flags__item__psk;
  `%__proj__Mkhandshake_pattern__item__premessage_ri;
  `%__proj__Mkhandshake_pattern__item__premessage_ir;
  `%__proj__Mkhandshake_pattern__item__messages;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_pis;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_pie;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_prs;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_pre;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_is;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_ie;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_rs;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_re;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_ss;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_ee;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_se;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_es;
  `%__proj__Mkhandshake_pattern_flags__item__hsk_psk;
  `%__proj__Mktuple2__item___1;
  `%__proj__Mktuple2__item___2
]

noextract
let update_smi_ids = [
  (* meta_info *)
  `%send_message_update_smi;
  `%receive_message_update_smi;
  `%send_tokens_update_smi;
  `%receive_tokens_update_smi;
  `%send_token_update_smi;
  `%receive_token_update_smi;
  (* handshake_state_flags *)
  `%send_tokens_update_hsf;
  `%receive_tokens_update_hsf;
  `%send_token_update_hsf;
  `%receive_token_update_hsf;
  (* nonce *)
  `%message_update_nonce; (* not necessary *)
  `%tokens_update_nonce;
  `%tokens_update_sk_nonce;
  `%token_update_sk_nonce;
  `%token_update_nonce;
  (* symmetric key *)
  `%tokens_update_sym_key_flag; (* not necessary *)
  `%token_update_sym_key_flag;
]

noextract
let simplify_smi_ids = List.append proj_ids update_smi_ids

(* TODO: [meta_ids] is only used to simplify the pattern compilation.
 * We should be able to make it smaller *)
noextract
let meta_ids = List.append [  
  `%get_config;
  `%iconfig;
  `%config;
  `%config_impls;
  `%get_dh_alg;
  `%get_aead_alg;
  `%get_hash_alg;

  `%get_premessage;
  `%opt_list_to_list_or_empty;
  `%opt_encrypt_size;
  `%encrypt_size;
  `%opt_decrypt_size;
  `%decrypt_size;
  `%get_message;

  `%wf_hs;
  `%hs;

  `%handshake_state_cleared_flags;
  `%hskf_uses_is;
  `%hskf_uses_ie;
  `%hskf_uses_rs;
  `%hskf_uses_re;
  `%compute_hsk_pre_msgs_flags;

  `%compute_premessages_post_smi;
  `%handshake_pattern_smi;
  `%handshake_messages_pre_smi;

  `%compute_hsk_pretoken_flags;
  `%compute_hsk_premessage_flags;
  `%handshake_pattern_cleared_flags;
  `%compute_hsk_pre_msgs_flags;
  `%compute_hsk_token_flags;
  `%compute_hsk_msg_flags;
  `%compute_hsk_msgs_flags_aux;
  `%compute_hsk_msgs_flags;
  `%compute_hsk_flags;
  `%chskf_check_is_psk;

  `%csend_message_pre_smi;
  `%creceive_message_pre_smi;
  `%csend_premessage_pre_smi;
  `%creceive_premessage_pre_smi;
  `%initialize_post_smi;
  `%csend_premessage_ppost_smi;
  `%receive_premessage_update_smi;
  `%receive_pretoken_update_smi;

  `%crawl_handshake_messages;
  `%crawl_messages_update_smi;
  `%send_message_update_smi;
  `%receive_message_update_smi;
  `%send_token_update_smi;
  `%receive_token_update_smi;

  `%token_update_sym_key_flag;
  `%tokens_update_sym_key_flag;
  `%List.Tot.index;
  `%List.Tot.splitAt;
  `%fst;
  `%snd;
  `%List.Tot.hd;
  `%List.Tot.tl;
  `%List.Tot.tail;
  
  `%is_even;
] simplify_smi_ids

#push-options "--ifuel 1"
noextract
let rec is_in_searched_types (debug : bool)
                             (type_ids : list string) (arity : nat) (ty : term) :
  Tac (option string) =
  match inspect ty with
  | Tv_App hd a ->
    print_dbg debug "Tv_App:";
    print_dbg debug (term_to_string ty);
    if arity > 0 then is_in_searched_types debug type_ids (arity-1) hd
    else None
  | Tv_Arrow bv c ->
    print_dbg debug "Tv_Arrow:";
    print_dbg debug (term_to_string ty);
     begin match inspect_comp c with
     | C_Total ret_ty _ ->
       is_in_searched_types debug type_ids arity ret_ty
     | _ -> None
     end
  | Tv_FVar fv ->
    print_dbg debug "Tv_FVar:";
    print_dbg debug (term_to_string ty);
    let fname = implode_qn (inspect_fv fv) in
    if List.mem fname type_ids then Some fname else None
  | Tv_Abs bv body ->
    print_dbg debug "Tv_Abs:";
    print_dbg debug (term_to_string ty);
    None
  | _ -> None
#pop-options

#push-options "--ifuel 1"
noextract
let get_searched_typed_term_id (debug : bool) (type_ids : list string) (arity : nat)
                               (e : env) (t : term) :
  Tac (option string) =
  try
    print_dbg debug "[> get_searched_typed_term_id:";
    print_dbg debug (term_to_string t);
    let tv = inspect (tc e t) in
    print_dbg debug (term_to_string tv);
    begin match is_in_searched_types debug type_ids arity tv with
    | Some type_id ->
      begin
      print_dbg debug "type matches:";
      print_dbg debug (term_to_string t);
      match inspect t with
      | Tv_FVar fv ->
        let fname = implode_qn (inspect_fv fv) in
        if debug then
          begin
          print_dbg debug (String.concat "" ["Found ["; type_id; "]:"]);
          print_dbg debug fname
          end;
        Some fname
      | _ -> None
      end
    | None -> None
    end
  with | _ -> None
#pop-options

(* So far the only match branch we really need is the [Tv_App] *)
#push-options "--ifuel 1"
noextract
let rec find_typed_instances (debug : bool) (type_ids : list string) (arity : nat)
                             (e : env) (t : term) :
  Tac (list string) =
  match inspect t with
  | Tv_App hd (a, _) ->
    let l1 = find_typed_instances debug type_ids arity e hd in
    let l2 = find_typed_instances debug type_ids arity e a in
    List.append l1 l2
  | Tv_Abs bv body ->
    let e' = push_binder e bv in
    find_typed_instances debug type_ids arity e' body
  | Tv_Let refcb attrs bv def body ->
    let l1 = find_typed_instances debug type_ids arity e def in
    let e' = push_binder e (mk_binder bv) in
    let l2 = find_typed_instances debug type_ids arity e' body in
    List.append l1 l2
  | Tv_FVar fv ->
    begin match get_searched_typed_term_id debug type_ids arity e t with
    | None -> []
    | Some s -> [s]
    end
  | _ -> []
#pop-options

noextract
let simplify_impl_getter (debug : bool) (struct_id : string) (getters_ids : list string) () :
  Tac unit =
  print_dbg debug "[> Start: simplify_impl_getter";
  let g = cur_goal () in
  let e = cur_env () in
  begin match term_as_formula g with
  | Comp (Eq _) l r ->
    (* Find the instance and simplify it *)
    let inames = find_typed_instances debug [struct_id] 1 e l in
    if List.length inames <> 1 then
      fail "[> simplify_impl_getter Did not find the proper number of hski instances";
    let simpl_ids = List.append inames getters_ids in
    (* Note that we also do iota redution, because we want to unfold the
     * [handshake_functions_impls_id] but also simplify the function getter *)
    norm [delta_only simpl_ids; iota];
    let g' = cur_goal () in
    print_dbg debug "result:";
    print_dbg debug (term_to_string g')
  | _ -> ()
  end;
  print_dbg debug "[> End: simplify_impl_getter"

noextract
let wf_handshake_pattern_id = `%wf_handshake_pattern

noextract
let find_pattern_instances (debug : bool) (e : env) (t : term) : Tac (list string) =
  find_typed_instances debug [wf_handshake_pattern_id] 0 e t

(* Normalize completely all the instances of [wf_handshake_pattern] that can be
 * found *)
noextract
let normalize_pattern (debug : bool) () : Tac unit =
  print_dbg debug "[> Start: normalize_pattern";
  let g = cur_goal () in
  let e = cur_env () in
  begin match term_as_formula g with
  | Comp (Eq _) l r ->
    let inames = find_pattern_instances debug e l in
    let simpl_ids = List.append inames meta_ids in
    norm [delta_only simpl_ids]
  | _ -> ()
  end;
  print_dbg debug "[> End: normalize_pattern"
