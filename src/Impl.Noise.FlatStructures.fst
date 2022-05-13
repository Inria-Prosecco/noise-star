module Impl.Noise.FlatStructures

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
module BS = Lib.ByteSequence
module LB = Lib.Buffer
open Lib.Buffer
open Lib.ByteBuffer

open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Impl.Noise.Types
open Impl.Noise.CipherState
open Impl.Noise.SymmetricState
open Impl.Noise.HandshakeState

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

/// This module provides concrete implementations for some structures used by 
/// Noise (cipher state, symmetric state...) in the form of flattened structures
/// (buffers).

(*** Key pair *)
inline_for_extraction noextract
let keypair_vsv (nc : iconfig) = private_key_vsv nc + public_key_vsv nc
let keypair_vs (nc : iconfig) = size (keypair_vsv nc)
type keypair_t (nc : iconfig) = lbuffer uint8 (keypair_vs nc)

unfold let keypair_gget_priv (#nc : iconfig) (kp : keypair_t nc) :
  GTot (private_key_t nc) =
  gsub kp 0ul (private_key_vs nc)
unfold let keypair_gget_pub (#nc : iconfig) (kp : keypair_t nc) :
  GTot (public_key_t nc) =
  gsub kp (private_key_vs nc) (public_key_vs nc)

let eval_keypair (#nc : iconfig) (h : HS.mem) (kp : keypair_t nc) :
  GTot (keypair (get_config nc)) =
  let priv = keypair_gget_priv kp in
  let pub = keypair_gget_pub kp in
  { priv = eval_private_key h priv; pub = eval_public_key h pub; }

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
let keypair_get_priv (#nc : iconfig) (kp : keypair_t nc) :
  Stack (private_key_t nc)
  (requires (fun h -> live h kp))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == keypair_gget_priv kp /\
              eval_private_key h1 b == (eval_keypair h1 kp).priv)) =
  sub kp 0ul (private_key_vs nc)

inline_for_extraction noextract
let keypair_get_pub (#nc : iconfig) (kp : keypair_t nc) :
  Stack (public_key_t nc)
  (requires (fun h -> live h kp))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == keypair_gget_pub kp /\
              eval_public_key h1 b == (eval_keypair h1 kp).pub)) =
  sub kp (private_key_vs nc) (public_key_vs nc)

let eval_opt_split_keypair (#nc : iconfig) (h : HS.mem)
                           (priv : opt_private_key_t nc) (pub : opt_public_key_t nc) :
  GTot (option (keypair (get_config nc))) =
  if g_is_null priv || g_is_null pub then None
  else Some ({ priv = eval_private_key h priv; pub = eval_public_key h pub; })

(*** Cipher state *)
(**** Definition, getters, setters *)
inline_for_extraction noextract
let cipher_state_vsv : size_nat = aead_key_vsv
let cipher_state_vs = size cipher_state_vsv
let cipher_state_t = lbuffer uint8 cipher_state_vs

inline_for_extraction noextract
let cs_k_offs_v = 0
inline_for_extraction noextract
let cs_k_offs = size cs_k_offs_v

unfold let cs_gget_k (st : cipher_state_t) : GTot aead_key_t =
  gsub st cs_k_offs aead_key_vs

let eval_cipher_state (h : HS.mem) (st : cipher_state_t) (has_key : bool) (n : nat) :
  GTot (st_v:cipher_state{Some? st_v.k == has_key}) =
  let k_v = if has_key then Some (eval_aead_key h (cs_gget_k st)) else None in
  { k = k_v; n = n; }

(* Note that it doesn't make sense to use this function if the cipher state doesn't have a key *)
inline_for_extraction noextract
let cs_get_k (st : cipher_state_t) :
  Stack aead_key_t
  (requires (fun h -> live h st))
  (ensures (fun h0 k h1 -> h0 == h1 /\ live h1 k /\
              k == gsub st 0ul aead_key_vs)) =
  sub st cs_k_offs aead_key_vs

(*** Symmetric state *)
(**** Definition, getters, setters *)
inline_for_extraction noextract
let symmetric_state_vsv (nc : iconfig) : size_nat =
  cipher_state_vsv + chaining_key_vsv nc + hash_vsv nc
let symmetric_state_vs (nc : iconfig) = size (symmetric_state_vsv nc)
type symmetric_state_t (nc : iconfig) = lbuffer uint8 (symmetric_state_vs nc)

inline_for_extraction noextract
let ss_c_state_offs_v = 0
inline_for_extraction noextract
let ss_c_state_offs = size ss_c_state_offs_v
inline_for_extraction noextract
let ss_ck_offs_v = cipher_state_vsv
inline_for_extraction noextract
let ss_ck_offs = size ss_ck_offs_v
inline_for_extraction noextract
let ss_h_offs_v (nc : iconfig) = cipher_state_vsv + chaining_key_vsv nc
inline_for_extraction noextract
let ss_h_offs (nc : iconfig) = size (ss_h_offs_v nc)

unfold let ss_gget_c_state (#nc : iconfig) (st : symmetric_state_t nc) :
  GTot cipher_state_t =
  gsub st ss_c_state_offs cipher_state_vs
unfold let ss_gget_ck (#nc : iconfig) (st : symmetric_state_t nc) :
  GTot (chaining_key_t nc) =
  gsub st ss_ck_offs (chaining_key_vs nc)
unfold let ss_gget_h (#nc : iconfig) (st : symmetric_state_t nc) :
  GTot (hash_t nc) =
  gsub st (ss_h_offs nc) (hash_vs nc)

let eval_key_chain (#nc : iconfig) (h : HS.mem) (k : chaining_key_t nc) :
  GTot (chaining_key (get_config nc)) =
  as_seq h k
let eval_hash (#nc : iconfig) (h : HS.mem) (b : hash_t nc) :
  GTot (hash (get_config nc)) =
  as_seq h b

let eval_symmetric_state (#nc : iconfig) (h : HS.mem) (st : symmetric_state_t nc)
                         (has_key : bool) (nonce : nat):
  GTot (st_v:symmetric_state (get_config nc){Some? st_v.c_state.k == has_key}) =
  let cst_v = eval_cipher_state h (ss_gget_c_state st) has_key nonce in
  let ck_v = eval_key_chain h (ss_gget_ck st) in
  let h_v = eval_hash h (ss_gget_h st) in
  { c_state = cst_v; ck = ck_v; h = h_v; }

inline_for_extraction noextract
let ss_get_c_state (#nc : iconfig) (st : symmetric_state_t nc) :
  Stack cipher_state_t
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st 0ul cipher_state_vs)) =
  sub st ss_c_state_offs cipher_state_vs

inline_for_extraction noextract
let ss_get_ck (#nc : iconfig) (st : symmetric_state_t nc) :
  Stack (chaining_key_t nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st cipher_state_vs (chaining_key_vs nc))) =
  sub st ss_ck_offs (chaining_key_vs nc)

inline_for_extraction noextract
let ss_get_h (#nc : iconfig) (st : symmetric_state_t nc) :
  Stack (hash_t nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st (size (cipher_state_vsv + (chaining_key_vsv nc))) (hash_vs nc))) =
  sub st (ss_h_offs nc) (hash_vs nc)


(*** Handshake state *)
(**** Definition, getters, setters *)
inline_for_extraction noextract
let handshake_state_vsv (nc : iconfig) : size_nat = symmetric_state_vsv nc + 7*(public_key_vsv nc)
let handshake_state_vs (nc : iconfig) = size (handshake_state_vsv nc)
type handshake_state_t (nc : iconfig) = lbuffer uint8 (handshake_state_vs nc)

(* TODO: macros: not constants anymore *)
inline_for_extraction noextract
let hs_sym_state_offs_v = 0
inline_for_extraction noextract
let hs_sym_state_offs = size hs_sym_state_offs_v
inline_for_extraction noextract
let hs_static_offs_v (nc : iconfig) = symmetric_state_vsv nc
inline_for_extraction noextract
let hs_static_offs (nc : iconfig) = size (hs_static_offs_v nc)
inline_for_extraction noextract
let hs_ephemeral_offs_v (nc : iconfig) = symmetric_state_vsv nc + keypair_vsv nc
inline_for_extraction noextract
let hs_ephemeral_offs (nc : iconfig) = size (hs_ephemeral_offs_v nc)
inline_for_extraction noextract
let hs_remote_static_offs_v (nc : iconfig) = symmetric_state_vsv nc + 2 * (keypair_vsv nc)
inline_for_extraction noextract
let hs_remote_static_offs (nc : iconfig) = size (hs_remote_static_offs_v nc)
inline_for_extraction noextract
let hs_remote_ephemeral_offs_v (nc : iconfig) =
  symmetric_state_vsv nc + 2 * (keypair_vsv nc) + public_key_vsv nc
inline_for_extraction noextract
let hs_remote_ephemeral_offs (nc : iconfig) = size (hs_remote_ephemeral_offs_v nc)
inline_for_extraction noextract
let hs_preshared_offs_v (nc : iconfig) =
  symmetric_state_vsv nc + 2 * (keypair_vsv nc) + 2 * (public_key_vsv nc)
inline_for_extraction noextract
let hs_preshared_offs (nc : iconfig) = size (hs_preshared_offs_v nc)

unfold let hs_gget_sym_state (#nc : iconfig) (st : handshake_state_t nc) :
  GTot (symmetric_state_t nc) =
  gsub st hs_sym_state_offs (symmetric_state_vs nc)
unfold let hs_gget_static (#nc : iconfig) (st : handshake_state_t nc) :
  GTot (keypair_t nc) =
  gsub st (hs_static_offs nc) (keypair_vs nc)
unfold let hs_gget_ephemeral (#nc : iconfig) (st : handshake_state_t nc) :
  GTot (keypair_t nc) =
  gsub st (hs_ephemeral_offs nc) (keypair_vs nc)
unfold let hs_gget_remote_static (#nc : iconfig) (st : handshake_state_t nc) :
  GTot (public_key_t nc) =
  gsub st (hs_remote_static_offs nc) (public_key_vs nc)
unfold let hs_gget_remote_ephemeral (#nc : iconfig) (st : handshake_state_t nc) :
  GTot (public_key_t nc) =
  gsub st (hs_remote_ephemeral_offs nc) (public_key_vs nc)
unfold let hs_gget_preshared (#nc : iconfig) (st : handshake_state_t nc) :
  GTot preshared_key_t =
  gsub st (hs_preshared_offs nc) preshared_key_vs

#push-options "--z3rlimit 50"
let eval_handshake_state (#nc : iconfig) (h : mem) (st : handshake_state_t nc) (smi : meta_info) :
  GTot (st_v:handshake_state (get_config nc){
          Some? st_v.sym_state.c_state.k == smi.hsf.sk /\
          Some? st_v.static == smi.hsf.s /\ Some? st_v.ephemeral == smi.hsf.e /\
          Some? st_v.remote_static == smi.hsf.rs /\
          Some? st_v.remote_ephemeral == smi.hsf.re /\
          Some? st_v.preshared == smi.hsf.psk}) =
  let sym_state_v = eval_symmetric_state h (hs_gget_sym_state st) smi.hsf.sk smi.nonce in
  let static_v =
    if smi.hsf.s then Some (eval_keypair h (hs_gget_static st)) else None in
  let ephemeral_v =
    if smi.hsf.e then Some (eval_keypair h (hs_gget_ephemeral st)) else None in
  let remote_static_v =
    if smi.hsf.rs then Some (eval_public_key h (hs_gget_remote_static st))
                  else None in
  let remote_ephemeral_v =
    if smi.hsf.re then Some (eval_public_key h (hs_gget_remote_ephemeral st))
                  else None in
  let preshared_v =
    if smi.hsf.psk then Some (eval_preshared_key h (hs_gget_preshared st)) else None in
  {
    sym_state = sym_state_v;
    static = static_v;
    ephemeral = ephemeral_v;
    remote_static = remote_static_v;
    remote_ephemeral = remote_ephemeral_v;
    preshared = preshared_v;
  }
#pop-options

/// This lemma is very useful to prevent the proofs from exploding
#push-options "--z3rlimit 25"
let eval_handshake_state_same_lem
  (#nc : iconfig) (h0 h1 : mem) (st : handshake_state_t nc) (smi : meta_info) :
  Lemma
  (requires(
    h0.[|st|] `S.equal` h1.[|st|]))
  (ensures(
    eval_handshake_state h1 st smi == eval_handshake_state h0 st smi)) = ()
#pop-options

inline_for_extraction noextract
let hs_get_sym_state (#nc : iconfig) (st : handshake_state_t nc) :
  Stack (symmetric_state_t nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st 0ul (symmetric_state_vs nc))) =
  sub st hs_sym_state_offs (symmetric_state_vs nc)

inline_for_extraction noextract
let hs_get_static (#nc : iconfig) (st : handshake_state_t nc) :
  Stack (keypair_t nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st (symmetric_state_vs nc) (keypair_vs nc))) =
  sub st (hs_static_offs nc) (keypair_vs nc)

inline_for_extraction noextract
let hs_get_ephemeral (#nc : iconfig) (st : handshake_state_t nc) :
  Stack (keypair_t nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st (size (symmetric_state_vsv nc + keypair_vsv nc)) (keypair_vs nc))) =
  sub st (hs_ephemeral_offs nc) (keypair_vs nc)

inline_for_extraction noextract
let hs_get_remote_static (#nc : iconfig) (st : handshake_state_t nc) :
  Stack (public_key_t nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st (size (symmetric_state_vsv nc +  (2 * (keypair_vsv nc)))) (public_key_vs nc))) =
  sub st (hs_remote_static_offs nc) (public_key_vs nc)

inline_for_extraction noextract
let hs_get_remote_ephemeral (#nc : iconfig) (st : handshake_state_t nc) :
  Stack (public_key_t nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st (size (symmetric_state_vsv nc +
                           (2 * (keypair_vsv nc)) + public_key_vsv nc))
                           (public_key_vs nc))) =
  sub st (hs_remote_ephemeral_offs nc) (public_key_vs nc)

inline_for_extraction noextract
let hs_get_preshared (#nc : iconfig) (st : handshake_state_t nc) :
  Stack preshared_key_t
  (requires (fun h -> live h st))
  (ensures (fun h0 b h1 -> h0 == h1 /\ live h1 b /\
              b == gsub st (size (symmetric_state_vsv nc +
                           2 * (keypair_vsv nc + public_key_vsv nc)))
                        preshared_key_vs)) =
  sub st (hs_preshared_offs nc) preshared_key_vs

(**** Conversion between type representations *)
/// We use the fact that tuples are inlined by Karamel to generate clean code.

(***** Key pair *)
let keypair_mt_t_rel (#nc : iconfig) (mkp : keypair_m nc) (kp : keypair_t nc) : Type0 =
  let mpriv, mpub = mkp in
  mpriv == keypair_gget_priv kp /\ mpub == keypair_gget_pub kp

inline_for_extraction noextract
let keypair_t_to_m (#nc : iconfig) (kp : keypair_t nc) :
  Stack (keypair_m nc)
  (requires (fun h -> live h kp))
  (ensures (fun h0 r h1 -> h1 == h0 /\ keypair_mt_t_rel r kp)) =
  keypair_get_priv kp, keypair_get_pub kp

(***** Cipher state *)

let cs_mt_t_rel (mst : cipher_state_m) (st : cipher_state_t) : Type0 =
  let mk = mst in
  mk == cs_gget_k st

inline_for_extraction noextract
let cipher_state_t_to_m (st : cipher_state_t) :
  Stack cipher_state_m
  (requires (fun h -> live h st))
  (ensures (fun h0 r h1 -> h1 == h0 /\ cs_mt_t_rel r st)) =
  cs_get_k st

let csm_modifies1_to_modifies2 (mst : cipher_state_m) (st : cipher_state_t)
                               (#a : Type0) (b : buffer_t MUT a) (h1 h2 : mem) :
 Lemma
 (requires (
   cs_mt_t_rel mst st /\ csm_modifies1 mst b h1 h2))
 (ensures (modifies2 st b h1 h2)) = ()


(***** Symmetric state *)

let ss_mt_t_rel (#nc : iconfig) (mst : symmetric_state_m nc)
                (st : symmetric_state_t nc) : Type0 =
  let mc_state, mck, mh = mst in
  cs_mt_t_rel mc_state (ss_gget_c_state st) /\
  mck == ss_gget_ck st /\ mh == ss_gget_h st

inline_for_extraction noextract
let symmetric_state_t_to_m (#nc : iconfig) (st : symmetric_state_t nc) :
  Stack (symmetric_state_m nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 r h1 ->
            h1 == h0 /\ ss_mt_t_rel r st)) =
  let mc_state = cipher_state_t_to_m (ss_get_c_state st) in
  mc_state, ss_get_ck st, ss_get_h st

let ssm_modifies1_to_modifies2 (#nc : iconfig)
                               (mst : symmetric_state_m nc) (st : symmetric_state_t nc)
                               (#a : Type0) (b : buffer_t MUT a) (h1 h2 : mem) :
 Lemma
 (requires (
   ss_mt_t_rel mst st /\ ssm_modifies1 mst b h1 h2))
 (ensures (modifies2 st b h1 h2)) = ()


(***** Handshake state *)
(****** Definitions *)
(* TODO: handshake_state_t could take parameters defining whether or not to
 * allocate memory for some keys...
 *)

let hs_mt_t_rel (#nc : iconfig) (mst : handshake_state_m nc) (st : handshake_state_t nc) :
  Type0 =
  let msym_state, mstatic, mephemeral, mremote_static,
      mremote_ephemeral, mpreshared = mst in
  ss_mt_t_rel msym_state (hs_gget_sym_state st) /\
  keypair_mt_t_rel mstatic (hs_gget_static st) /\
  keypair_mt_t_rel mephemeral (hs_gget_ephemeral st) /\
  mremote_static == hs_gget_remote_static st /\
  mremote_ephemeral == hs_gget_remote_ephemeral st /\
  mpreshared == hs_gget_preshared st

#push-options "--z3rlimit 50"
inline_for_extraction noextract
let handshake_state_t_to_m (#nc : iconfig) (st : handshake_state_t nc) :
  Stack (handshake_state_m nc)
  (requires (fun h -> live h st))
  (ensures (fun h0 r h1 ->
            h1 == h0 /\ hs_mt_t_rel r st)) =
  let mc_state, mck, mh = symmetric_state_t_to_m (hs_get_sym_state st) in
  [@inline_let] let msym_state = (mc_state, mck, mh) in
  let mspriv, mspub = keypair_t_to_m (hs_get_static st) in
  let mepriv, mepub = keypair_t_to_m (hs_get_ephemeral st) in
  let mremote_static = hs_get_remote_static st in
  let mremote_ephemeral = hs_get_remote_ephemeral st in
  let mpreshared = hs_get_preshared st in
  msym_state, (mspriv, mspub), (mepriv, mepub), mremote_static, mremote_ephemeral, mpreshared
#pop-options

(****** Lemmas *)
let eval_handshake_state_eq (#nc : iconfig) (h : mem)
                            (mst : handshake_state_m nc) (st : handshake_state_t nc)
                            (smi : meta_info) :
  Lemma
  (requires (
    hs_mt_t_rel mst st /\ hs_nn_pred smi mst))
  (ensures (
    eval_handshake_state_m h mst smi ==
    eval_handshake_state h st smi)) = ()

let hsm_modifies1_to_modifies2 (#nc : iconfig)
                               (mst : handshake_state_m nc) (st : handshake_state_t nc)
                               (#a : Type0) (b : buffer_t MUT a) (h1 h2 : mem) :
 Lemma
 (requires (hs_mt_t_rel mst st /\ hsm_modifies1 mst b h1 h2))
 (ensures (modifies2 st b h1 h2)) = ()

#push-options "--z3rlimit 50"
let handshake_state_t_to_m_impl_hsm_inv
  (#nc : iconfig) (h : mem)
  (mst : handshake_state_m nc) (st : handshake_state_t nc) (smi : meta_info) :
  Lemma
  (requires (hs_mt_t_rel mst st /\ live h st /\
             hs_nn_pred smi mst))
  (ensures (hsm_inv h mst smi)) = ()
#pop-options

#push-options "--z3rlimit 25"
let handshake_state_t_to_m_disjoint_impl
  (#nc : iconfig) (mst : handshake_state_m nc) (st : handshake_state_t nc)
  (#t : buftype) (#a : Type0) (#len : size_t) (b : lbuffer_t t a len) :
  Lemma
  (requires (hs_mt_t_rel mst st /\ disjoint st b))
  (ensures (hsm_disjoint mst b)) = ()
#pop-options
