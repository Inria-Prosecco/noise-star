module Impl.Noise.Types

open FStar.Mul
module HS = FStar.HyperStack
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.RawIntTypes
open Lib.IntTypes

module HST = FStar.HyperStack.ST
open Lib.Sequence
module S = Lib.Sequence
module Seq = FStar.Seq

module B = LowStar.Buffer
open Lib.Buffer
open Lib.ByteBuffer
open LowStar.BufferOps

module Spec = Spec.Noise
open Spec.Noise
open Meta.Noise

module Hash = Spec.Hash.Definitions
module HashImpl = Hacl.Hash.Definitions

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(*** Lemmas for sequences *)
let lemma_slice (#a: Type) (s: S.seq a) (i: nat): Lemma
  (requires (i <= S.length s))
  (ensures (Seq.equal (Seq.append (Seq.slice s 0 i) (Seq.slice s i (Seq.length s))) s))
=
  ()

let lemma_slice_ijk (#a: Type) (s: Seq.seq a) (i j k: nat): Lemma
  (requires (i <= j /\ j <= k /\ k <= Seq.length s))
  (ensures (Seq.equal (Seq.append (Seq.slice s i j) (Seq.slice s j k)) (Seq.slice s i k)))
=
  ()

let lemma_lslice (#a: Type) (#len : size_nat) (s: lseq a len) (i: nat): Lemma
  (requires (i <= len))
  (ensures (equal ((slice s 0 i) @| (slice s i len)) s))
=
  ()

let lemma_lslice_ijk (#a: Type) (#len : size_nat) (s: lseq a len) (i j k: size_nat): Lemma
  (requires (i <= j /\ j <= k /\ k <= len))
  (ensures (equal ((slice s i j) @| (slice s j k)) (slice s i k)))
=
  ()

(*** Potentially null buffers *)
(* TODO: not sure this is ok for the CONST buffers *)
#push-options "--ifuel 1"
inline_for_extraction noextract
let null (#ty : buftype) (#a : Type0) : buffer_t ty a =
  match ty with
  | IMMUT -> LowStar.ImmutableBuffer.inull #a
  | MUT -> LowStar.Buffer.null #a
  | CONST -> LowStar.ConstBuffer.of_buffer (LowStar.Buffer.null #a)
#pop-options

#push-options "--ifuel 1"
let g_is_null (#ty : buftype) (#a : Type0) (b : buffer_t ty a) : GTot bool =
  match ty with
  | IMMUT -> LowStar.Buffer.g_is_null #a #(LowStar.ImmutableBuffer.immutable_preorder a)
                                         #(LowStar.ImmutableBuffer.immutable_preorder a)
                                         b
  | MUT ->   LowStar.Buffer.g_is_null #a #(LowStar.Buffer.trivial_preorder a)
                                         #(LowStar.Buffer.trivial_preorder a)
                                         b
  | CONST -> LowStar.Buffer.g_is_null #a (LowStar.ConstBuffer.as_mbuf b)
#pop-options

inline_for_extraction noextract
val is_null (#ty : buftype) (#a : Type0) (b : buffer_t ty a) :
  Stack bool (requires (fun h -> live h b))
             (ensures  (fun h y h' -> h == h' /\ y == g_is_null b))
#push-options "--ifuel 1"
let is_null #ty #a b =
  match ty with
  | IMMUT -> LowStar.Buffer.is_null #a #(LowStar.ImmutableBuffer.immutable_preorder a)
                                       #(LowStar.ImmutableBuffer.immutable_preorder a) b
  | MUT -> LowStar.Buffer.is_null #a #(LowStar.Buffer.trivial_preorder a)
                                       #(LowStar.Buffer.trivial_preorder a) b
  | CONST -> LowStar.Buffer.is_null #a (LowStar.ConstBuffer.cast b)
#pop-options

unfold let lbuffer_t_or_null (ty : buftype) (a : Type0) (len : size_t) =
  b:buffer_t ty a {~(g_is_null b) ==> length #ty #a b == v len}

type lbuffer_or_null = lbuffer_t_or_null MUT

let unchanged_lbuffer_or_null (#a : Type0) (#len : size_t) (b : lbuffer_or_null a len)
                              (h0 h1 : mem) : Type0 =
  if g_is_null b then True
  else let b' : lbuffer a len = b in h1.[|b'|] `S.equal` h0.[|b'|]

inline_for_extraction noextract
val update_sub_opt :
  #ty : buftype ->
  #a : Type0 ->
  (* Warning: len must be valid for extraction *)
  #len : size_t ->
  dst : lbuffer_or_null a len ->
  src : lbuffer_t_or_null ty a len ->
  Stack unit
  (requires (fun h -> live h dst /\ live h src /\ disjoint dst src /\
                    (g_is_null dst ==> g_is_null src)))
  (ensures (fun h0 _ h1 ->
    (if g_is_null src then modifies0 h0 h1 else modifies1 dst h0 h1) /\
    (if g_is_null src then
      (if g_is_null dst then True else h1.[|dst <: lbuffer_t MUT a len|] `S.equal`
                                    h0.[|dst <: lbuffer_t MUT a len|])
     else h1.[|dst <: lbuffer_t MUT a len|] `S.equal` h0.[|src <: lbuffer_t ty a len|])))
let update_sub_opt #ty #a #len dst src =
  (* The first assignement which is computationally useless allows to prevent
   * non-compilable extraction of the following form if the src parameter is null:
   * [>   if (!(NULL == NULL))
   * [>     memcpy(mremote_static, NULL, (uint32_t)32U * sizeof (void * ));
   * Instead we get:
   * [>   uint8_t *src = NULL;
   * [>   if (!(src == NULL))
   * [>     memcpy(mremote_ephemeral, src, (uint32_t)32U * sizeof(uint_t));
   *)
  let src = src in
  if is_null src then ()
  else update_sub (dst <: lbuffer_t MUT a len) 0ul len src

(* Potentially null buffer as an optional sequence *)
let pn_as_seq (#t : buftype) (#a : Type0) (#len : size_t)
              (h : mem) (b : lbuffer_t_or_null t a len) :
  GTot (option (Seq.lseq a (v len))) =
  if g_is_null b then None else (Some (as_seq h (b <: lbuffer_t t a len)))

(* Convert potentially null buffers known as non-null as sequences *)
let pn_as_nn (#t : buftype) (#a : Type0) (#len : size_t)
             (h : mem) (b : lbuffer_t_or_null t a len) :
  Ghost (lbuffer_t t a len)
  (requires (not (g_is_null b))) (ensures (fun _ -> True)) =
  b

(* Interpret potentially null buffers known as non-null as sequences *)
let nn_as_seq (#t : buftype) (#a : Type0) (#len : size_t)
              (h : mem) (b : lbuffer_t_or_null t a len) :
  Ghost (S.lseq a (v len))
  (requires (not (g_is_null b))) (ensures (fun _ -> True)) =
  as_seq h (b <: lbuffer_t t a len)

(** Updates a sub-buffer typed as potentially null but statically known as non-null *)
inline_for_extraction noextract
val update_nn :
  #ty : buftype ->
  #a : Type0 ->
  #len : size_t ->
  dst : lbuffer_or_null a len{not (g_is_null dst)} ->
  src : lbuffer_t_or_null ty a len{not (g_is_null src)} ->
  Stack unit
  (requires (fun h -> live h dst /\ live h src /\ disjoint dst src))
  (ensures (fun h0 _ h1 ->
    modifies1 dst h0 h1 /\
    (nn_as_seq h1 dst) `S.equal` (nn_as_seq h0 src)))
let update_nn #ty #a #len dst src =
  update_sub (dst <: lbuffer_t MUT a len) 0ul len src

(* TODO: use that *)
unfold let (=$=) (#a : Type) (#len : size_nat) (s1 s2 : lseq a len) = S.equal #a #len s1 s2

(* Conventions:
 * As in F* the type is always written after the variable name (ie: [x : t]),
 * I use suffixes to indicate the variable/types.
 *
 * For types:
 * - #_t : concrete type (state_t is the implementation of type state)
 * For variables:
 * - #_v : value in the spec
 * - #_vsv : value size expressed in a spec type (nat, int, size_nat...)
 * - #_vs : value size expressed as a machine integer
 *)

(*** Configurations *)

/// The general error code, which is used for the primitive functions but also for
/// the API. We define it here and derive sub-error codes from it so that we only
/// have one error data-type in the C code, and don't have to bother with conversions.

type error_code =
| CSuccess
| CIncorrect_transition (* Id function called while state did not have proper status *)
| CPremessage (* Error while processing the premessages *)
| CNo_key (* Missing key *)
| CAlready_key (* Key already received *)
| CRs_rejected_by_policy (* Remote static key rejected by the validation policy *)
| CRs_not_certified (* Remote static key rejected by the payload validation function *)
| CAlready_peer (* We received a remote static while we already know who the remote peer is *)
| CPeer_conflict (* Two peers have the same static key *)
| CUnknown_peer_id (* Couldn't find a peer in the device *)
| CInput_size (* If the input message doesn't have the proper size *)
| CDH_error (* A DH operation failed *)
| CDecrypt_error (* An authenticated decryption failed *)
| CSaturated_nonce (* Nonce is saturated *)
| CEphemeral_generation (* Failed to generate an ephemeral key (because of randomness, or because DH failed) *)
| CSecurity_level (* Security requirement not met *)

/// We sometimes need to assign a number to every error code above
#push-options "--ifuel 1"
inline_for_extraction noextract
let error_code_to_nat (e : error_code) : n:nat{n <= 15} =
  match e with
  | CSuccess -> 0
  | CIncorrect_transition -> 1
  | CPremessage -> 2
  | CNo_key -> 3
  | CAlready_key -> 4
  | CRs_rejected_by_policy -> 5
  | CRs_not_certified -> 6
  | CAlready_peer -> 7
  | CPeer_conflict -> 8
  | CUnknown_peer_id -> 9
  | CInput_size -> 10
  | CDH_error -> 11
  | CDecrypt_error -> 12
  | CSaturated_nonce -> 13
  | CEphemeral_generation -> 14
  | CSecurity_level -> 15
#pop-options

inline_for_extraction noextract
let nat_to_error_code (n : nat{n <= 15}) : error_code =
  match n with
  | 0 -> CSuccess
  | 1 -> CIncorrect_transition
  | 2 -> CPremessage
  | 3 -> CNo_key
  | 4 -> CAlready_key
  | 5 -> CRs_rejected_by_policy
  | 6 -> CRs_not_certified
  | 7 -> CAlready_peer
  | 8 -> CPeer_conflict
  | 9 -> CUnknown_peer_id
  | 10 -> CInput_size
  | 11 -> CDH_error
  | 12 -> CDecrypt_error
  | 13 -> CSaturated_nonce
  | 14 -> CEphemeral_generation
  | 15 -> CSecurity_level

/// Sanity checks
let error_code_to_nat_nat_to_error_code_id_lem (n : nat{n <= 15}) :
  Lemma (error_code_to_nat (nat_to_error_code n) = n) = ()

let nat_to_error_code_id_error_code_to_nat_lem (r : error_code) :
  Lemma (nat_to_error_code (error_code_to_nat r) = r) = ()

inline_for_extraction noextract
type prim_error_code =
  e:error_code{
    match e with
    | CSuccess | CDH_error | CDecrypt_error -> true
    | _ -> false
  }
//| CSuccess
//| CDH_error
//| CDecrypt_error

/// The return type type class.
/// Together with [prim_error_code], we use this type class to conveniently define
/// return types for our functions. The main purpose of [return_type] is to
/// allow to define very precise types computed statically, so that we use unit
/// whenever we can and remove tests statically known to alway succeed.
noeq type return_type = {
  rty : Type0; (* should be eqtype *)
  to_prim_error_code : rty -> Tot prim_error_code;
  success : r:rty{to_prim_error_code r = CSuccess};
  never_fails : b:bool{b ==> (forall (r : rty). to_prim_error_code r = CSuccess)};
}

inline_for_extraction noextract
let rtype (tc : return_type) : Type0 =
  with_norm(tc.rty)

inline_for_extraction noextract
let to_prim_error_code (#tc : return_type) (r : rtype tc) : prim_error_code =
  with_norm(tc.to_prim_error_code r)

inline_for_extraction noextract
let is_success (#tc : return_type) (r : rtype tc) :
  bool =
  with_norm(to_prim_error_code r = CSuccess)

inline_for_extraction noextract
let success (tc : return_type) : r:rtype tc{is_success r} =
  with_norm(tc.success)

inline_for_extraction noextract
let never_fails (tc : return_type) :
  b:bool{b ==> (forall (r : rtype tc). to_prim_error_code #tc r = CSuccess)} =
  (**) assert(rtype tc `subtype_of` tc.rty);
  with_norm(tc.never_fails)

inline_for_extraction noextract
let is_always_success(#tc : return_type) (r : rtype tc) :
  b:bool{b ==> to_prim_error_code r = CSuccess} =
  never_fails tc

/// The implementation configuration.
/// Contains the static hardware preconditions for all the primitives' implementations.
///
/// WARNING:
/// ========
/// EverCrypt and the rest of HACL* don't follow the same convention with regard
/// to the presence of hardware preconditions. More specifically, the EverCrypt
/// implementations which have hardware requirements have related preconditions,
/// while some HACL* functions like the vectorized hash functions don't have any
/// precondition.
/// For this reason, it is recommended not to use directly the functions defined in
/// HACL in order to supply Noise with the required primitives but rather to use the
/// implementations provided in Impl.Noise.CryptoPrimitives, which add the proper
/// preconditions when necessary.

inline_for_extraction noextract
noeq type iconfig =
| IConfig :
     c:config
  -> dh_pre:Ghost.erased Type0
  -> aead_pre:Ghost.erased Type0
  -> hash_pre:Ghost.erased Type0
  -> iconfig

inline_for_extraction noextract
let get_config (inc : iconfig) : config =
  (* Doesn't normalize correctly at extraction if we write:
   * [> let (nc, dh_config, enc_config, dec_config, hash_config) = inc in nc
   * See: https://github.com/FStarLang/FStar/issues/2038
   *)
  match inc with | IConfig nc dh_pre aead_pre hash_pre -> nc

inline_for_extraction noextract
let get_dh_pre (inc : iconfig) : Type0 =
  match inc with | IConfig nc dh_pre aead_pre hash_pre -> dh_pre

inline_for_extraction noextract
let get_aead_pre (inc : iconfig) : Type0 =
  match inc with | IConfig nc dh_pre aead_pre hash_pre -> aead_pre

inline_for_extraction noextract
let get_hash_pre (inc : iconfig) : Type0 =
  match inc with | IConfig nc dh_pre aead_pre hash_pre -> hash_pre

inline_for_extraction noextract
let get_pres (inc : iconfig) : Type0 =
  get_dh_pre inc /\ get_aead_pre inc /\ get_hash_pre inc

/// In the following we define general instances of [return_type]
inline_for_extraction noextract
type unit_return_type : return_type = {
  rty = unit;
  to_prim_error_code = (fun _ -> CSuccess);
  success = ();
  never_fails = true;
}

inline_for_extraction noextract
let prim_error_code_return_type : return_type = {
  rty = prim_error_code;
  to_prim_error_code = (fun r -> r);
  success = CSuccess;
  never_fails = false;
}

inline_for_extraction noextract
type dh_rtype =  
  r:prim_error_code{
    r == CSuccess \/ r == CDH_error}

inline_for_extraction noextract
type dh_return_type : return_type =
  { prim_error_code_return_type with rty = dh_rtype; }

inline_for_extraction noextract
let encrypt_return_type : return_type =
  unit_return_type

inline_for_extraction noextract
type decrypt_rtype : Type0 =
  r:prim_error_code{r == CSuccess \/ r == CDecrypt_error}

inline_for_extraction noextract
let decrypt_return_type : return_type =
  { prim_error_code_return_type with
    rty = decrypt_rtype; }

inline_for_extraction noextract
let hash_return_type : return_type = unit_return_type

inline_for_extraction noextract
let encrypt_hash_return_type : return_type =
  unit_return_type

inline_for_extraction noextract
let decrypt_hash_rtype (has_sk : bool) : Type0 =
  if has_sk then
    r:prim_error_code{
      (r == CSuccess \/ r == CDecrypt_error)}
  else unit

inline_for_extraction noextract
let decrypt_hash_return_type (has_sk : bool) : return_type =
  if has_sk then
    { prim_error_code_return_type with
      rty = decrypt_hash_rtype has_sk; }
  else unit_return_type

inline_for_extraction noextract
type dh_hash_rtype : Type0 = dh_rtype

inline_for_extraction noextract
let dh_hash_return_type : return_type = dh_return_type

inline_for_extraction noextract
let hash_rtype_to_encrypt_hash (r : rtype hash_return_type) :
  r':rtype encrypt_hash_return_type {
    to_prim_error_code r' == to_prim_error_code r} =
  success encrypt_return_type

inline_for_extraction noextract
let hash_rtype_to_decrypt_hash (#has_sk : bool)
                               (r : rtype hash_return_type) :
  r':rtype (decrypt_hash_return_type has_sk) {
    to_prim_error_code r' == to_prim_error_code r} =
  success _

inline_for_extraction noextract
let decrypt_rtype_to_decrypt_hash (r : rtype decrypt_return_type) :
  r':rtype (decrypt_hash_return_type true) {
    to_prim_error_code r' == to_prim_error_code r} = r

inline_for_extraction noextract
let hash_rtype_to_dh_hash (r : rtype hash_return_type) :
  r':rtype dh_hash_return_type {
    is_success r' == is_success r} =
  convert_subtype #dh_rtype #(rtype dh_hash_return_type) CSuccess

inline_for_extraction noextract
let dh_rtype_to_dh_hash (r : rtype dh_return_type) :
  r':rtype dh_hash_return_type {
    to_prim_error_code r' == to_prim_error_code r} = r

(**** DH *)

// Secret to public
inline_for_extraction noextract
type dh_sp_st (a : dh_alg) (pre : Type0) =
  output : lbuffer uint8 (size (apublic_key_size a)) ->
  input : lbuffer uint8 (size (aprivate_key_size a)) ->
  Stack (rtype dh_return_type)
  (requires (fun h -> pre /\ live h output /\ live h input /\
                    disjoint output input))
  (ensures (fun h0 r h1 ->
              modifies1 output h0 h1 /\
              begin let r_v = asecret_to_public #a h0.[|input|] in
              match to_prim_error_code r, r_v with
              | CSuccess, Some dh_v -> h1.[|output|] `S.equal` dh_v
              | CDH_error, None -> True
              | _ -> False
              end))

inline_for_extraction noextract
type dh_st (a : dh_alg) (pre : Type0) =
  dest : lbuffer uint8 (size (apublic_key_size a)) ->
  priv : lbuffer uint8 (size (aprivate_key_size a)) ->
  pub : lbuffer uint8 (size (apublic_key_size a)) ->
  Stack (rtype dh_return_type)
  (requires (fun h -> pre /\ live h dest /\ live h priv /\ live h pub /\
                    disjoint dest priv /\ disjoint dest pub))
  (ensures (fun h0 r h1 ->
              modifies1 dest h0 h1 /\
              begin let r_v = adh #a h0.[|priv|] h0.[|pub|] in
              match to_prim_error_code r, r_v with
              | CSuccess, Some dh_v -> h1.[|dest|] `S.equal` dh_v
              | CDH_error, None -> True
              | _ -> False
              end))

(**** AEAD *)

inline_for_extraction noextract
type aead_encrypt_st (a : aead_alg) (pre : Type0) =
  key : lbuffer uint8 (size aead_key_size) ->
  nonce : pub_uint64 ->
  aad_len : size_t{size_v aad_len <= aaead_max_input a} ->
  aad : lbuffer uint8 aad_len ->
  plen : size_t{size_v plen <= aaead_max_input a /\ size_v plen + aead_tag_size <= max_size_t} ->
  plain : lbuffer uint8 plen ->
  cipher : lbuffer uint8 (size (encrypt_size (size_v plen))) ->
  Stack (rtype encrypt_return_type)
  (requires (fun h ->
    pre /\ live h key /\ live h aad /\ live h plain /\ live h cipher /\
    disjoint key cipher /\ disjoint plain cipher /\ disjoint aad cipher /\ (* TODO: disjoint_or_equal plain cipher *)
    disjoint plain aad))
  (ensures (fun h0 r h1 ->
    modifies1 cipher h0 h1 /\
    is_success r /\ (* sanity check *)
    h1.[|cipher|] `S.equal` aaead_encrypt a h0.[|key|] (v nonce) h0.[|aad|] h0.[|plain|]))

inline_for_extraction noextract
type aead_decrypt_st (a : aead_alg) (pre : Type0) =
  key : lbuffer uint8 (size aead_key_size) ->
  nonce : pub_uint64 ->
  aad_len : size_t{size_v aad_len <= aaead_max_input a} ->
  aad : lbuffer uint8 aad_len ->
  plen : size_t{size_v plen <= aaead_max_input a /\ size_v plen + aead_tag_size <= max_size_t} ->
  plain : lbuffer uint8 plen ->
  cipher : lbuffer uint8 (size (encrypt_size (size_v plen))) ->
  Stack (rtype decrypt_return_type)
  (requires (fun h ->
    pre /\ live h key /\ live h aad /\ live h plain /\ live h cipher /\
    disjoint key plain /\ disjoint cipher plain /\ disjoint aad plain /\
    disjoint cipher aad))
  (ensures (fun h0 r h1 ->
    modifies1 plain h0 h1 /\
    begin match to_prim_error_code r, aaead_decrypt a h0.[|key|] (v nonce) h0.[|aad|] h0.[|cipher|] with
    | CDecrypt_error, None -> True
    | CSuccess, Some plain_v -> h1.[|plain|] `S.equal` plain_v
    | _ -> False
    end))

(**** Hash *)
/// We need a hash algorithm in the 3 following situations:
/// - to hash a buffer
/// - to hash a hash with some data
/// - for HMAC
/// In order to make things simple and leave room for implementation possibilities
/// and potential optimisations, we require 3 functions for hash: do_hash,
/// do_hash2 and HMAC. Note that it is more flexible and easier to use than
/// requiring, for instance, init, update and finish for an incremental hash...
/// Note that we assume all the hash functions have the same precondition,
/// which seems quite natural. If it is not the case, the resulting
/// precondition for the Noise functions is the conjunction of all the preconditions
/// of all the cryptographic primitives, meaning that it has no impact in practice,
/// as we can take as precondition for all the hash functions the conjunction
/// of the hash preconditions.

inline_for_extraction noextract
type do_hash_st (a : hash_alg) (pre : Type0) =
  output : lbuffer uint8 (size (ahash_size a)) ->
  inlen : size_t{size_v inlen <= ahash_max_input a} ->
  input : lbuffer uint8 inlen ->
  Stack (rtype hash_return_type)
  (requires (fun h ->
    live h output /\ live h input /\ disjoint input output))
  (ensures (fun h0 _ h1 ->
    modifies1 output h0 h1 /\
    h1.[|output|] `S.equal` ado_hash a h0.[|input|]))

inline_for_extraction noextract
type do_hash2_st (a : hash_alg) (pre : Type0) =
  (* The hash is used as input and output *)
  hash : lbuffer uint8 (size (ahash_size a)) ->
  inlen : size_t ->
  input : lbuffer uint8 inlen ->
  Stack (rtype hash_return_type)
  (requires (fun h ->
    live h hash /\ live h input /\
    ahash_size a + size_v inlen <= max_size_t /\
    ahash_size a + size_v inlen <= ahash_max_input a))
  (ensures (fun h0 _ h1 ->
    modifies1 hash h0 h1 /\
    h1.[|hash|] `S.equal` ado_hash a (Seq.append h0.[|hash|] h0.[|input|])))

inline_for_extraction noextract
type hmac_st (a : hash_alg) (pre : Type0) =
  output : lbuffer uint8 (size (ahash_size a)) ->
  keylen : size_t{size_v keylen + ahash_block_size a < pow2 32} ->
  key : lbuffer uint8 keylen ->
  datalen : size_t{size_v datalen + ahash_block_size a < pow2 32} ->
  data : lbuffer uint8 datalen ->
  Stack (rtype hash_return_type)
  (requires (fun h ->
    live h output /\ live h key /\ live h data /\
    disjoint key output))
  (ensures (fun h0 _ h1 ->
    modifies1 output h0 h1 /\
    h1.[|output|] `S.equal` ahmac a h0.[|key|] h0.[|data|]))    

(**** Configurations *)
/// Tuple containing implementations for a configuration. We add an additional
/// parameter for hardware preconditions, required by some functions implemented
/// with Vale.

/// Cryptographic primitive implementation: (pre, prim_impl)

inline_for_extraction noextract
let cprim_impl (pre : Type0) (f : Type0 -> Type) :
  Type =
  f pre

inline_for_extraction noextract
let idh_sp_type (nc : iconfig) : Type =
  dh_sp_st (get_dh_alg (get_config nc)) (get_dh_pre nc)

inline_for_extraction noextract
let idh_type (nc : iconfig) : Type =
  dh_st (get_dh_alg (get_config nc)) (get_dh_pre nc)

inline_for_extraction noextract
let iaead_encrypt_type (nc : iconfig) : Type =
  aead_encrypt_st (get_aead_alg (get_config nc)) (get_aead_pre nc)

inline_for_extraction noextract
let iaead_decrypt_type (nc : iconfig) : Type =
  aead_decrypt_st (get_aead_alg (get_config nc)) (get_aead_pre nc)

inline_for_extraction noextract
let ido_hash_type (nc : iconfig) : Type =
  do_hash_st (get_hash_alg (get_config nc)) (get_hash_pre nc)

inline_for_extraction noextract
let ido_hash2_type (nc : iconfig) : Type =
  do_hash2_st (get_hash_alg (get_config nc)) (get_hash_pre nc)

inline_for_extraction noextract
let ihmac_type (nc : iconfig) : Type =
  hmac_st (get_hash_alg (get_config nc)) (get_hash_pre nc)

inline_for_extraction noextract
noeq type config_impls (inc : iconfig) =
  | Config_impls :
    ci_dh_sp : idh_sp_type inc ->
    ci_dh : idh_type inc ->
    ci_aead_encrypt : iaead_encrypt_type inc ->
    ci_aead_decrypt : iaead_decrypt_type inc ->
    ci_do_hash1 : ido_hash_type inc ->
    ci_do_hash2 : ido_hash2_type inc ->
    ci_hmac : ihmac_type inc ->
    config_impls inc

/// Functions getters
inline_for_extraction noextract
let idh_sp (#nc : iconfig) (ci : config_impls nc) :
  Tot (idh_sp_type nc) =
  match ci with | Config_impls dh_sp dhf enc dec h1 h2 hmac -> dh_sp

inline_for_extraction noextract
let idh (#nc : iconfig) (ci : config_impls nc) :
  Tot (idh_type nc) =
  match ci with | Config_impls dh_sp dhf enc dec h1 h2 hmac -> dhf

inline_for_extraction noextract
let iaead_encrypt (#nc : iconfig) (ci : config_impls nc) :
  Tot (iaead_encrypt_type nc) =
  match ci with | Config_impls dh_sp dhf enc dec h1 h2 hmac -> enc

inline_for_extraction noextract
let iaead_decrypt (#nc : iconfig) (ci : config_impls nc) :
  Tot (iaead_decrypt_type nc) =
  match ci with | Config_impls dh_sp dhf enc dec h1 h2 hmac -> dec

inline_for_extraction noextract
let ido_hash (#nc : iconfig) (ci : config_impls nc) :
  Tot (ido_hash_type nc) =
  match ci with | Config_impls dh_sp dhf enc dec h1 h2 hmac -> h1

inline_for_extraction noextract
let ido_hash2 (#nc : iconfig) (ci : config_impls nc) :
  Tot (ido_hash2_type nc) =
  match ci with | Config_impls dh_sp dhf enc dec h1 h2 hmac -> h2

inline_for_extraction noextract
let ihmac (#nc : iconfig) (ci : config_impls nc) :
  Tot (ihmac_type nc) =
  match ci with | Config_impls dh_sp dhf enc dec h1 h2 hmac -> hmac

(*** General types *)
inline_for_extraction noextract
let norm_with_eq (#a: Type) (x: a) : Tot (x':a{x' == x}) =
  with_norm x

inline_for_extraction noextract
let ahash_vsv (a : hash_alg) : size_nat = norm_with_eq(ahash_size a)
inline_for_extraction
let ahash_vs (a : hash_alg) : size_t = size (ahash_vsv a)

inline_for_extraction noextract
let hash_vsv (nc : iconfig) : size_nat = norm_with_eq(hash_size (get_config nc))
inline_for_extraction noextract
let hash_vs (nc : iconfig) = size (hash_vsv nc)
inline_for_extraction noextract
type hash_t (nc : iconfig) = lbuffer uint8 (hash_vs nc)

inline_for_extraction noextract
let aead_key_vsv : size_nat = aead_key_size
inline_for_extraction noextract
let aead_key_vs = size aead_key_vsv
inline_for_extraction noextract
type aead_key_t = lbuffer uint8 aead_key_vs
inline_for_extraction noextract
type opt_aead_key_t = lbuffer_or_null uint8 aead_key_vs
inline_for_extraction noextract
type aead_nonce_t = pub_uint64

inline_for_extraction noextract
let aead_aad_vsv (nc : iconfig) : size_nat = norm_with_eq(hash_size (get_config nc))
inline_for_extraction noextract
let aead_aad_vs (nc : iconfig) = size (aead_aad_vsv nc)
inline_for_extraction noextract
type aead_aad_t (nc : iconfig) = lbuffer uint8 (aead_aad_vs nc)

inline_for_extraction noextract
let aead_tag_vsv : size_nat = aead_tag_size
inline_for_extraction noextract
let aead_tag_vs = size aead_tag_vsv
inline_for_extraction noextract
type aead_tag_t = lbuffer uint8 aead_tag_vs

inline_for_extraction noextract
let chaining_key_vsv (nc : iconfig) : size_nat = hash_vsv nc
inline_for_extraction noextract
let chaining_key_vs (nc : iconfig) = size (chaining_key_vsv nc)
inline_for_extraction noextract
type chaining_key_t (nc : iconfig) = lbuffer uint8 (chaining_key_vs nc)

inline_for_extraction noextract
let hashable_size_t (nc : iconfig) = n:size_t{is_hashable_size (get_config nc) (size_v n)}
inline_for_extraction noextract
type hashable_t (nc : iconfig) (len : hashable_size_t nc) = lbuffer uint8 len

inline_for_extraction noextract
type hashable_key_t (nc : iconfig) =
  b:buffer uint8 {length b = public_key_size (get_config nc) \/ length b = preshared_key_size}

inline_for_extraction noextract
type plain_message_len_t (nc : iconfig) =
  s:size_t { is_plain_message_length (get_config nc) (v s) }
inline_for_extraction noextract
type plain_message_t (nc : iconfig) (len : plain_message_len_t nc) = lbuffer uint8 len

(*** keys, keypair *)
inline_for_extraction noextract
let private_key_vsv (nc : iconfig) = norm_with_eq(private_key_size (get_config nc))
inline_for_extraction noextract
let private_key_vs (nc : iconfig) = size (private_key_vsv nc)
inline_for_extraction noextract
type private_key_t (nc : iconfig) = lbuffer uint8 (private_key_vs nc)

inline_for_extraction noextract
let public_key_vsv (nc : iconfig) = norm_with_eq(public_key_size (get_config nc))
inline_for_extraction noextract
let public_key_vs (nc : iconfig) = size (public_key_vsv nc)
inline_for_extraction noextract
type public_key_t (nc : iconfig) = lbuffer uint8 (public_key_vs nc)

let eval_private_key (#nc : iconfig) (h : HS.mem) (k : private_key_t nc) :
  GTot (private_key (get_config nc)) =
  as_seq h k
let eval_public_key (#nc : iconfig) (h : HS.mem) (k : public_key_t nc) :
  GTot (public_key (get_config nc)) =
  as_seq h k

inline_for_extraction noextract
let preshared_key_vsv = preshared_key_size
inline_for_extraction noextract
let preshared_key_vs = size preshared_key_vsv
inline_for_extraction noextract
type preshared_key_t = lbuffer uint8 preshared_key_vs

let eval_preshared_key (h : HS.mem) (k : preshared_key_t) : GTot preshared_key =
  as_seq h k

inline_for_extraction noextract
type opt_public_key_t (nc : iconfig) = lbuffer_or_null uint8 (public_key_vs nc)
inline_for_extraction noextract
type opt_private_key_t (nc : iconfig) = lbuffer_or_null uint8 (private_key_vs nc)
inline_for_extraction noextract
type opt_preshared_key_t = lbuffer_or_null uint8 preshared_key_vs

let eval_opt_private_key (#nc : iconfig) (h : mem) (b : opt_public_key_t nc) :
  GTot (option (public_key (get_config nc))) =
  if g_is_null b then None else Some (eval_public_key h b)
let eval_opt_public_key (#nc : iconfig) (h : mem) (b : opt_public_key_t nc) :
  GTot (option (public_key (get_config nc))) =
  if g_is_null b then None else Some (eval_public_key h b)
let eval_opt_preshared_key (h : mem) (b : opt_preshared_key_t) :
  GTot (option preshared_key) =
  if g_is_null b then None else Some (eval_preshared_key h b)

inline_for_extraction //noextract
type keypair_m (nc : iconfig) =
  opt_private_key_t nc & opt_public_key_t nc

inline_for_extraction noextract
let mk_keypair_m (#nc : iconfig) (priv : opt_private_key_t nc) (pub : opt_public_key_t nc) :
  Tot (keypair_m nc) =
  priv, pub

inline_for_extraction noextract
let kpm_get_priv (#nc : iconfig) (kp : keypair_m nc) : opt_private_key_t nc =
  match kp with priv, pub -> priv

inline_for_extraction noextract
let kpm_get_pub (#nc : iconfig) (kp : keypair_m nc) : opt_public_key_t nc =
  match kp with priv, pub -> pub

let unchanged_keypair_m (#nc : iconfig) (kp : keypair_m nc)
                        (h0 h1 : mem) : Type0 =
  unchanged_lbuffer_or_null (kpm_get_priv kp) h0 h1 /\
  unchanged_lbuffer_or_null (kpm_get_pub kp) h0 h1

(** If [b] is true, [buf] must be non-null *)
let buffer_nn_pred (b : bool) (#t : buftype) (#a : Type0) (#len : size_t)
                   (buf : lbuffer_t_or_null t a len) : GTot bool =
  if b then not (g_is_null buf) else true

(** If [b] is true, both keys in [kp] must be non-null *)
let keypair_nn_pred (#nc : iconfig) (b : bool) (kp : keypair_m nc) : GTot bool =
  if b then not (g_is_null (kpm_get_priv kp)) && not (g_is_null (kpm_get_pub kp)) else true

let eval_keypair_m (#nc : iconfig) (h : HS.mem)
                   (kp : keypair_m nc{~(g_is_null (kpm_get_priv kp)) /\
                                      ~(g_is_null (kpm_get_pub kp))}) :
  GTot (keypair (get_config nc)) =
  { priv = nn_as_seq h (kpm_get_priv kp); pub = nn_as_seq h (kpm_get_pub kp); }
let eval_opt_keypair_m (#nc : iconfig) (b : bool) (h : HS.mem)
                       (kp: keypair_m nc{keypair_nn_pred b kp}) :
  GTot (option (keypair (get_config nc))) =
  if b then Some (eval_keypair_m h kp) else None

(* Aliasing predicates *)
let live_kpm (#nc : iconfig) (h : mem) (kp : keypair_m nc) : GTot Type0 =
  live h (kpm_get_priv kp) /\ live h (kpm_get_pub kp)

let keypair_loc (#nc : iconfig) (kp : keypair_m nc) : GTot B.loc =
  B.loc_union (loc (kpm_get_priv kp)) (loc (kpm_get_pub kp))

let disjoint_kpm (#nc : iconfig) (kp : keypair_m nc) : Type0 =
  B.loc_disjoint (loc (kpm_get_priv kp)) (loc (kpm_get_pub kp))

let kpm_loc_disjoint (#nc : iconfig) (kp : keypair_m nc) (l : B.loc) : GTot Type0 =
  B.loc_disjoint (keypair_loc kp) l

let kpm_disjoint (#nc : iconfig) (kp : keypair_m nc)
                 (#t : buftype) (#a : Type0) (#len : size_t)
                 (b : lbuffer_t t a len) : GTot Type0 =
  B.loc_disjoint (keypair_loc kp) (loc b)

let kpm_is_valid (#nc : iconfig) (h : mem) (kp : keypair_m nc) (not_null : bool) :
  Type0 =
  live_kpm h kp /\ disjoint_kpm kp /\
  (not_null ==> (~(g_is_null (kpm_get_priv kp)) /\ ~(g_is_null (kpm_get_pub kp))))

inline_for_extraction noextract
val update_keypair_opt :
  #nc : iconfig ->
  dst : keypair_m nc ->
  src_priv : opt_private_key_t nc ->
  src_pub : opt_public_key_t nc ->
  Stack unit
  (requires (fun h -> live_kpm h dst /\ live h src_priv /\ live h src_pub /\
                    disjoint_kpm dst /\
                    kpm_loc_disjoint dst (B.loc_union (loc src_priv) (loc src_pub)) /\
                    (g_is_null src_priv <==> g_is_null src_pub) /\
                    ((g_is_null (kpm_get_priv dst) || g_is_null (kpm_get_pub dst)) ==>
                       g_is_null src_priv)
                    ))
  (ensures (fun h0 _ h1 ->
    (if g_is_null src_priv then modifies0 h0 h1
     else modifies (B.loc_union (loc (kpm_get_priv dst)) (loc (kpm_get_pub dst))) h0 h1) /\
    begin
    let src = (src_priv, src_pub) in
    if not (g_is_null src_priv)
    then eval_keypair_m h1 dst == eval_keypair_m h0 src
    else True
    end))

let update_keypair_opt #nc dst src_priv src_pub =
  if is_null src_priv then () else
    begin
    update_sub ((kpm_get_priv dst) <: private_key_t nc) 0ul (private_key_vs nc)
               (src_priv <: private_key_t nc);
    update_sub ((kpm_get_pub dst) <: public_key_t nc) 0ul (public_key_vs nc)
               (src_pub <: public_key_t nc)
    end
