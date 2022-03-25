module Spec.Noise.CryptoPrimitives

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

/// DH : we support Curve25519
// Remark: Noise also supports Curve448, which is not supported by HACL*
module DH = Spec.Agile.DH
open Spec.Agile.DH

/// AEAD : we support AES256 GCM and Chacha20Poly1305
module AEAD = Spec.Agile.AEAD
open Spec.Agile.AEAD

/// Hash : we support SHA2 256, SHA2 512 and Blake2
module Hash = Spec.Agile.Hash
open Spec.Agile.Hash
module HMAC = Spec.Agile.HMAC
open Spec.Agile.HMAC
module HKDF = Spec.Agile.HKDF
open Spec.Agile.HKDF

(* We reopen ByteSequence because [lbytes] is redefined there many times in HACL,
 * and sometimes doesn't have exactly the same definition. *)
open Lib.ByteSequence

open FStar.Mul

/// For .fsti/.fst alignment purposes
val _align_beg : unit

(*** Configuration *)
let is_supported_dh_alg (a : DH.algorithm) =
  match a with
  | DH_Curve25519 -> true
  | _ -> false

type dh_alg = a:DH.algorithm{is_supported_dh_alg a}

let is_supported_aead_alg (a : AEAD.alg) : bool =
  match a with
  | AES256_GCM | CHACHA20_POLY1305 -> true
  | _ -> false

type aead_alg = a:AEAD.alg{is_supported_aead_alg a}

let is_supported_hash_alg (a : Hash.algorithm) : bool =
  match a with
  | SHA2_256 | SHA2_512
  | Blake2S | Blake2B -> true
  | _ -> false

type hash_alg = a:Hash.algorithm{is_supported_hash_alg a}

/// Noise algorithmic configuration:
/// dh algorithm & aead algorithm & hash algorithm
inline_for_extraction noextract
type config = dh_alg & aead_alg & hash_alg

inline_for_extraction noextract
let get_dh_alg (c : config) : dh_alg =
  (* Doesn't normalize correctly at extraction if we write:
   * [> let dha, aead, h = c in dha
   * See: https://github.com/FStarLang/FStar/issues/2038
   *)
  match c with dha, aead, h -> dha

inline_for_extraction noextract
let get_aead_alg (c : config) : aead_alg =
  match c with dha, aead, h -> aead

inline_for_extraction noextract
let get_hash_alg (c : config) : hash_alg =
  match c with dha, aead, h -> h

/// Note that from now onwards, we will often define predicates/functions/types twice:
/// one version will take parameters relative only to the configuration of the operation
/// we consider (DH, AEAD, Hash), the other version will take a Noise configuration
/// as parameter.

(*** Basic type definitions *)

inline_for_extraction
let aprivate_key_size (a : dh_alg) : size_nat = DH.size_key a
inline_for_extraction
let apublic_key_size (a : dh_alg) : size_nat = DH.size_public a

type aprivate_key (a : dh_alg) = lbytes (aprivate_key_size a)
type apublic_key (a : dh_alg) = lbytes (apublic_key_size a)

inline_for_extraction
let private_key_size (nc : config) : size_nat = aprivate_key_size (get_dh_alg nc)
inline_for_extraction
let public_key_size (nc : config) : size_nat = apublic_key_size (get_dh_alg nc)
inline_for_extraction let preshared_key_size : size_nat = 32

type private_key (nc : config) = lbytes (private_key_size nc)
type public_key (nc : config) = lbytes (public_key_size nc)
type preshared_key = lbytes preshared_key_size

// TODO: would be more logical to have private key first
noeq type keypair (nc : config) = {
  pub : public_key nc;
  priv : private_key nc;
}

let mk_keypair (#nc : config) (pub : public_key nc) (priv : private_key nc) =
  Mkkeypair pub priv

(* A hashable key is either a public key or a preshared key *)
type hashable_key (nc : config) =
  b:bytes {length b = public_key_size nc \/ length b = preshared_key_size}


(*** DH *)
val adh :
     #a:dh_alg
  -> aprivate_key a
  -> apublic_key a ->
  Tot (option (apublic_key a))

let dh :
     #nc:config
  -> private_key nc
  -> public_key nc ->
  Tot (option (public_key nc)) =
  fun #nc priv pub ->
  adh #(get_dh_alg nc) priv pub

/// Not used in the Noise technical paper, but useful in practice
// TODO: this can actually never fail
let asecret_to_public :
     #a:dh_alg
  -> aprivate_key a ->
  Tot (option (apublic_key a)) =
  fun #a -> DH.secret_to_public a

let secret_to_public :
     #nc:config
  -> private_key nc ->
  Tot (option (public_key nc)) =
  fun #nc -> asecret_to_public #(get_dh_alg nc)

(*** AEAD *)

inline_for_extraction let aead_key_size : size_nat = 32 (* size fixed by Noise tech. paper *)
inline_for_extraction let aead_tag_size : size_nat = 16 (* size fixed by Noise tech. paper  *)

type aead_key = lbytes aead_key_size (* size fixed by Noise tech. paper *)
type aead_tag = lbytes aead_tag_size (* size fixed by Noise tech. paper *)

/// The nonce used for AEAD encryption/decryption is not secret as it is simply a counter
inline_for_extraction let aead_nonce_size : size_nat = 8
type aead_nonce = range_t U64

inline_for_extraction noextract
let aaead_max_input (a : aead_alg) =
  match a with
  | AEAD.AES256_GCM ->
    (* We want to be able to use the EverCrypt implementation, which has the
     * following requirement, stronger than the requirement in the
     * Agile spec. A cleaner way would be to leave the agile spec requirement
     * here, and change the implementation files so that the user provides
     * upper limits for the input in addition to implementations for the
     * cryptographic primitives. However, 2^31 is very big for a handshake,
     * so there is no point in making things more cumbersome just for that purpose. *)
    pow2 31
  | _ -> AEAD.max_length a

inline_for_extraction noextract
let aead_max_input (nc : config) = aaead_max_input (get_aead_alg nc)

val aaead_encrypt :
     a:aead_alg
  -> aead_key
  -> aead_nonce
  -> aad:bytes{length aad <= aaead_max_input a}
  -> msg:bytes{length msg <= aaead_max_input a} ->
  Tot (r:bytes{length r == length msg + aead_tag_size})

val aaead_decrypt :
     a:aead_alg
  -> aead_key
  -> aead_nonce
  -> aad:bytes{length aad <= aaead_max_input a}
  -> cipher:bytes{length cipher >= aead_tag_size /\
                  length cipher <= aaead_max_input a + aead_tag_size} ->
  Tot (option (r:bytes{length r + aead_tag_size == length cipher}))

val aaead_correctness :
     a:aead_alg
  -> k:aead_key
  -> n:aead_nonce
  -> aad:bytes{length aad <= aaead_max_input a}
  -> msg:bytes{length msg <= aaead_max_input a} ->
  Lemma (
    // Note: due to some typing issues, we can't prove the lemma if
    // we write it with an equality
    match aaead_decrypt a k n aad (aaead_encrypt a k n aad msg) with
    | None -> False
    | Some msg' -> msg' == msg)

let aead_encrypt :
     nc:config
  -> aead_key
  -> aead_nonce
  -> aad:bytes{length aad <= aead_max_input nc}
  -> msg:bytes{length msg <= aead_max_input nc} ->
  Tot (r:bytes{length r == length msg + aead_tag_size}) =
  fun nc k n aad msg ->
  aaead_encrypt (get_aead_alg nc) k n aad msg

let aead_decrypt :
     nc:config
  -> aead_key
  -> aead_nonce
  -> aad:bytes{length aad <= aead_max_input nc}
  -> cipher:bytes{length cipher >= aead_tag_size /\
                  length cipher <= aead_max_input nc + aead_tag_size} ->
  Tot (option (r:bytes{length r + aead_tag_size == length cipher})) =
  fun nc k n aad cipher ->
  aaead_decrypt (get_aead_alg nc) k n aad cipher

let aead_correctness :
     nc:config
  -> k:aead_key
  -> n:aead_nonce
  -> aad:bytes{length aad <= aead_max_input nc}
  -> msg:bytes{length msg <= aead_max_input nc} ->
  Lemma (
    // Note: due to some typing issues, we can't prove the lemma if
    // we write it with an equality
    match aead_decrypt nc k n aad (aead_encrypt nc k n aad msg) with
    | None -> False
    | Some msg' -> msg' == msg) =
  fun nc k n aad msg ->
  aaead_correctness (get_aead_alg nc) k n aad msg

(*** Hash *)
/// We have to explicitly write the match of ``ahash_size`` so that it gets
/// properly inlined at extraction time. The return type refinement is for
/// sanity.
inline_for_extraction noextract
let ahash_size (a : hash_alg) : s:size_nat{s = Hash.hash_length a} =
  match a with
  | MD5 -> 16
  | SHA1 -> 20
  | SHA2_224 -> 28
  | SHA2_256 -> 32
  | SHA2_384 -> 48
  | SHA2_512 -> 64
  | Blake2S -> 32
  | Blake2B -> 64

inline_for_extraction noextract
let hash_size (c : config) : size_nat =
  ahash_size (get_hash_alg c)

inline_for_extraction noextract
type ahash (a : hash_alg) = lbytes (ahash_size a)
type hash (nc : config) = lbytes (hash_size nc)

let ahash_max_input (a : hash_alg) : Tot pos =
  Hash.max_input_length a

let hash_max_input (nc : config) : Tot pos =
  ahash_max_input (get_hash_alg nc)

let ahash_block_size (a : hash_alg) : Tot (s:pos{s = Hash.block_length a}) =
  match a with
  | MD5
  | SHA1
  | SHA2_224
  | SHA2_256 -> 64
  | SHA2_384
  | SHA2_512 -> 128
  | Blake2S -> 64
  | Blake2B -> 128

let hash_block_size (nc : config) : Tot pos =
  ahash_block_size (get_hash_alg nc)

val ado_hash :
     a:hash_alg
  -> input:bytes{length input <= ahash_max_input a} ->
  Tot (ahash a)

let do_hash :
     nc:config
  -> input:bytes{length input <= hash_max_input nc} ->
  Tot (hash nc) =
  fun nc -> ado_hash (get_hash_alg nc)

(**** Some utilities *)
inline_for_extraction noextract
let aead_max_input_norm (nc : config) :
  Tot (l:nat{l = aead_max_input nc}) =
  match get_aead_alg nc with
  | AES256_GCM -> 
    (**) normalize_term_spec(pow2 31);
    2147483648 (* pow2 31 *)
  | CHACHA20_POLY1305 ->
    (**) normalize_term_spec(pow2 32 - 1 - 16);
    4294967279 (* pow2 32 - 1 - 16 *)

inline_for_extraction noextract
let ahash_max_input_norm (a : hash_alg) :
  Tot (l:nat{l = ahash_max_input a}) =
  match a with
  | SHA2_256 ->
    (**) normalize_term_spec(pow2 61 - 1);
    2305843009213693951 (* pow2 61 - 1 *)
  | SHA2_512 ->
    (**) normalize_term_spec(pow2 125 - 1);
    42535295865117307932921825928971026431 (* pow2 125 - 1 *)
  | Blake2S ->
    (**) normalize_term_spec(pow2 64 - 1);
    18446744073709551615 (* pow2 64 - 1 *)
  | Blake2B ->
    (**) normalize_term_spec(pow2 128 - 1);
    340282366920938463463374607431768211455 (* pow2 128 - 1 *)

inline_for_extraction noextract
let hash_max_input_norm (nc : config) :
  Tot (l:nat{l = hash_max_input nc}) =
  ahash_max_input_norm (get_hash_alg nc)

let ahash_max_input_norm_lem (a : hash_alg) :
  Lemma(ahash_max_input a = ahash_max_input_norm a) = ()

let hash_max_input_norm_lem (nc : config) :
  Lemma(hash_max_input nc = hash_max_input_norm nc) = ()

(*** HMAC *)
val ahmac :
  a: hash_alg ->
  key: bytes ->
  data: bytes ->
  Pure (lbytes (ahash_size a))
  (requires (
    Seq.length key + ahash_block_size a < pow2 32 /\
    Seq.length data + ahash_block_size a < pow2 32))
  (ensures fun _ -> True)

let hmac (nc : config) = ahmac (get_hash_alg nc)

(*** HKDF *)
/// HKDF with 3 outputs as defined by the Noise technical paper.
/// We show below that it is equivalent to the generic HKDF defined by using
/// the extract and expand functions defined in HACL*.
let hkdf_s =
  #nc : config ->
  chaining_key : hash nc ->
  key : bytes{length key = 0 \/ length key = 32 \/ length key = public_key_size nc} ->
  Tot (hash nc & hash nc & hash nc)

val hkdf : hkdf_s

let kdf1 : #nc:config -> ck:hash nc -> k:hashable_key nc -> Tot (hash nc) =
  fun #hc ck k ->
  let k1, _, _ = hkdf ck k in
  k1

let kdf2 : #nc:config -> ck:hash nc -> k:hashable_key nc -> Tot (hash nc & hash nc) =
  fun #hc ck k ->
  let k1, k2, _ = hkdf ck k in
  k1, k2

let kdf2_no_key : #nc:config -> ck:hash nc -> Tot (hash nc & hash nc) =
  fun #nc ck ->
  let k1, k2, _ = hkdf ck lbytes_empty in
  k1, k2

let kdf3 : #nc:config -> ck:hash nc -> k:hashable_key nc -> Tot (hash nc & hash nc & hash nc) =
  hkdf

/// HKDF with 3 outputs defined by using the HACL* extract and expand functions
val hacl_hkdf : hkdf_s

/// The two HKDF definitions are equivalent
val hkdf_is_hacl_hkdf :
  #nc : config ->
  chaining_key : hash nc ->
  key : bytes{length key = 0 \/ length key = 32 \/ length key = public_key_size nc} ->
  Lemma(hkdf #nc chaining_key key == hacl_hkdf #nc chaining_key key)

(*** Additional type definitions *)
let is_hashable_size (nc : config) (n : nat) : bool =
  n + hash_size nc <= max_size_t &&
  n + hash_size nc <= hash_max_input nc

/// The length conditions for a plain message to be encryptable through
/// [encrypt_and_hash]. Note that some conditions might be redundant.
let is_plain_message_length (nc : config) (n : nat) : bool =
  (* The plain text must be encryptable *)
  n <= aead_max_input nc &&
  (* The ciphertext (with a tag) must be hashable *)
  is_hashable_size nc (n + aead_tag_size) &&
  (* We can concatenate the cipher text and the tag *)
  n + aead_tag_size <= max_size_t

let is_hashable (nc : config) (s:bytes) : bool = is_hashable_size nc (length s)
type hashable (nc : config) = s:bytes{is_hashable nc s}

type chaining_key (nc : config) = hash nc

type plain_message (nc : config) = s:bytes {is_plain_message_length nc (length s)}
type aead_aad (nc : config) = s:bytes{length s <= aead_max_input nc}

