module Spec.Noise.CryptoPrimitives

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
module S = Lib.Sequence
open FStar.Seq

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

/// DH : we support Curve25519
// Remark: Noise also supports Curve448
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

friend Spec.Agile.HKDF

/// For .fsti/.fst alignment purposes
let _align_beg = ()

(*** DH *)

let adh #a = DH.dh a

(*** AEAD *)

let aaead_encrypt a k n aad msg =
  match a with
  | AES256_GCM ->
    (* We encode the nonce as BIG endian *)
    let n8 = uint_to_bytes_be (u64 n) in
    AEAD.encrypt #AES256_GCM k n8 aad msg
  | CHACHA20_POLY1305 ->
    (* We encode the nonce as LITTLE endian *)
    let n8 = uint_to_bytes_le (u64 n) in
    let n12 = (create 4 (u8 0)) @| n8 in
    AEAD.encrypt #CHACHA20_POLY1305 k n12 aad msg

let aaead_decrypt a k n aad cipher =
  match a with
  | AES256_GCM ->
    (* We encode the nonce as BIG endian *)
    let n8 = uint_to_bytes_be (u64 n) in
    AEAD.decrypt #AES256_GCM k n8 aad cipher
  | CHACHA20_POLY1305 ->
    (* We encode the nonce as LITTLE endian *)
    let n8 = uint_to_bytes_le (u64 n) in
    let n12 = (create 4 (u8 0)) @| n8 in
    AEAD.decrypt #CHACHA20_POLY1305 k n12 aad cipher

let aaead_correctness a k n aad msg =
  match a with
  | AES256_GCM ->
    let n8 = uint_to_bytes_be (u64 n) in
    AEAD.correctness #AES256_GCM k n8 aad msg
  | CHACHA20_POLY1305 ->
    let n8 = uint_to_bytes_le (u64 n) in
    let n12 = (create 4 (u8 0)) @| n8 in
    AEAD.correctness #CHACHA20_POLY1305 k n12 aad msg

(*** Hash *)
let ado_hash a input =
  Hash.hash a input

(*** HMAC *)
let ahmac a =
  fun key data ->
  (**) ahash_max_input_norm_lem a;
  HMAC.hmac a key data

(*** HKDF *)
let hkdf #nc ck k =
  let const1 = create 1 (u8 0x1) in
  let const2 = create 1 (u8 0x2) in
  let const3 = create 1 (u8 0x3) in
  let extracted = hmac nc ck k in
  let first = hmac nc extracted const1 in
  let second = hmac nc extracted (Seq.append first const2) in
  let third = hmac nc extracted (Seq.append second const3) in
  first, second, third

let hacl_hkdf #nc ck k =
  let a = get_hash_alg nc in
  (**) ahash_max_input_norm_lem a;
  let extracted = HKDF.extract a ck k in
  let expanded = HKDF.expand a extracted Seq.empty (3 * hash_size nc) in
  Seq.slice expanded 0 (hash_size nc),
  Seq.slice expanded (hash_size nc) (2 * (hash_size nc)),
  Seq.slice expanded (2 * (hash_size nc)) (3 * (hash_size nc))

let hkdf_is_hacl_hkdf #nc ck k =
  let h = hacl_hkdf #nc ck k in
  let a = get_hash_alg nc in
  (**) ahash_max_input_norm_lem a;
  let extracted = HKDF.extract a ck k in
  let expanded = HKDF.expand a extracted Seq.empty (3 * hash_size nc) in
  assert(extracted == hmac nc ck k);
  assert(expanded == HKDF.expand a extracted Seq.empty (3 * hash_size nc));
  let len = 3 * hash_size nc in
  let prk = extracted in
  let open Spec.Agile.HMAC in
  let tlen = hash_length a in
  let n = len / tlen in
  assert(n = 3);
  let hmac = HMAC.hmac a prk in
  let f = expand_loop a prk Seq.empty n in
  let f_eq (i : nat{i < n}) (tag : a_spec a i) :
    Lemma(
      let t = hmac (tag @| Seq.create 1 (u8 (i + 1))) in
      f i tag == (t, t))
    [SMTPat (f i tag)] =
    let t = hmac (tag @| Seq.create 1 (u8 (i + 1))) in
    let t1, t2 = f i tag in
    assert(t1 == hmac (tag @| Seq.empty @| Seq.create 1 (u8 (i + 1))));
    assert((tag @| Seq.empty @| Seq.create 1 (u8 (i + 1)))
           `Seq.equal` (tag @| Seq.create 1 (u8 (i + 1))))
  in
  let blocks0 = S.generate_blocks tlen n 0 (a_spec a) f Seq.empty in
  let blocks1 = S.generate_blocks tlen n 1 (a_spec a) f Seq.empty in
  let blocks2 = S.generate_blocks tlen n 2 (a_spec a) f Seq.empty in
  let blocks3 = S.generate_blocks tlen n n (a_spec a) f Seq.empty in
  let tag, output = blocks3 in
  assert(n * tlen = len);
  assert(output == expanded);
  (* blocks0 *)
  S.eq_generate_blocks0 tlen n (a_spec a) f Seq.empty;
  assert(blocks0 == (Seq.empty, Seq.empty));
  (* blocks1 *)
  S.unfold_generate_blocks tlen n (a_spec a) f Seq.empty 0;
  assert(blocks1 == (let acc', s' = f 0 Seq.empty in acc', Seq.append Seq.empty s'));
  assert((Seq.empty @| Seq.create 1 (u8 1)) `Seq.equal` Seq.create 1 (u8 1));
  assert((Seq.empty @| Seq.create 1 (u8 1)) == Seq.create 1 (u8 1));
  let h0 = hmac (Seq.empty @| Seq.create 1 (u8 1)) in
  (* I don't understand why, but the proof doesn't work without this *)
  let hmac_same_input_eq (x y : S.lseq uint8 1) :
    Lemma (requires (Seq.equal x y))
    (ensures (hmac x == hmac y)) = ()
  in
  hmac_same_input_eq (Seq.create 1 (u8 1)) (Seq.empty @| Seq.create 1 (u8 1));
  let h0' = hmac (Seq.create 1 (u8 1)) in
  assert(h0 == h0');
  assert((h0, h0) == f 0 Seq.empty);
  assert(blocks1 == (h0, Seq.append Seq.empty h0));
  assert((Seq.empty @| h0) `Seq.equal` h0);
  assert(blocks1 == (h0, h0));
  (* blocks2 *)
  S.unfold_generate_blocks tlen n (a_spec a) f Seq.empty 1;
  assert(
    blocks2 ==
    (let acc, s = blocks1 in
     let acc', s' = f 1 acc in
     acc', Seq.append s s'));
  assert(blocks2 == (let acc', s' = f 1 h0 in acc', Seq.append h0 s'));
  let h1 = hmac (h0 @| Seq.create 1 (u8 2)) in
  assert((h1, h1) == f 1 h0);
  assert(blocks2 == (h1, h0 @| h1));
  (* blocks3 *)
  S.unfold_generate_blocks tlen n (a_spec a) f Seq.empty 2;
  assert(
    blocks3 ==
    (let acc, s = blocks2 in
     let acc', s' = f 2 acc in
     acc', Seq.append s s'));
  assert(blocks3 == (let acc', s' = f 2 h1 in acc', Seq.append (h0 @| h1) s'));
  let h2 = hmac (h1 @| Seq.create 1 (u8 3)) in
  assert((h2, h2) == f 2 h1);
  assert(blocks3 == (h2, (h0 @| h1) @| h2));
  (* Conclusion *)
  let h0', h1', h2' = h in
  assert(Seq.equal h2' h2);
  assert(Seq.equal h1' h1);
  assert(Seq.equal h0' h0)
