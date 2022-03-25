module Spec.Noise.API.Device.Lemmas

open Lib.ByteSequence
open Spec.Noise.API.State.Definitions
module State = Spec.Noise.API.State.Definitions
open Spec.Noise.API.Device.Definitions
friend Spec.Noise.API.Device.Definitions
module M = Spec.Noise.Map
open Spec.Noise.CryptoPrimitives
open FStar.List.Tot
open Spec.Noise.Utils

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** Invariant preservation *)
(**** Add peer *)
val add_peer_get_distinct_ids_lem :
     #dc:dconfig
  -> dv:device dc
  -> pinfo:dc.dc_info
  -> rs:option (public_key dc.dc_nc)
  -> psk:option preshared_key ->
  Lemma
  (requires
    dv_peers_counter_invariant dv /\
    peers_pairwise_distinct_ids dv.dv_peers)
  (ensures (
    match add_peer_get dv pinfo rs psk with
    | None -> True
    | Some (p, dv') ->
      dv_peers_counter_invariant dv' /\
      peers_pairwise_distinct_ids dv'.dv_peers))

#push-options "--fuel 1"
let add_peer_get_distinct_ids_lem #dc dv pinfo rs psk =
  match add_peer_get dv pinfo rs psk with
  | None -> ()
  | Some (p, dv') ->
    for_all_mem (peer_has_smaller_id dv.dv_peers_counter) dv.dv_peers;
    for_all_mem (peer_has_smaller_id dv'.dv_peers_counter) dv.dv_peers;
    assert(dv_peers_counter_invariant dv');
    for_all_mem (peers_distinct_ids p) dv.dv_peers
#pop-options

val add_peer_get_distinct_statics_lem :
     #dc:dconfig
  -> dv:device dc
  -> pinfo:dc.dc_info
  -> rs:option (public_key dc.dc_nc)
  -> psk:option preshared_key ->
  Lemma
  (requires
    peers_pairwise_distinct_statics dv.dv_peers)
  (ensures (
    match add_peer_get dv pinfo rs psk with
    | None -> True
    | Some (p, dv') ->
      peers_pairwise_distinct_statics dv'.dv_peers))

#push-options "--fuel 1 --ifuel 1"
let add_peer_get_distinct_statics_lem #dc dv pinfo rs psk =
  match add_peer_get dv pinfo rs psk with
  | None -> ()
  | Some (p, dv') ->
    match rs with
    | None ->
      M.forall_implies_list_for_all (peers_distinct_statics p) dv.dv_peers
    | Some rs ->
      M.tryFind_not_is_for_all_lem (peer_has_s rs)
                                   peers_distinct_statics
                                   p dv.dv_peers
#pop-options

val add_peer_get_invariant_preservation_lem :
     #dc:dconfig
  -> dv:device dc
  -> pinfo:dc.dc_info
  -> rs:option (public_key dc.dc_nc)
  -> psk:option preshared_key ->
  Lemma
  (requires
    dv_peers_counter_invariant dv /\
    peers_pairwise_distinct_ids dv.dv_peers /\
    peers_pairwise_distinct_statics dv.dv_peers)
  (ensures (
    match add_peer_get dv pinfo rs psk with
    | None -> True
    | Some (p, dv') ->
      dv_peers_counter_invariant dv' /\
      peers_pairwise_distinct_ids dv'.dv_peers /\
      peers_pairwise_distinct_statics dv'.dv_peers))

let add_peer_get_invariant_preservation_lem #dc dv pinfo rs psk =
  add_peer_get_distinct_ids_lem #dc dv pinfo rs psk;
  add_peer_get_distinct_statics_lem #dc dv pinfo rs psk

(**** Remove peer *)

val remove_peer_invariant_lem :
     #dc:dconfig
  -> dv:device dc
  -> id:peer_id ->
  Lemma
  (requires
    dv_peers_counter_invariant dv /\
    peers_pairwise_distinct_ids dv.dv_peers /\
    peers_pairwise_distinct_statics dv.dv_peers)
  (ensures (
    let dv' = remove_peer dv id in
    dv_peers_counter_invariant dv' /\
    peers_pairwise_distinct_ids dv'.dv_peers /\
    peers_pairwise_distinct_statics dv'.dv_peers))

let remove_peer_invariant_lem #dc dv id =
  M.filter_one_preserves_for_all (peer_has_smaller_id dv.dv_peers_counter) (peer_has_not_id id) dv.dv_peers;
  M.filter_one_preserves_pairwise_rel peers_distinct_ids (peer_has_not_id id) dv.dv_peers;
  M.filter_one_preserves_pairwise_rel peers_distinct_statics (peer_has_not_id id) dv.dv_peers


(*** Misc *)
val lookup_peer_by_id_same_id :
     #dc:dconfig
  -> dv:device dc
  -> id:peer_id ->
  Lemma (
    match lookup_peer_by_id dv id with
    | None -> True
    | Some p -> p.p_id = id)

let lookup_peer_by_id_same_id #dc dv id =
  M.tryFind_lem (peer_has_id id) dv.dv_peers

val lookup_peer_by_static_same_static :
     #dc:dconfig
  -> dv:device dc
  -> s : public_key dc.dc_nc ->
  Lemma(
    match lookup_peer_by_static dv s with
    | None -> True
    | Some p -> Some? p.p_s /\ Some?.v p.p_s == s)

let lookup_peer_by_static_same_static #dc dv s =
  M.tryFind_lem (peer_has_s s) dv.dv_peers

(*** Serialization/deserialization *)

open Lib.RandomSequence

val deserialize_serialize_bytes_eq
  (dc : dconfig) (sk : aead_key) (name : dc.dc_info)
  (b : bytes{Seq.length b <= aead_max_input dc.dc_nc})
  (entr : entropy) :
    Lemma (
      let c, _ = serialize_bytes dc sk name b entr in
      // Note: doesn't work if we write an equality without the match
      match deserialize_bytes dc sk name c with
      | None -> False
      | Some b' -> b == b')

let deserialize_serialize_bytes_eq dc sk name b entr =
  let n8, n, entr' = generate_random_nonce entr in
  let name_raw = dc.dc_info_to_bytes name in
  let c0 = aead_encrypt dc.dc_nc sk n name_raw b in
  let c1 = Seq.append n8 c0 in
  let n8', c' = Seq.split c1 aead_nonce_size in
  let n' = bytes_to_nonce n8' in
  assert(Seq.equal n8' n8);
  assert(n' = n);
  assert(Seq.equal c' c0);
  Spec.Noise.CryptoPrimitives.aead_correctness dc.dc_nc sk n name_raw b

val create_device_from_serialized
  (#dc:dconfig) (dv:device dc) (entr:entropy) :
  Lemma
  // TODO: remove this precondition once we remove the precondition on the
  // length of the encrypted data
  (requires (
    Some? dv.dv_static_identity /\
    // The public key was computed from the private key
    dv.dv_static_identity == keypair_from_private (Some?.v dv.dv_static_identity).priv))
  (ensures (
    match serialize_device_secret dv entr with
    | None, _ -> None? dv.dv_sk \/ None? dv.dv_static_identity
    | Some enc_key, _ ->
      // TODO: we shouldn't have a precondition on the length of the encrypted data
      // given to the device
      Some? dv.dv_sk /\ Some? dv.dv_static_identity /\
      Seq.length enc_key = enc_private_key_with_nonce_size dc.dc_nc /\
      begin match create_device_from_secret dc dv.dv_pattern dv.dv_prologue dv.dv_info (Some?.v dv.dv_sk) (Some enc_key) with
      | None -> False
      | Some dv' ->
        dv' == { dv with dv_states_counter = 0; dv_peers = []; dv_peers_counter = 0; }
      end))

let create_device_from_serialized #dc dv entr =
  match dv.dv_sk, dv.dv_static_identity with
  | None, _ -> ()
  | _, None -> ()
  | Some sk, Some s ->
    let enc_s, entr' = serialize_bytes dc sk dv.dv_info s.priv entr in
    assert(Seq.length enc_s = enc_private_key_with_nonce_size dc.dc_nc);
    deserialize_serialize_bytes_eq dc sk dv.dv_info s.priv entr;
    assert(
      match Spec.Noise.API.Device.Definitions.deserialize_bytes dc sk dv.dv_info enc_s with
      | None  -> False
      | Some s' -> Mkkeypair?.priv s == s');
    let res = create_device_from_secret dc dv.dv_pattern dv.dv_prologue dv.dv_info sk (Some enc_s) in
    match res with
    | None -> assert(False)
    | Some dv' -> ()

val deserialize_serialize_peer_secret_lem
  (#dc:dconfig) (dv0 dv1:device dc) (peer:peer dc) (entr:entropy) :
  Lemma
  (requires (
    // We manipulate different devices, because the device evolves over time
    dv0.dv_info == dv1.dv_info /\
    dv0.dv_sk == dv1.dv_sk))
  (ensures (
    match serialize_peer_secret dv0 peer entr with
    | None, _ -> None? dv0.dv_sk
    | Some enc_keys, _ ->
      match deserialize_peer_secret dv1 peer.p_info (Some? peer.p_s) (Some? peer.p_psk) enc_keys with
      | None -> Some? peer.p_s /\ Some? (lookup_peer_by_static dv1 (Some?.v peer.p_s))
      | Some (peer', dv1') ->
        // The peer identifier is not necessarily the same
        peer'.p_info == peer.p_info /\
        peer'.p_s == peer.p_s /\
        peer'.p_psk == peer.p_psk))

let deserialize_serialize_peer_secret_lem #dc dv0 dv1 p entr =
  // Serialize
  let device_name = dv0.dv_info in
  match dv0.dv_sk with
  | None -> ()
  | Some sk ->
    let p_s = match p.p_s with | None -> Seq.empty | Some s -> s in
    let p_psk = match p.p_psk with | None -> Seq.empty | Some s -> s in
    let keys0 = Seq.append p_s p_psk in
    let enc_keys, entr' = serialize_bytes dc sk p.p_info keys0 entr in
    deserialize_serialize_bytes_eq dc sk p.p_info keys0 entr;
    // Deserialize
    let rsb = Some? p.p_s in
    let pskb = Some? p.p_psk in
    let req_length = aead_nonce_size + aead_tag_size in
    let req_length = if rsb then public_key_size dc.dc_nc + req_length else req_length in
    let req_length = if pskb then preshared_key_size + req_length else req_length in
    if req_length <> Seq.length enc_keys then ()
    else    
      match deserialize_bytes dc sk p.p_info enc_keys with
      | None -> assert(False)
      | Some keys1 ->
        let ((p_s', keys2) : option (public_key dc.dc_nc) & bytes) =
          if rsb then
            begin
            let s, keys2 = Seq.split keys1 (public_key_size dc.dc_nc) in
            assert(Seq.equal (Seq.append s keys2 ) keys1);
            Some s, keys2
            end
          else None, keys1
        in
        let p_psk' : option preshared_key = if pskb then Some keys2 else None in
        assert(keys1 == keys0);
        assert(
          match p.p_s, p.p_psk with
          | None, None -> Seq.equal keys0 Seq.empty /\ Seq.equal keys2 Seq.empty
          | Some s, None -> Seq.equal keys0 s /\ Seq.equal (Some?.v p_s') keys1 /\ p_s' == Some s
          | None, Some psk -> Seq.equal keys0 psk /\ Seq.equal (Some?.v p_psk') keys1 /\ p_psk' == Some psk
          | Some s, Some psk ->
            Seq.equal keys0 (Seq.append s psk) /\
            Seq.equal keys1 (Seq.append (Some?.v p_s') (Some?.v p_psk')) /\
            Seq.equal s (Some?.v p_s') /\ Seq.equal psk (Some?.v p_psk'));
        assert(p_s' == p.p_s);
        assert(p_psk' == p.p_psk);
        ()
