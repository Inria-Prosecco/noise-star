module Spec.Noise.API.Device.Definitions

open Lib.ByteSequence
open FStar.Mul
open FStar.List.Tot

friend Spec.Noise.Base.Definitions
module Base = Spec.Noise.Base.Definitions
module State = Spec.Noise.API.State.Definitions
friend Spec.Noise.API.State.Definitions
open Spec.Noise.Utils
module M = Spec.Noise.Map

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** Peer *)

noeq type raw_peer (nc : config) (info_ty : Type0) : Type0 = {
  p_id : peer_id; // identifier in the table
  p_info : info_ty; // meta-data provided by the end-user
  p_s : option (public_key nc);
  p_psk : option preshared_key;
}

let peer_get_id #dc p = p.p_id
let peer_get_info #dc p = p.p_info
let peer_get_static #dc p = p.p_s
let peer_get_psk #dc p = p.p_psk

let raw_peer_has_s (#nc : config) (#info_ty : Type0) (s : public_key nc) (p : raw_peer nc info_ty) :
  Tot bool =
  match p.p_s with
  | None -> false
  | Some k -> lbytes_eq k s

(*** Device *)
(* A device handles one static identity and one handshake pattern. The user
 * can of course use several devices at the same time.
 * Stores the list of peers.
 * Is used for example to lookup keys: when creating a state, we may not know
 * who we are talking to, once we know (i.e.: after having received a public
 * static key) we can lookup information like the psk associated to this peer. *)
// TODO: make the device parametric in the dconfig?

noeq type device (dc : dconfig) = {
  dv_pattern : wfs_handshake_pattern;
  dv_info : dc.dc_info; // TODO: rename to dv_name
  dv_sk : option aead_key;
  dv_static_identity : option (keypair dc.dc_nc);
  dv_prologue : hashable dc.dc_nc;
  dv_states_counter : state_id;
  dv_peers : M.t (peer dc);
  dv_peers_counter : peer_id;
}

let device_get_pattern dv = dv.dv_pattern
let device_get_peers dv = dv.dv_peers
let device_get_info dv = dv.dv_info
let device_get_static #dc dv = dv.dv_static_identity
let device_get_states_counter dv = dv.dv_states_counter
let device_get_peers_counter dv = dv.dv_peers_counter

(** Small helpers for serialization/deserialization *)

let bytes_to_nonce (n8 : lbytes aead_nonce_size) : aead_nonce =
  let nonce = uint_from_bytes_le #U64 n8 in
  UInt64.v (Lib.RawIntTypes.u64_to_UInt64 nonce)

let generate_random_nonce (entr : entropy) : lbytes aead_nonce_size & aead_nonce & entropy =
  // Generate some random bytes
  let entr', n8 = crypto_random entr aead_nonce_size in
  // Convert the bytes to a nonce
  n8, bytes_to_nonce n8, entr'

val serialize_bytes (dc : dconfig) (sk : aead_key) (name : dc.dc_info)
                    (b : bytes{Seq.length b <= aead_max_input dc.dc_nc})
                    (entr : entropy) :
  bytes & entropy

let serialize_bytes dc sk name b entr =
  let n8, n, entr' = generate_random_nonce entr in
  let name_raw = dc.dc_info_to_bytes name in
  let c = aead_encrypt dc.dc_nc sk n name_raw b in
  let c = Seq.append n8 c in
  c, entr'

val deserialize_bytes
  (dc : dconfig) (sk : aead_key) (name : dc.dc_info)
  (c : bytes{
    Seq.length c >= aead_tag_size + aead_nonce_size /\
    Seq.length c <= aead_max_input dc.dc_nc + aead_tag_size + aead_nonce_size}) :
  option (p:bytes{Seq.length p + aead_tag_size + aead_nonce_size = Seq.length c})

let deserialize_bytes dc sk name c =
  // Split between the nonce and the cipher
  let name_raw = dc.dc_info_to_bytes name in
  let n8, c = Seq.split c aead_nonce_size in
  let n = bytes_to_nonce n8 in
  // Decrypt
  match aead_decrypt dc.dc_nc sk n name_raw c with
  | None -> None
  | Some p -> Some p

(** Creation *)

let create_device dc hsk prologue info sk static_identity =
  let dv =
  {
    dv_pattern = hsk;
    dv_info = info;
    dv_sk = sk;
    dv_static_identity = None;
    dv_prologue = prologue;
    dv_states_counter = 0;
    dv_peers = [];
    dv_peers_counter = 0;
  }
  in
  match static_identity with
  | None -> Some dv
  | Some spriv ->
    let nc = dc.dc_nc in
    match keypair_from_private #nc spriv with
    | None ->
      // TODO: so actually it can't fail.
      // We should update the signature or secret_to_public and propagate that
      (**) assert(False);
      None
    | Some kp -> Some ({ dv with dv_static_identity = Some kp; })

let create_device_from_secret dc hsk prologue info sk static_identity =
  match static_identity with
  | None -> create_device dc hsk prologue info (Some sk) None
  | Some s ->
    match deserialize_bytes dc sk info s with
    | None -> None
    | Some s ->
      create_device dc hsk prologue info (Some sk) (Some s)

let peer_has_id (#dc : dconfig) (id : peer_id) (p : peer dc) : Tot bool =
  p.p_id = id

let peer_has_not_id (#dc : dconfig) (id : peer_id) (p : peer dc) :
  Tot bool =
  not (peer_has_id id p)

let peer_has_s (#dc : dconfig) (s : public_key dc.dc_nc) (p : peer dc) :
  Tot bool =
  raw_peer_has_s s p

let peers_distinct_ids (#dc : dconfig) (p1 p2 : peer dc) : Tot bool =
  p1.p_id <> p2.p_id

let peers_distinct_statics (#dc : dconfig) (p1 p2 : peer dc) :
  Tot bool =
  match p1.p_s, p2.p_s with
  | Some s1, Some s2 -> not (lbytes_eq s1 s2)
  | _ -> true

let peers_pairwise_distinct_ids (#dc : dconfig) (peers : list (peer dc)) :
  Tot bool =
  M.pairwise_rel peers_distinct_ids peers

let peers_pairwise_distinct_statics (#dc : dconfig) (peers : list (peer dc)) :
  Tot bool =
  M.pairwise_rel peers_distinct_statics peers

val peer_has_smaller_id (#dc : dconfig) (id : peer_id) (p : peer dc) : Tot bool
let peer_has_smaller_id #dc id p =
  p.p_id < id

val dv_peers_counter_invariant (#dc : dconfig) (dv : device dc) : Tot bool
let dv_peers_counter_invariant #dc dv =
  for_all (peer_has_smaller_id dv.dv_peers_counter) dv.dv_peers

let lookup_peer_by_id dv id =
  M.lookup (peer_has_id id) dv.dv_peers

let lookup_peer_by_static #dc dv s =
  M.lookup (peer_has_s s) dv.dv_peers

let add_peer_get #dc dv pinfo rs psk =
  let pid = dv.dv_peers_counter in
  let p = { p_id = pid; p_info = pinfo; p_s = rs; p_psk = psk } in
  (* Check if there is a peer with the same static key in the device before adding a new one *)
  let p2 =
    match rs with
    | None -> None
    | Some rs -> lookup_peer_by_static dv rs
  in
  match p2 with
  | None -> Some (p, { dv with dv_peers = p :: dv.dv_peers; dv_peers_counter = pid+1; })
  | _ -> None

let remove_peer #dc dv id =
  let peers = M.filter_one (peer_has_not_id id) dv.dv_peers in
  { dv with dv_peers = peers }

let serialize_device_secret #dc dv entr =
  match dv.dv_sk, dv.dv_static_identity with
  | None, _ -> None, entr
  | _, None -> None, entr
  | Some sk, Some s ->
    let enc_s, entr' = serialize_bytes dc sk dv.dv_info s.priv entr in
    Some enc_s, entr'

let serialize_peer_secret #dc dv p entr =
  // We need a static key to encrypt
  match dv.dv_sk with
  | None -> None, entr
  | Some sk ->
    let p_s = match p.p_s with | None -> Seq.empty | Some s -> s in
    let p_psk = match p.p_psk with | None -> Seq.empty | Some s -> s in
    let keys = Seq.append p_s p_psk in
    let enc_keys, entr' = serialize_bytes dc sk p.p_info keys entr in
    Some enc_keys, entr'

let deserialize_peer_secret #dc dv peer_name rs psk enc_keys =
  match dv.dv_sk with
  | None -> None
  | Some sk ->
    // Checking the length before splitting
    let req_length = aead_nonce_size + aead_tag_size in
    let req_length = if rs then public_key_size dc.dc_nc + req_length else req_length in
    let req_length = if psk then preshared_key_size + req_length else req_length in
    if req_length <> Seq.length enc_keys then None
    else    
      match deserialize_bytes dc sk peer_name enc_keys with
      | None -> None
      | Some keys ->
        let ((p_s, keys) : option (public_key dc.dc_nc) & bytes) =
          if rs then
            let s, keys = Seq.split keys (public_key_size dc.dc_nc) in
            Some s, keys
          else None, keys
        in
        let p_psk = if psk then Some keys else None in
        add_peer_get dv peer_name p_s p_psk
      
