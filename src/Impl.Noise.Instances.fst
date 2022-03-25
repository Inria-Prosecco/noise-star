module Impl.Noise.Instances

open Lib.Buffer

module Spec = Spec.Noise.Instances
open Spec.Noise
open Impl.Noise.Extraction
open Impl.Noise.PatternMessages

module ImplCFields = Hacl.Impl.Curve25519.Fields.Core
module ImplPolyFields = Hacl.Impl.Poly1305.Fields
module ImplBlake2Core = Hacl.Impl.Blake2.Core

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let impls_params : config_impls_params Spec.Noise.Instances.wgc =
  ImplCFields.M51, ImplPolyFields.M32, ImplBlake2Core.M32

%splice[dh; aead_encrypt; aead_decrypt; hash; aead_encrypt; aead_decrypt; wg_inc; hski]
(generate_pattern_declarations true impls_params default_extract_decls_params "wg_inc" "hski")

(*** IKpsk2 *)
(**** General functions *)
(* initialization *)
[@(Tactics.postprocess_with pp_hsk_def)]
let initialize_IKpsk2 =
  initialize hski Spec.pattern_IKpsk2

(* premessages *)
[@(Tactics.postprocess_with pp_hsk_def)]
let send_premessage_IKpsk2 =
  csend_premessage hski Spec.pattern_IKpsk2 false false

[@(Tactics.postprocess_with pp_hsk_def)]
let receive_premessage_IKpsk2 =
  creceive_premessage hski Spec.pattern_IKpsk2 false false

(* messages *)
[@(Tactics.postprocess_with pp_hsk_def)]
let create_initiation_IKpsk2 =
  csend_message hski Spec.pattern_IKpsk2 0 false 12ul

[@(Tactics.postprocess_with pp_hsk_def)]
let consume_initiation_IKpsk2 =
  creceive_message hski Spec.pattern_IKpsk2 0 false 12ul

// TODO: the normalize_term in cset_psk_st doesn't work anymore. Fix that.
// Maybe start by investigating while the following doesn't normalize here:
// [> let x = chskf_check_is_psk (convert_pattern Spec.pattern_IKpsk2)
// (note that it normalizes in Impl.Noise.PatternMessages.Definitions.fst...)
[@@ noextract_to "Kremlin"] noextract
let _convert_pattern (x : wf_handshake_pattern) : handshake_pattern = x

(* set the PSK just before the response message *)
[@(Tactics.postprocess_with pp_hsk_def)]
let cset_psk_IKpsk2 =
  // TODO: remove those once the normalization is fixed
  (**) normalize_term_spec(chskf_check_is_psk (_convert_pattern Spec.pattern_IKpsk2));
  (**) normalize_term_spec(chskf_check_is_psk (Spec.pattern_IKpsk2));
  cset_psk hski Spec.pattern_IKpsk2 1

[@(Tactics.postprocess_with pp_hsk_def)]
let create_response_IKpsk2 =
  csend_message hski Spec.pattern_IKpsk2 1 true 0ul (null Lib.IntTypes.uint8)

[@(Tactics.postprocess_with pp_hsk_def)]
let consume_response_IKpsk2 =
  creceive_message hski Spec.pattern_IKpsk2 1 true 0ul (null Lib.IntTypes.uint8)

(*** XX *)
(* initialization *)
[@(Tactics.postprocess_with pp_hsk_def)]
let initialize_XX =
  initialize hski Spec.pattern_XX

(* messages *)
[@(Tactics.postprocess_with pp_hsk_def)]
let create_initiation_XX =
  csend_message hski Spec.pattern_XX 0 false

[@(Tactics.postprocess_with pp_hsk_def)]
let consume_initiation_XX =
  creceive_message hski Spec.pattern_XX 0 false

[@(Tactics.postprocess_with pp_hsk_def)]
let create_response1_XX =
  csend_message hski Spec.pattern_XX 1 false

[@(Tactics.postprocess_with pp_hsk_def)]
let consume_response1_XX =
  creceive_message hski Spec.pattern_XX 1 false

[@(Tactics.postprocess_with pp_hsk_def)]
let create_response2_XX =
  csend_message hski Spec.pattern_XX 2 false

[@(Tactics.postprocess_with pp_hsk_def)]
let consume_response2_XX =
  creceive_message hski Spec.pattern_XX 2 false
