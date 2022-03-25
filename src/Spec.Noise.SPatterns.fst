/// The following file takes the patterns defined in Spec.Noise.SPatterns and
/// add information about the security levels in their type.

module Spec.Noise.SPatterns

open Spec.Noise.Base
open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Meta.Noise
module T = FStar.Tactics
open Spec.Noise.Patterns
open Spec.Noise.PatternsSecurity

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

type wfs_handshake_pattern = hsk:wf_handshake_pattern{Some? (ac_levels hsk)}

[@ (strict_on_arguments [0]) ] noextract
let check_swf (hsk : handshake_pattern) : bool =
  Some? (ac_levels hsk)

inline_for_extraction noextract
let mk_wfs_pattern (hsk : wf_handshake_pattern{normalize_term #bool (check_swf hsk)}) :
  wfs_handshake_pattern =
  hsk

inline_for_extraction noextract let pattern_NN = mk_wfs_pattern Spec.Noise.Patterns.pattern_NN
inline_for_extraction noextract let pattern_KN = mk_wfs_pattern Spec.Noise.Patterns.pattern_KN
inline_for_extraction noextract let pattern_NK = mk_wfs_pattern Spec.Noise.Patterns.pattern_NK
inline_for_extraction noextract let pattern_KK = mk_wfs_pattern Spec.Noise.Patterns.pattern_KK
inline_for_extraction noextract let pattern_NX = mk_wfs_pattern Spec.Noise.Patterns.pattern_NX
inline_for_extraction noextract let pattern_KX = mk_wfs_pattern Spec.Noise.Patterns.pattern_KX
inline_for_extraction noextract let pattern_XN = mk_wfs_pattern Spec.Noise.Patterns.pattern_XN
inline_for_extraction noextract let pattern_IN = mk_wfs_pattern Spec.Noise.Patterns.pattern_IN
inline_for_extraction noextract let pattern_XK = mk_wfs_pattern Spec.Noise.Patterns.pattern_XK
inline_for_extraction noextract let pattern_IK = mk_wfs_pattern Spec.Noise.Patterns.pattern_IK
inline_for_extraction noextract let pattern_XX = mk_wfs_pattern Spec.Noise.Patterns.pattern_XX
inline_for_extraction noextract let pattern_IX = mk_wfs_pattern Spec.Noise.Patterns.pattern_IX
inline_for_extraction noextract let pattern_N = mk_wfs_pattern Spec.Noise.Patterns.pattern_N
inline_for_extraction noextract let pattern_K = mk_wfs_pattern Spec.Noise.Patterns.pattern_K
inline_for_extraction noextract let pattern_X = mk_wfs_pattern Spec.Noise.Patterns.pattern_X
inline_for_extraction noextract let pattern_NNpsk0 = mk_wfs_pattern Spec.Noise.Patterns.pattern_NNpsk0
inline_for_extraction noextract let pattern_NNpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_NNpsk2
inline_for_extraction noextract let pattern_NKpsk0 = mk_wfs_pattern Spec.Noise.Patterns.pattern_NKpsk0
inline_for_extraction noextract let pattern_NKpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_NKpsk2
inline_for_extraction noextract let pattern_NXpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_NXpsk2
inline_for_extraction noextract let pattern_XNpsk3 = mk_wfs_pattern Spec.Noise.Patterns.pattern_XNpsk3
inline_for_extraction noextract let pattern_XKpsk3 = mk_wfs_pattern Spec.Noise.Patterns.pattern_XKpsk3
inline_for_extraction noextract let pattern_XXpsk3 = mk_wfs_pattern Spec.Noise.Patterns.pattern_XXpsk3
inline_for_extraction noextract let pattern_KNpsk0 = mk_wfs_pattern Spec.Noise.Patterns.pattern_KNpsk0
inline_for_extraction noextract let pattern_KNpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_KNpsk2
inline_for_extraction noextract let pattern_KKpsk0 = mk_wfs_pattern Spec.Noise.Patterns.pattern_KKpsk0
inline_for_extraction noextract let pattern_KKpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_KKpsk2
inline_for_extraction noextract let pattern_KXpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_KXpsk2
inline_for_extraction noextract let pattern_INpsk1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_INpsk1
inline_for_extraction noextract let pattern_INpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_INpsk2
inline_for_extraction noextract let pattern_IKpsk1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_IKpsk1
inline_for_extraction noextract let pattern_IKpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_IKpsk2
inline_for_extraction noextract let pattern_IXpsk2 = mk_wfs_pattern Spec.Noise.Patterns.pattern_IXpsk2
inline_for_extraction noextract let pattern_Npsk0 = mk_wfs_pattern Spec.Noise.Patterns.pattern_Npsk0
inline_for_extraction noextract let pattern_Kpsk0 = mk_wfs_pattern Spec.Noise.Patterns.pattern_Kpsk0
inline_for_extraction noextract let pattern_Xpsk1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_Xpsk1
inline_for_extraction noextract let pattern_NK1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_NK1
inline_for_extraction noextract let pattern_NX1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_NX1
inline_for_extraction noextract let pattern_X1N = mk_wfs_pattern Spec.Noise.Patterns.pattern_X1N
inline_for_extraction noextract let pattern_X1K = mk_wfs_pattern Spec.Noise.Patterns.pattern_X1K
inline_for_extraction noextract let pattern_XK1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_XK1
inline_for_extraction noextract let pattern_X1K1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_X1K1
inline_for_extraction noextract let pattern_X1X = mk_wfs_pattern Spec.Noise.Patterns.pattern_X1X
inline_for_extraction noextract let pattern_XX1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_XX1
inline_for_extraction noextract let pattern_X1X1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_X1X1
inline_for_extraction noextract let pattern_K1N = mk_wfs_pattern Spec.Noise.Patterns.pattern_K1N
inline_for_extraction noextract let pattern_K1K = mk_wfs_pattern Spec.Noise.Patterns.pattern_K1K
inline_for_extraction noextract let pattern_KK1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_KK1
inline_for_extraction noextract let pattern_K1K1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_K1K1
inline_for_extraction noextract let pattern_K1X = mk_wfs_pattern Spec.Noise.Patterns.pattern_K1X
inline_for_extraction noextract let pattern_KX1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_KX1
inline_for_extraction noextract let pattern_K1X1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_K1X1
inline_for_extraction noextract let pattern_I1N = mk_wfs_pattern Spec.Noise.Patterns.pattern_I1N
inline_for_extraction noextract let pattern_I1K = mk_wfs_pattern Spec.Noise.Patterns.pattern_I1K
inline_for_extraction noextract let pattern_IK1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_IK1
inline_for_extraction noextract let pattern_I1K1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_I1K1
inline_for_extraction noextract let pattern_I1X = mk_wfs_pattern Spec.Noise.Patterns.pattern_I1X
inline_for_extraction noextract let pattern_IX1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_IX1
inline_for_extraction noextract let pattern_I1X1 = mk_wfs_pattern Spec.Noise.Patterns.pattern_I1X1
