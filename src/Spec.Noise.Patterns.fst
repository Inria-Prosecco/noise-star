module Spec.Noise.Patterns

open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Meta.Noise
module T = FStar.Tactics

#set-options "--z3rlimit 15 --fuel 0 --ifuel 0"

/// The following file defines all the 59 patterns listed in the Noise technical paper
/// Note: we actually retrieved the list from the Cacophony source files:
/// https://github.com/centromere/cacophony/blob/master/src/Crypto/Noise/HandshakePatterns.hs

(*
 * | NN:
 * =======================
 * -> e
 * <- e, ee
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NN =
  wf_hs "NN" [
    ~>~ [E];
    ~<~ [E; EE]
  ]

(*
 * | KN:
 * =======================
 * -> s
 * -----------------------
 * -> e
 * <- e, ee, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KN =
  wf_hs "KN" [
    ~>>~ [PS];
    ~>~ [E];
    ~<~ [E; EE; SE]
  ]

(*
 * | NK:
 * =======================
 * <- s
 * -----------------------
 * -> e, es
 * <- e, ee
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NK =
  wf_hs "NK" [
    ~<<~ [PS];
    ~>~ [E; ES];
    ~<~ [E; EE]
  ]

(*
 * | KK:
 * =======================
 * -> s
 * <- s
 * -----------------------
 * -> e, es, ss
 * <- e, ee, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KK =
  wf_hs "KK" [
    ~>>~ [PS];
    ~<<~ [PS];
    ~>~ [E; ES; SS];
    ~<~ [E; EE; SE]
  ]

(*
 * | NX:
 * =======================
 * -> e
 * <- e, ee, s, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NX =
  wf_hs "NX" [
    ~>~ [E];
    ~<~ [E; EE; S; ES]
  ]

(*
 * | KX:
 * =======================
 * -> s
 * -----------------------
 * -> e
 * <- e, ee, se, s, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KX =
  wf_hs "KX" [
    ~>>~ [PS];
    ~>~ [E];
    ~<~ [E; EE; SE; S; ES]
  ]

(*
 * | XN:
 * =======================
 * -> e
 * <- e, ee
 * -> s, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XN =
  wf_hs "XN" [
    ~>~ [E];
    ~<~ [E; EE];
    ~>~ [S; SE]
  ]

(*
 * | IN:
 * =======================
 * -> e, s
 * <- e, ee, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IN =
  wf_hs "IN" [
    ~>~ [E; S];
    ~<~ [E; EE; SE]
  ]

(*
 * | XK:
 * =======================
 * <- s
 * -----------------------
 * -> e, es
 * <- e, ee
 * -> s, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XK =
  wf_hs "XK" [
    ~<<~ [PS];
    ~>~ [E; ES];
    ~<~ [E; EE];
    ~>~ [S; SE]
  ]

(*
 * | IK:
 * =======================
 * <- s
 * -----------------------
 * -> e, es, s, ss
 * <- e, ee, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IK =
  wf_hs "IK" [
    ~<<~ [PS];
    ~>~ [E; ES; S; SS];
    ~<~ [E; EE; SE]
  ]

(*
 * | XX:
 * =======================
 * -> e
 * <- e, ee, s, es
 * -> s, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XX =
  wf_hs "XX" [
    ~>~ [E];
    ~<~ [E; EE; S; ES];
    ~>~ [S; SE]
  ]

(*
 * | IX:
 * =======================
 * -> e, s
 * <- e, ee, se, s, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IX =
  wf_hs "IX" [
    ~>~ [E; S];
    ~<~ [E; EE; SE; S; ES]
  ]

(*
 * | N:
 * =======================
 * <- s
 * -----------------------
 * -> e, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_N =
  wf_hs "N" [
    ~<<~ [PS];
    ~>~ [E; ES]
  ]

(*
 * | K:
 * =======================
 * -> s
 * <- s
 * -----------------------
 * -> e, es, ss
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K =
  wf_hs "K" [
    ~>>~ [PS];
    ~<<~ [PS];
    ~>~ [E; ES; SS]
  ]

(*
 * | X:
 * =======================
 * <- s
 * -----------------------
 * -> e, es, s, ss
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X =
  wf_hs "X" [
    ~<<~ [PS];
    ~>~ [E; ES; S; SS]
  ]

(*
 * | NNpsk0:
 * =======================
 * -> psk, e
 * <- e, ee
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NNpsk0 =
  wf_hs "NNpsk0" [
    ~>~ [PSK; E];
    ~<~ [E; EE]
  ]

(*
 * | NNpsk2:
 * =======================
 * -> e
 * <- e, ee, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NNpsk2 =
  wf_hs "NNpsk2" [
    ~>~ [E];
    ~<~ [E; EE; PSK]
  ]

(*
 * | NKpsk0:
 * =======================
 * <- s
 * -----------------------
 * -> psk, e, es
 * <- e, ee
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NKpsk0 =
  wf_hs "NKpsk0" [
    ~<<~ [PS];
    ~>~ [PSK; E; ES];
    ~<~ [E; EE]
  ]

(*
 * | NKpsk2:
 * =======================
 * <- s
 * -----------------------
 * -> e, es
 * <- e, ee, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NKpsk2 =
  wf_hs "NKpsk2" [
    ~<<~ [PS];
    ~>~ [E; ES];
    ~<~ [E; EE; PSK]
  ]

(*
 * | NXpsk2:
 * =======================
 * -> e
 * <- e, ee, s, es, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NXpsk2 =
  wf_hs "NXpsk2" [
    ~>~ [E];
    ~<~ [E; EE; S; ES; PSK]
  ]

(*
 * | XNpsk3:
 * =======================
 * -> e
 * <- e, ee
 * -> s, se, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XNpsk3 =
  wf_hs "XNpsk3" [
    ~>~ [E];
    ~<~ [E; EE];
    ~>~ [S; SE; PSK]
  ]

(*
 * | XKpsk3:
 * =======================
 * <- s
 * -----------------------
 * -> e, es
 * <- e, ee
 * -> s, se, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XKpsk3 =
  wf_hs "XKpsk3" [
    ~<<~ [PS];
    ~>~ [E; ES];
    ~<~ [E; EE];
    ~>~ [S; SE; PSK]
  ]

(*
 * | XXpsk3:
 * =======================
 * -> e
 * <- e, ee, s, es
 * -> s, se, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XXpsk3 =
  wf_hs "XXpsk3" [
    ~>~ [E];
    ~<~ [E; EE; S; ES];
    ~>~ [S; SE; PSK]
  ]

(*
 * | KNpsk0:
 * =======================
 * -> s
 * -----------------------
 * -> psk, e
 * <- e, ee, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KNpsk0 =
  wf_hs "KNpsk0" [
    ~>>~ [PS];
    ~>~ [PSK; E];
    ~<~ [E; EE; SE]
  ]

(*
 * | KNpsk2:
 * =======================
 * -> s
 * -----------------------
 * -> e
 * <- e, ee, se, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KNpsk2 =
  wf_hs "KNpsk2" [
    ~>>~ [PS];
    ~>~ [E];
    ~<~ [E; EE; SE; PSK]
  ]

(*
 * | KKpsk0:
 * =======================
 * -> s
 * <- s
 * -----------------------
 * -> psk, e, es, ss
 * <- e, ee, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KKpsk0 =
  wf_hs "KKpsk0" [
    ~>>~ [PS];
    ~<<~ [PS];
    ~>~ [PSK; E; ES; SS];
    ~<~ [E; EE; SE]
  ]

(*
 * | KKpsk2:
 * =======================
 * -> s
 * <- s
 * -----------------------
 * -> e, es, ss
 * <- e, ee, se, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KKpsk2 =
  wf_hs "KKpsk2" [
    ~>>~ [PS];
    ~<<~ [PS];
    ~>~ [E; ES; SS];
    ~<~ [E; EE; SE; PSK]
  ]

(*
 * | KXpsk2:
 * =======================
 * -> s
 * -----------------------
 * -> e
 * <- e, ee, se, s, es, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KXpsk2 =
  wf_hs "KXpsk2" [
    ~>>~ [PS];
    ~>~ [E];
    ~<~ [E; EE; SE; S; ES; PSK]
  ]

(*
 * | INpsk1:
 * =======================
 * -> e, s, psk
 * <- e, ee, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_INpsk1 =
  wf_hs "INpsk1" [
    ~>~ [E; S; PSK];
    ~<~ [E; EE; SE]
  ]

(*
 * | INpsk2:
 * =======================
 * -> e, s
 * <- e, ee, se, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_INpsk2 =
  wf_hs "INpsk2" [
    ~>~ [E; S];
    ~<~ [E; EE; SE; PSK]
  ]

(*
 * | IKpsk1:
 * =======================
 * <- s
 * -----------------------
 * -> e, es, s, ss, psk
 * <- e, ee, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IKpsk1 =
  wf_hs "IKpsk1" [
    ~<<~ [PS];
    ~>~ [E; ES; S; SS; PSK];
    ~<~ [E; EE; SE]
  ]

(*
 * | IKpsk2:
 * =======================
 * <- s
 * -----------------------
 * -> e, es, s, ss
 * <- e, ee, se, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IKpsk2 =
  wf_hs "IKpsk2" [
    ~<<~ [PS];
    ~>~ [E; ES; S; SS];
    ~<~ [E; EE; SE; PSK]
  ]

(*
 * | IXpsk2:
 * =======================
 * -> e, s
 * <- e, ee, se, s, es, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IXpsk2 =
  wf_hs "IXpsk2" [
    ~>~ [E; S];
    ~<~ [E; EE; SE; S; ES; PSK]
  ]

(*
 * | Npsk0:
 * =======================
 * <- s
 * -----------------------
 * -> psk, e, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_Npsk0 =
  wf_hs "Npsk0" [
    ~<<~ [PS];
    ~>~ [PSK; E; ES]
  ]

(*
 * | Kpsk0:
 * =======================
 * -> s
 * <- s
 * -----------------------
 * -> psk, e, es, ss
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_Kpsk0 =
  wf_hs "Kpsk0" [
    ~>>~ [PS];
    ~<<~ [PS];
    ~>~ [PSK; E; ES; SS]
  ]

(*
 * | Xpsk1:
 * =======================
 * <- s
 * -----------------------
 * -> e, es, s, ss, psk
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_Xpsk1 =
  wf_hs "Xpsk1" [
    ~<<~ [PS];
    ~>~ [E; ES; S; SS; PSK]
  ]

(*
 * | NK1:
 * =======================
 * <- s
 * -----------------------
 * -> e
 * <- e, ee, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NK1 =
  wf_hs "NK1" [
    ~<<~ [PS];
    ~>~ [E];
    ~<~ [E; EE; ES]
  ]

(*
 * | NX1:
 * =======================
 * -> e
 * <- e, ee, s
 * -> es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_NX1 =
  wf_hs "NX1" [
    ~>~ [E];
    ~<~ [E; EE; S];
    ~>~ [ES]
  ]

(*
 * | X1N:
 * =======================
 * -> e
 * <- e, ee
 * -> s
 * <- se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1N =
  wf_hs "X1N" [
    ~>~ [E];
    ~<~ [E; EE];
    ~>~ [S];
    ~<~ [SE]
  ]

(*
 * | X1K:
 * =======================
 * <- s
 * -----------------------
 * -> e, es
 * <- e, ee
 * -> s
 * <- se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1K =
  wf_hs "X1K" [
    ~<<~ [PS];
    ~>~ [E; ES];
    ~<~ [E; EE];
    ~>~ [S];
    ~<~ [SE]
  ]

(*
 * | XK1:
 * =======================
 * <- s
 * -----------------------
 * -> e
 * <- e, ee, es
 * -> s, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XK1 =
  wf_hs "XK1" [
    ~<<~ [PS];
    ~>~ [E];
    ~<~ [E; EE; ES];
    ~>~ [S; SE]
  ]

(*
 * | X1K1:
 * =======================
 * <- s
 * -----------------------
 * -> e
 * <- e, ee, es
 * -> s
 * <- se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1K1 =
  wf_hs "X1K1" [
    ~<<~ [PS];
    ~>~ [E];
    ~<~ [E; EE; ES];
    ~>~ [S];
    ~<~ [SE]
  ]

(*
 * | X1X:
 * =======================
 * -> e
 * <- e, ee, s, es
 * -> s
 * <- se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1X =
  wf_hs "X1X" [
    ~>~ [E];
    ~<~ [E; EE; S; ES];
    ~>~ [S];
    ~<~ [SE]
  ]

(*
 * | XX1:
 * =======================
 * -> e
 * <- e, ee, s
 * -> es, s, se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_XX1 =
  wf_hs "XX1" [
    ~>~ [E];
    ~<~ [E; EE; S];
    ~>~ [ES; S; SE]
  ]

(*
 * | X1X1:
 * =======================
 * -> e
 * <- e, ee, s
 * -> es, s
 * <- se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_X1X1 =
  wf_hs "X1X1" [
    ~>~ [E];
    ~<~ [E; EE; S];
    ~>~ [ES; S];
    ~<~ [SE]
  ]

(*
 * | K1N:
 * =======================
 * -> s
 * -----------------------
 * -> e
 * <- e, ee
 * -> se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1N =
  wf_hs "K1N" [
    ~>>~ [PS];
    ~>~ [E];
    ~<~ [E; EE];
    ~>~ [SE]
  ]

(*
 * | K1K:
 * =======================
 * -> s
 * <- s
 * -----------------------
 * -> e, es
 * <- e, ee
 * -> se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1K =
  wf_hs "K1K" [
    ~>>~ [PS];
    ~<<~ [PS];
    ~>~ [E; ES];
    ~<~ [E; EE];
    ~>~ [SE]
  ]

(*
 * | KK1:
 * =======================
 * -> s
 * <- s
 * -----------------------
 * -> e
 * <- e, ee, se, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KK1 =
  wf_hs "KK1" [
    ~>>~ [PS];
    ~<<~ [PS];
    ~>~ [E];
    ~<~ [E; EE; SE; ES]
  ]

(*
 * | K1K1:
 * =======================
 * -> s
 * <- s
 * -----------------------
 * -> e
 * <- e, ee, es
 * -> se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1K1 =
  wf_hs "K1K1" [
    ~>>~ [PS];
    ~<<~ [PS];
    ~>~ [E];
    ~<~ [E; EE; ES];
    ~>~ [SE]
  ]

(*
 * | K1X:
 * =======================
 * -> s
 * -----------------------
 * -> e
 * <- e, ee, s, es
 * -> se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1X =
  wf_hs "K1X" [
    ~>>~ [PS];
    ~>~ [E];
    ~<~ [E; EE; S; ES];
    ~>~ [SE]
  ]

(*
 * | KX1:
 * =======================
 * -> s
 * -----------------------
 * -> e
 * <- e, ee, se, s
 * -> es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_KX1 =
  wf_hs "KX1" [
    ~>>~ [PS];
    ~>~ [E];
    ~<~ [E; EE; SE; S];
    ~>~ [ES]
  ]

(*
 * | K1X1:
 * =======================
 * -> s
 * -----------------------
 * -> e
 * <- e, ee, s
 * -> se, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_K1X1 =
  wf_hs "K1X1" [
    ~>>~ [PS];
    ~>~ [E];
    ~<~ [E; EE; S];
    ~>~ [SE; ES]
  ]

(*
 * | I1N:
 * =======================
 * -> e, s
 * <- e, ee
 * -> se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1N =
  wf_hs "I1N" [
    ~>~ [E; S];
    ~<~ [E; EE];
    ~>~ [SE]
  ]

(*
 * | I1K:
 * =======================
 * <- s
 * -----------------------
 * -> e, es, s
 * <- e, ee
 * -> se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1K =
  wf_hs "I1K" [
    ~<<~ [PS];
    ~>~ [E; ES; S];
    ~<~ [E; EE];
    ~>~ [SE]
  ]

(*
 * | IK1:
 * =======================
 * <- s
 * -----------------------
 * -> e, s
 * <- e, ee, se, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IK1 =
  wf_hs "IK1" [
    ~<<~ [PS];
    ~>~ [E; S];
    ~<~ [E; EE; SE; ES]
  ]

(*
 * | I1K1:
 * =======================
 * <- s
 * -----------------------
 * -> e, s
 * <- e, ee, es
 * -> se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1K1 =
  wf_hs "I1K1" [
    ~<<~ [PS];
    ~>~ [E; S];
    ~<~ [E; EE; ES];
    ~>~ [SE]
  ]

(*
 * | I1X:
 * =======================
 * -> e, s
 * <- e, ee, s, es
 * -> se
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1X =
  wf_hs "I1X" [
    ~>~ [E; S];
    ~<~ [E; EE; S; ES];
    ~>~ [SE]
  ]

(*
 * | IX1:
 * =======================
 * -> e, s
 * <- e, ee, se, s
 * -> es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_IX1 =
  wf_hs "IX1" [
    ~>~ [E; S];
    ~<~ [E; EE; SE; S];
    ~>~ [ES]
  ]

(*
 * | I1X1:
 * =======================
 * -> e, s
 * <- e, ee, s
 * -> se, es
 *)

[@(T.postprocess_with pp_normalize_tac)]
inline_for_extraction noextract
let pattern_I1X1 =
  wf_hs "I1X1" [
    ~>~ [E; S];
    ~<~ [E; EE; S];
    ~>~ [SE; ES]
  ]

(**
 * List of supported patterns
 *)
inline_for_extraction noextract
let supported_patterns = [
  pattern_NN;
  pattern_KN;
  pattern_NK;
  pattern_KK;
  pattern_NX;
  pattern_KX;
  pattern_XN;
  pattern_IN;
  pattern_XK;
  pattern_IK;
  pattern_XX;
  pattern_IX;
  pattern_N;
  pattern_K;
  pattern_X;
  pattern_NNpsk0;
  pattern_NNpsk2;
  pattern_NKpsk0;
  pattern_NKpsk2;
  pattern_NXpsk2;
  pattern_XNpsk3;
  pattern_XKpsk3;
  pattern_XXpsk3;
  pattern_KNpsk0;
  pattern_KNpsk2;
  pattern_KKpsk0;
  pattern_KKpsk2;
  pattern_KXpsk2;
  pattern_INpsk1;
  pattern_INpsk2;
  pattern_IKpsk1;
  pattern_IKpsk2;
  pattern_IXpsk2;
  pattern_Npsk0;
  pattern_Kpsk0;
  pattern_Xpsk1;
  pattern_NK1;
  pattern_NX1;
  pattern_X1N;
  pattern_X1K;
  pattern_XK1;
  pattern_X1K1;
  pattern_X1X;
  pattern_XX1;
  pattern_X1X1;
  pattern_K1N;
  pattern_K1K;
  pattern_KK1;
  pattern_K1K1;
  pattern_K1X;
  pattern_KX1;
  pattern_K1X1;
  pattern_I1N;
  pattern_I1K;
  pattern_IK1;
  pattern_I1K1;
  pattern_I1X;
  pattern_IX1;
  pattern_I1X1
]

let is_supported_pattern (p : handshake_pattern) : bool =
  let patterns : list handshake_pattern = List.Tot.map (fun (x : wf_handshake_pattern) -> (x <: handshake_pattern)) supported_patterns in
  List.Tot.mem p patterns

let noise_pattern_names =
  List.Tot.map (fun (x : Spec.Noise.WellFormedness.wf_handshake_pattern) -> x.name) supported_patterns

(**
 * Some properties
 *)
#push-options "--fuel 1 --ifuel 1"

// TODO: move to List.Tot.Properties
(** If an element can be [index]ed, then it is a [mem] of the list. *)
let rec lemma_index_mem (#t:eqtype) (l:list t) (i:nat{i < List.Tot.length l}) :
  Lemma
    (ensures (List.Tot.index l i `List.Tot.mem` l))
    [SMTPat (List.Tot.index l i `List.Tot.mem` l)] =
  match i with
  | 0 -> ()
  | _ -> lemma_index_mem (List.Tot.tl l) (i - 1)

(** [index l i == index (x::l) (i+1) *)
let rec index_cons (#t:Type) (x:t) (l:list t) (i:nat{i < List.Tot.length l}) :
  Lemma
  (ensures (List.Tot.index l i == List.Tot.index (x::l) (i+1)))
  (decreases l) =
  match l with
  | [] -> ()
  | x' :: l' ->
    if i = 0 then () else index_cons x' l' (i-1)
