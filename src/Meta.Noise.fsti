module Meta.Noise

/// This module contains various meta utilities for Noise

open FStar.Tactics

/// By having this dependency here, the interactive helpers are always loaded
/// (prevents from restarting F* whenever we need them...)
module Helpers = FStar.InteractiveHelpers

#set-options "--z3rlimit 25 --fuel 0 --ifuel 0"

/// For monomorphisation at extraction time
inline_for_extraction noextract
let monotype (a : Type0) = b:Type0{a == b}

/// Normalize a term. We wrap [normalize_term] in a function declared
/// [inline_for_extraction] so that the normalization happens only
/// during extraction and has no influence in the encoding sent to Z3.
/// We make the definition opaque by hiding it behind an interface to make
/// sure no normalization occurs when generating the proof obligations.
inline_for_extraction noextract
val with_onorm (#a : Type) (x : a) : (y:a{y==x})

/// [with_norm] will be deprecated once [normalize_term] is made compatible
/// with inline_for_extraction
inline_for_extraction noextract
let with_norm (#a : Type) (x : a) : (y:a{y==x}) =
  normalize_term x

// TODO: rename the helpers
inline_for_extraction noextract
val with_norm_steps (s : list norm_step) (#a : Type) (x : a) : (y:a{y==x})

/// Post-process a definition by normalizing it. Useful when we want to
/// evaluate the result of a function.
let pp_normalize_tac () : Tac unit =
  norm [zeta; simplify; primops; delta; iota];
  trefl()

/// We sometimes need to help type inference
inline_for_extraction noextract
let convert_type (#a1 : Type) (#a2 : Type{a1 == a2}) (x : a1) : y:a2{x === y} =
  x

inline_for_extraction noextract
let convert_subtype (#a1 : Type) (#a2 : Type{subtype_of a1 a2}) (x : a1) : a2 =
  x
