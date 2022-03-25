module Meta.Noise

/// This module contains various meta utilities for Noise

open FStar.Tactics

#set-options "--z3rlimit 25 --fuel 0 --ifuel 0"

let with_onorm (#a : Type) (x : a) : (y:a{y==x}) =
  normalize_term x

let with_norm_steps s #a x =
  Pervasives.norm s x
