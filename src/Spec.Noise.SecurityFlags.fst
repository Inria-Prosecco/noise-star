/// This file defines some very high level security flags that we derive from
/// the levels listed in the technical paper. They are supposed to be more
/// meaningful to the users than the Noise levels.

module Spec.Noise.SecurityFlags

open Spec.Noise.AuthConf
open Spec.Noise.PatternsSecurity

#set-options "--z3rlimit 15 --fuel 0 --ifuel 2"

/// Returns true if the sender is authentified
val alevel_sender_auth (n:nat) : bool
let alevel_sender_auth n =
  // Note that this authentication only relies on the static keys:
  // there may be key-compromise impersonation.
  // If we want to be resistant to KCI, we need: [n >= 2]
  n >= 1

/// Returns true if the recipient is known
val clevel_recv_auth (n:nat) : bool
let clevel_recv_auth n =
  // Note that this authentication only relies on the static keys:
  // there may be key-compromise impersonation.
  // If we want to be resistant to KCI, we need: [n >= 4]
  n >= 2

/// Returns true if the message is replayable
val clevel_replayable (n:nat) : bool
let clevel_replayable n =
  n = 0 || n = 2

/// Returns true if we have strong forward secrecy
val clevel_sfs (n:nat): bool
let clevel_sfs n =
  // Could actually be 4
  n >= 5
