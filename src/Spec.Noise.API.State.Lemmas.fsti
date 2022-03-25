module Spec.Noise.API.State.Lemmas

open Spec.Noise.CryptoPrimitives
open Spec.Noise.Base
open Spec.Noise.WellFormedness
open Lib.ByteSequence
open Spec.Noise.API.State.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

// Many lemmas are stated in terms of definitions hidden in Spec.Noise.API.State.Definitions.fst,
// which is why nothing is revealed in the interface.
