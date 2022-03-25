module Spec.Noise.Testing.Load

open Spec.Noise.Testing.Base

/// Declaration of the .ml function which will load the test vectors
val load_test_vectors : unit -> list handshake_test_vector
