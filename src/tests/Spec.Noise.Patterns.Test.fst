module Spec.Noise.Patterns.Test

open Spec.Noise.Testing
//open Spec.Noise.TestVectors

open FStar.All
//module IO = FStar.IO

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

let test () : ML bool =
  let hsk_tests = load_test_vectors () in
  execute_handshakes hsk_tests
