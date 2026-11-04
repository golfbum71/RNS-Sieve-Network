/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# CRT — one big cycle is the same as many small wheels

A position in the combined cycle of all the wheels carries exactly the same
information as one position on each individual wheel. This is what lets
every later count be done one wheel at a time and multiplied together.

Proof: `RNSSolutions/CRT.lean`. Metadata: `formalization.yaml`.
Source of record: `rns_sieve_6.lean`, Part A, Step 3 (`crt_map_bijective`).
-/

namespace RNS.CRT

/-- **The combined cycle matches the individual wheels exactly.** For every
bound, reading a position of the combined cycle as one position on each
active wheel (`crt_map`) is a one-to-one correspondence: every choice of
positions on the individual wheels comes from exactly one position of the
combined cycle. -/
def crt_map_bijective : Prop :=
  ∀ limit : Nat, Function.Bijective (crt_map limit)

end RNS.CRT
