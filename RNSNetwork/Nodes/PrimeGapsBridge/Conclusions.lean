/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Nat.ModEq   -- `Nat.ModEq`, written `a ≡ b [MOD n]`

/-!
# PrimeGapsBridge — the network's admissibility is PrimeGapsLib's

The network calls an offset pattern admissible when, at every wheel, the
pattern occupies fewer positions than the wheel has (`is_admissible`, via
`w`). Axiom Math's PrimeGapsLib, which proves in Lean that infinitely many
prime gaps are at most 246 (assuming the Bombieri–Vinogradov theorem), calls
a set admissible when, for every prime, some residue class is missed by every
member (`Finset.Admissible`).

The two say the same thing. So PrimeGapsLib's results about admissible sets
apply to the network's admissible patterns with no change of meaning, and the
network's admissible patterns are exactly the ones its sieve can use.

PrimeGapsLib's definition is copied here word for word (from
`PrimeGapsTheory/NumberTheory/Admissible.lean`), not imported, so the
toolchains stay independent.

Proof: `RNSSolutions/PrimeGapsBridge.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.PrimeGapsBridge

/-- PrimeGapsLib's `Finset.Admissible`, copied word for word: for every prime
`p` there is a residue class `a` that no member of `H` lands in. -/
def primegaps_admissible (H : Finset Nat) : Prop :=
  ∀ p : Nat, p.Prime → ∃ a : Nat, ∀ h ∈ H, ¬ (h ≡ a [MOD p])

/-- **The two definitions agree.** An offset pattern is admissible in the
network's sense (fewer occupied positions than the wheel size, at every wheel)
exactly when it is admissible in PrimeGapsLib's sense (some residue class
missed, at every prime). -/
def admissible_iff_primegaps : Prop :=
  ∀ T : Finset Nat, is_admissible T ↔ primegaps_admissible T

end RNS.PrimeGapsBridge
