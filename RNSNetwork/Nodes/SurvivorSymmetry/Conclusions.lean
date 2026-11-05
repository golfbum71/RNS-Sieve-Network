/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# SurvivorSymmetry — survivors are mirror-symmetric

A position of the combined cycle survives the wheels exactly when its
reflection in the cycle (the cycle length minus the position) survives:
every wheel size divides the cycle length, so a wheel divides the position
exactly when it divides the reflection.

Proof: `RNSSolutions/SurvivorSymmetry.lean`. Metadata: `formalization.yaml`.

Source: D. H. Lehmer, "The distribution of totatives", Canad. J. Math. 7
(1955), Theorem 1; restated by Grob and Schmitt, arXiv:1905.03117 (2019),
Theorem 2. The interval-by-interval form needs exact endpoints, so only the
position-by-position form is stated here.
-/

namespace RNS.SurvivorSymmetry

/-- **Mirror symmetry.** For any wheels `W` and a position `k` at or below
the cycle length, `k` survives every wheel exactly when the cycle length
minus `k` does. (No primality is needed.) -/
def survivor_reflection : Prop :=
  ∀ (W : Finset Nat) (k : Nat), k ≤ W.prod id →
    ((∀ q ∈ W, ¬ q ∣ k) ↔ (∀ q ∈ W, ¬ q ∣ W.prod id - k))

end RNS.SurvivorSymmetry
