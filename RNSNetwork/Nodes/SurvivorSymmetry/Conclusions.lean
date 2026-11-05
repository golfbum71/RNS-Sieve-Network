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

The counting form follows: up to a point `t` inside the cycle, the survivors
number the whole cycle's survivors minus the survivors up to the mirror point
(the cycle length minus `t` minus 1). This is Legendre's mirror identity for
his count phi(x, a).

Source: D. H. Lehmer, "The distribution of totatives", Canad. J. Math. 7
(1955), Theorem 1; restated by Grob and Schmitt, arXiv:1905.03117 (2019),
Theorem 2.
-/

namespace RNS.SurvivorSymmetry

/-- **Mirror symmetry.** For any wheels `W` and a position `k` at or below
the cycle length, `k` survives every wheel exactly when the cycle length
minus `k` does. (No primality is needed.) -/
def survivor_reflection : Prop :=
  ∀ (W : Finset Nat) (k : Nat), k ≤ W.prod id →
    ((∀ q ∈ W, ¬ q ∣ k) ↔ (∀ q ∈ W, ¬ q ∣ W.prod id - k))

/-- **Mirror symmetry, counting form.** For a nonempty set of wheels `W` and a
point `t` before the end of the cycle, the survivors up to `t` and the
survivors up to the cycle length minus `t` minus 1 together number one full
cycle's survivors. -/
def survivor_count_reflection : Prop :=
  ∀ (W : Finset Nat) (t : Nat), W.Nonempty → t < W.prod id →
    (survivors_upto W t).card + (survivors_upto W (W.prod id - t - 1)).card
      = (survivors_upto W (W.prod id)).card

end RNS.SurvivorSymmetry
