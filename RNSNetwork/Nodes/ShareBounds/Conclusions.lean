/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# ShareBounds — the survivor share falls like one over the logarithm

With the wheels below a bound, the share of the cycle that survives every
wheel is at most one over the logarithm of the bound. The reason: one over
the share is the product, over the wheels, of the wheel size over the wheel
size minus 1, and that product is at least the sum of one over each number
up to the last wheel (each such number is built from the wheels), which is
at least the logarithm. The share surviving the twin pattern is at most twice
the square of the same bound.

Proof: `RNSSolutions/ShareBounds.lean`, which assumes two claims of
`SurvivorCount` and nothing else. Metadata: `formalization.yaml`.
-/

namespace RNS.ShareBounds

/-- **The survivor share is at most one over the logarithm.** For the wheels
below `limit` (at least 2), the survivors of the pattern `{0}` as a share of
the cycle length are at most one over the logarithm of `limit`. -/
def survivor_share_le_inv_log : Prop :=
  ∀ limit : Nat, 2 ≤ limit →
    ((wheel_survivors_gen {0} limit).card : Real) / (primorial_modulus limit : Real)
      ≤ 1 / Real.log limit

/-- **The twin share is at most twice the square of that.** For the wheels
below `limit` (at least 2), the survivors of the twin pattern as a share of
the cycle length are at most twice the square of one over the logarithm of
`limit`. -/
def twin_share_le_two_inv_log_sq : Prop :=
  ∀ limit : Nat, 2 ≤ limit →
    ((wheel_survivors limit).card : Real) / (primorial_modulus limit : Real)
      ≤ 2 * (1 / Real.log limit) ^ 2

end RNS.ShareBounds
