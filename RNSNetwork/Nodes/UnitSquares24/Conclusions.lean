/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.ZMod.Units

/-!
# UnitSquares24 — 24 is the largest cycle on which every open position squares to 1

On the cycle of length `m`, call a position open when it shares no factor with
`m` (it survives every wheel dividing `m`). Every open position squares to 1
on the cycle exactly when `m` divides 24. In the language of number fields this
is the statement that the number w₂ of the rational numbers is 24.

The familiar consequence: every prime from 5 on squares to one more than a
multiple of 24.

Proof: `RNSSolutions/UnitSquares24.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.UnitSquares24

/-- **Every open position squares to 1 exactly on the divisors of 24.** For a
cycle length `m` other than 0, every unit of the cycle squares to 1 if and
only if `m` divides 24. -/
def units_square_one_iff : Prop :=
  ∀ m : ℕ, m ≠ 0 → ((∀ u : (ZMod m)ˣ, u ^ 2 = 1) ↔ m ∣ 24)

/-- **Prime squares on the cycle of 24.** Every prime from 5 on squares to one
more than a multiple of 24. -/
def prime_sq_mod_24 : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p ^ 2 % 24 = 1

end RNS.UnitSquares24
