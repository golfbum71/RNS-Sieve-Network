/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# BirchTateRational — 24 times ζ(−1) is −2

The Riemann zeta function at −1 is −1/12. Multiplied by 24 — the largest cycle
on which every open position squares to 1 (node `UnitSquares24`) — it gives −2.
This is the numerical side of the Birch–Tate formula for the rational numbers,
ζ(−1) = −(order of K₂ of the integers) / w₂, with K₂ of the integers of order 2
and w₂ = 24. K₂ is not in Mathlib, so only the numbers are stated. Deligne and
Ribet (1980) proved that w₂ times ζ(−1) is a whole number for every totally
real field; this node is the rational case of that, in numbers.

Proof: `RNSSolutions/BirchTateRational.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.BirchTateRational

/-- **ζ(−1) = −1/12.** -/
def zeta_neg_one : Prop := riemannZeta (-1) = -1 / 12

/-- **w₂ times ζ(−1) is −2.** There is a largest cycle length on which every
open position squares to 1; it is 24, and it times ζ(−1) is −2. -/
def w2_times_zeta : Prop :=
  ∃ m : ℕ, m ≠ 0 ∧ (∀ u : (ZMod m)ˣ, u ^ 2 = 1) ∧
    (∀ k : ℕ, k ≠ 0 → (∀ u : (ZMod k)ˣ, u ^ 2 = 1) → k ≤ m) ∧
    m = 24 ∧ (m : ℂ) * riemannZeta (-1) = -2

end RNS.BirchTateRational
