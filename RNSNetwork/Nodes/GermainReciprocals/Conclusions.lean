/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PatternUpperBound.Conclusions     -- `pattern_count_le`
import RNSNetwork.Nodes.PatternReciprocals.Conclusions    -- `position_count`, `reciprocal_of`

/-!
# GermainReciprocals — the Sophie Germain primes' reciprocals add up to a finite total

A Sophie Germain prime is a prime `p` with `2p + 1` also prime. In the network's
terms it is a position where both linear forms `n` and `2n + 1` are prime: the
pattern of the two forms `(1, 0)` and `(2, 1)`.

On every wheel from 3 up the two forms block two different positions (0 and
the half of the wheel minus one), so no odd wheel is bad and the bad factor of
`PatternUpperBound` is 1. Hence:

* the Sophie Germain primes up to `N` number at most a constant times
  N / log² N from some start on (`PatternUpperBound`);
* the sum of their reciprocals is finite (`PatternReciprocals`' general fact).

Proof: `RNSSolutions/GermainReciprocals.lean`. Rests on `PatternUpperBound`,
`BadWheels` and `PatternReciprocals`. Metadata: `formalization.yaml`.
-/

namespace RNS.GermainReciprocals

/-- The Sophie Germain condition at a position: the position and twice it
plus one are both prime. -/
def germain (n : ℕ) : Prop := n.Prime ∧ (2 * n + 1).Prime

/-- **At most a constant times N / log² N.** From some start on, the Sophie
Germain primes up to `N` number at most a constant times N / log² N. -/
def germain_count_le : Prop :=
  ∃ C N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
    (RNS.PatternReciprocals.position_count germain N : ℝ) ≤ C * N / Real.log N ^ 2

/-- **The reciprocals add up to a finite total.** -/
def germain_reciprocal_summable : Prop :=
  Summable (RNS.PatternReciprocals.reciprocal_of germain)

end RNS.GermainReciprocals
