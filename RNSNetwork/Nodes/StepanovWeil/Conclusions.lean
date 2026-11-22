/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# StepanovWeil — the square-root bound for the residue character of any pattern

On the wheel of an odd prime `p`, take an offset pattern whose members sit on
different positions of the wheel, and multiply the distances of a position
from all of them. Adding the quadratic character of that product around the
whole wheel gives a total whose square is at most (the number of offsets minus
1) squared times `p`: a sum of `p` terms of size 1 cancels down to about the
square root of `p`. This is Weil's bound (1948) for the curve
y² = product of the distances; Stepanov (1969) found an elementary proof by
an auxiliary polynomial, completed in this form by Schmidt.

Cited, not proved in Lean. Metadata: `formalization.yaml`.
-/

namespace RNS.StepanovWeil

/-- **Weil's bound, pattern form** (cited). On an odd prime wheel, for an offset
pattern with at least one member and no two members on the same position, the
square of the character sum of the product of distances is at most (pattern
size − 1)² times the wheel size. -/
def weil_pattern_bound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ T : Finset ℕ, 0 < T.card → w T p = T.card →
    (∑ x : ZMod p, quadraticChar (ZMod p) (∏ t ∈ T, (x + (t : ZMod p)))) ^ 2 ≤
      ((T.card : ℤ) - 1) ^ 2 * p

end RNS.StepanovWeil
