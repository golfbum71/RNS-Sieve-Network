/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# HurwitzZetaZero — the Hurwitz zeta function at 0

For a point `x` with `0 < x ≤ 1`, the Hurwitz zeta function at 0 equals one
half minus `x`. Equivalently, the sawtooth's Fourier series converges to the
sawtooth. This is the bridge between L-function values and the finite sums
over a cycle's residues that `GermainCriterion` needs.

Cited, not proved here: Mathlib gives the Hurwitz zeta values at the negative
integers but stops short of 0 (`hurwitzZeta_neg_nat` asks for a nonzero
exponent), because the matching Fourier series converges only conditionally.
Metadata: `formalization.yaml`.
-/

namespace RNS.HurwitzZetaZero

/-- **The Hurwitz zeta function at 0.** For `0 < x ≤ 1`, Mathlib's
`hurwitzZeta x 0` equals `1/2 - x`. -/
def hurwitz_zeta_at_zero : Prop :=
  ∀ x : ℝ, 0 < x → x ≤ 1 → HurwitzZeta.hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ)

end RNS.HurwitzZetaZero
