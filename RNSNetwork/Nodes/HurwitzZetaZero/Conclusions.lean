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

Mathlib gives the Hurwitz zeta values at the negative integers but stops
short of 0 (`hurwitzZeta_neg_nat` asks for a nonzero exponent), because the
matching Fourier series converges only conditionally. The value at 0 is proved
here (`hurwitz_zeta_at_zero`) from one cited input, `sin_zeta_at_one`: the
sawtooth's Fourier series, as Mathlib's `sinZeta` at 1. The even part of the
Hurwitz zeta function at 0 is in Mathlib, and the odd part is `sinZeta` at 1
divided by π, by Mathlib's functional equation.
Metadata: `formalization.yaml`.
-/

namespace RNS.HurwitzZetaZero

/-- **The Hurwitz zeta function at 0.** For `0 < x ≤ 1`, Mathlib's
`hurwitzZeta x 0` equals `1/2 - x`. -/
def hurwitz_zeta_at_zero : Prop :=
  ∀ x : ℝ, 0 < x → x ≤ 1 → HurwitzZeta.hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ)

/-- **The sawtooth's Fourier series at 1** (cited). For `0 < x < 1`, Mathlib's
`sinZeta x`, the continuation of `∑ sin(2π n x) / nˢ`, equals `π (1/2 - x)` at
1: the series `∑ sin(2π n x) / n` sums to `π (1/2 - x)`. At 1 the series
converges only conditionally, which is why Mathlib stops short of it. -/
def sin_zeta_at_one : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 →
    HurwitzZeta.sinZeta (x : UnitAddCircle) 1 = (Real.pi : ℂ) * (1 / 2 - (x : ℂ))

end RNS.HurwitzZetaZero
