/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.PrimeCounting

/-!
# VonKochBound — the Riemann hypothesis as an error term, against the Brocard window

Von Koch (1901): the Riemann hypothesis is equivalent to the prime count up to
`x` differing from the logarithmic integral by at most a constant times the
square root of `x` times the logarithm of `x`. Only the forward direction is
recorded here, and it is cited.

The proved claim compares sizes: once `x` is past e⁴, that error term is
larger than four times the square root of `x`, the guaranteed length of the
Brocard window (node `BrocardWindowLength`) measured in the same units. This
compares two sizes only; it does not show that the Riemann hypothesis fails to
imply Brocard's conjecture.

Proofs: `RNSSolutions/VonKochBound.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.VonKochBound

/-- The logarithmic integral from 2 (offset form). -/
noncomputable def log_integral (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- The Riemann hypothesis (open), as stated in Mathlib. -/
def riemann_hypothesis : Prop := RiemannHypothesis

/-- **Von Koch's bound** (cited). If the Riemann hypothesis holds, the prime
count up to `x` is within a constant times the square root of `x` times its
logarithm of the logarithmic integral, for every `x` from 2 on. -/
def von_koch_bound : Prop :=
  riemann_hypothesis → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - log_integral x| ≤ C * Real.sqrt x * Real.log x

/-- **The error term outgrows the window.** Once `x` is past e⁴, four times the
square root of `x` is smaller than the square root of `x` times its
logarithm. -/
def error_exceeds_window : Prop :=
  ∀ x : ℝ, Real.exp 4 < x → 4 * Real.sqrt x < Real.sqrt x * Real.log x

end RNS.VonKochBound
