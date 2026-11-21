/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# OrbitalTrace — the trace on one wheel's loop, and why it vanishes below the wheel

Scaling by a number `γ` above 1 (for a prime wheel, `γ` is the prime) turns
the positive numbers into a loop: identify each positive number with its
multiples by every power of `γ`. A test function `φ` on the positive numbers
acts on functions on the loop by multiplicative convolution, and its trace
is the sum of its eigenvalues, one for each exponential wave on the loop.
Those eigenvalues are the Mellin transform of `φ` at the evenly spaced points
`2πi m / log γ` (here `m` runs over the whole numbers), the same points as
the zeros of the wheel's Euler factor in `EulerFactorZeros`.

In the logarithmic coordinate `u` (a positive number is `e^u`) the Mellin
transform of `φ` at `-2πi w` is the Fourier transform of `ψ(u) = φ(e^u)` at
`w`. The claims are stated that way, with `ψ` a Schwartz function.

Poisson summation turns the sum of the eigenvalues into a sum over the
loop's own points: it equals `log γ` times the sum of `φ` at the powers of
`γ` (`orbital_trace_poisson`). So if `φ` vanishes outside the open interval
from 1 to `γ` the trace is zero (`orbital_trace_vanishes`): no power of `γ`
lies strictly between 1 and `γ`. For a prime wheel this says a test function
that lives below the prime's own scale never sees that wheel.

This is the toy example of §1.2.8 of A. M. Masullo, *The Music of the
Primes* (preprint, 2026), the model for the vanishing of all but finitely
many of his orbital traces. Metadata: `formalization.yaml`.
-/

open scoped FourierTransform SchwartzMap

namespace RNS.OrbitalTrace

/-- **The trace on the loop by Poisson summation.** For `γ > 1` and a test
function `φ` on the positive numbers whose logarithmic form `ψ(u) = φ(e^u)` is
a Schwartz function, the sum over all whole numbers `m` of the Fourier
transform of `ψ` at `m / log γ` (the Mellin transform of `φ` at the loop's
eigenvalue points) equals `log γ` times the sum of `φ` at every power of `γ`. -/
def orbital_trace_poisson : Prop :=
  ∀ γ : ℝ, 1 < γ → ∀ (φ : ℝ → ℂ) (ψ : 𝓢(ℝ, ℂ)), (∀ u : ℝ, ψ u = φ (Real.exp u)) →
    ∑' m : ℤ, 𝓕 (ψ : ℝ → ℂ) ((m : ℝ) / Real.log γ) =
      (Real.log γ : ℂ) * ∑' k : ℤ, φ (γ ^ k)

/-- **The trace vanishes below the wheel.** If moreover `φ` vanishes outside
the open interval from 1 to `γ`, the sum of the eigenvalues is zero. -/
def orbital_trace_vanishes : Prop :=
  ∀ γ : ℝ, 1 < γ → ∀ (φ : ℝ → ℂ) (ψ : 𝓢(ℝ, ℂ)), (∀ u : ℝ, ψ u = φ (Real.exp u)) →
    (∀ t : ℝ, t ∉ Set.Ioo 1 γ → φ t = 0) →
    ∑' m : ℤ, 𝓕 (ψ : ℝ → ℂ) ((m : ℝ) / Real.log γ) = 0

end RNS.OrbitalTrace
