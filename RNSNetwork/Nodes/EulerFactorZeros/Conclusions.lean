/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# EulerFactorZeros — one wheel's Euler factor, and why two wheels never share a zero

Each prime wheel has an Euler factor, one minus the prime raised to the power
minus `s`. Its zeros are evenly spaced up the imaginary axis, one every
`2π / log p` (here `p` is the wheel's prime and `s` the complex exponent).
That spacing is the analytic face of the wheel's cycle: the wheel's own
period, measured on the logarithmic scale.

Two different prime wheels have periods `log p` and `log q` (here `q` is the
second wheel's prime) that never line up: no whole multiple of one equals a
whole multiple of the other, except zero. That is unique factorization
(a power of one prime is never a power of another), the same fact that makes
the wheels independent in the Chinese Remainder Theorem. So the Euler
factors of two different wheels have exactly one zero in common, at `s = 0`.

This is the case of the rational numbers of Theorem 1.7.1.1(1) and (3) in
A. M. Masullo, *The Music of the Primes* (preprint, 2026), where it is used
to choose the topologies for a trace formula. Metadata: `formalization.yaml`.
-/

namespace RNS.EulerFactorZeros

/-- **The zeros of one wheel's Euler factor.** For a prime `p`, the Euler
factor `1 - p^(-s)` vanishes exactly at the whole multiples of `2πi / log p`. -/
def euler_factor_zeros : Prop :=
  ∀ p : ℕ, p.Prime → ∀ s : ℂ,
    (1 : ℂ) - (p : ℂ) ^ (-s) = 0 ↔
      ∃ k : ℤ, s = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (Real.log p : ℂ)

/-- **The periods of two wheels never line up.** For different primes `p` and
`q`, a whole multiple `a` of `log p` equals a whole multiple `b` of `log q`
only when both multiples are zero. -/
def log_periods_independent : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ∀ a b : ℤ,
    (a : ℝ) * Real.log p = (b : ℝ) * Real.log q → a = 0 ∧ b = 0

/-- **Two wheels share one zero.** For different primes `p` and `q`, the only
common zero of the Euler factors `1 - p^(-s)` and `1 - q^(-s)` is `s = 0`. -/
def euler_factor_common_zero : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ∀ s : ℂ,
    (1 : ℂ) - (p : ℂ) ^ (-s) = 0 → (1 : ℂ) - (q : ℂ) ^ (-s) = 0 → s = 0

end RNS.EulerFactorZeros
