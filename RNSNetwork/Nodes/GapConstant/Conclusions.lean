/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.TwinConstant.Conclusions
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Group.Nat.Even

/-!
# GapConstant — the constant for prime pairs at any even gap

For prime pairs a fixed even gap apart (the pattern `{0, gap}`), each wheel
blocks two positions, except a wheel dividing the gap, which blocks only one
(both members of the pair then sit at the same position of that wheel). The
wheel of size 2 always divides an even gap, just as it divides 2. So the
wheel-built constant for the gap is the twin-prime constant times, for each
odd prime dividing the gap, that prime minus one over that prime minus two.

A gap of six therefore has exactly twice the twin constant: the wheel of size
3 blocks one position instead of two, because a gap divisible by 6 keeps both
numbers in the same column. The pair (n, N − n) behind Goldbach's problem
blocks the positions 0 and N on each wheel, the same count as the gap pattern
`{0, N}`, so its constant is given by the same formula with the odd primes
dividing N. Hardy and Littlewood (1923).

Proof: `RNSSolutions/GapConstant.lean`. Rests on `SingularSeries`
(`factor_multipliable`) and `TwinConstant` (`twin_prime_constant_eq_classical`).
Metadata: `formalization.yaml`.
-/

namespace RNS.GapConstant

/-- The correction for the odd primes dividing `g`: the product of the prime
minus one over the prime minus two. -/
noncomputable def odd_divisor_correction (g : Nat) : ℝ :=
  ∏ p ∈ g.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- **The constant for any even gap.** For an even gap `g > 0`, the
Hardy–Littlewood constant of `{0, g}` is the twin constant (that of `{0, 2}`)
times the correction for the odd primes dividing `g`. -/
def gap_constant_eq_twin_mul : Prop :=
  ∀ g : Nat, g ≠ 0 → Even g →
    hardy_littlewood_constant {0, g} = hardy_littlewood_constant {0, 2} * odd_divisor_correction g

/-- **The same with the classical twin constant.** -/
def gap_constant_classical : Prop :=
  ∀ g : Nat, g ≠ 0 → Even g →
    hardy_littlewood_constant {0, g} =
      RNS.TwinConstant.twin_prime_classical_constant * odd_divisor_correction g

/-- **The gap of six has twice the twin constant.** -/
def sexy_constant_eq_two_twin : Prop :=
  hardy_littlewood_constant {0, 6} = 2 * hardy_littlewood_constant {0, 2}

/-- The wheel-built constant for the pair `n` and `N − n`: on the wheel of
size `p` the pair blocks the positions 0 and `N` modulo `p`. -/
noncomputable def goldbach_constant_of (N : Nat) : ℝ :=
  ∏' p : Nat.Primes, (p : ℝ) * ((p : ℝ) - (({0, N % (p : Nat)} : Finset Nat).card : ℝ)) /
    ((p : ℝ) - 1) ^ 2

/-- **The Goldbach constant.** For an even `N > 0`, the constant for the pair
`n`, `N − n` is the twin constant times the correction for the odd primes
dividing `N`. -/
def goldbach_constant : Prop :=
  ∀ N : Nat, N ≠ 0 → Even N →
    goldbach_constant_of N = hardy_littlewood_constant {0, 2} * odd_divisor_correction N

end RNS.GapConstant
