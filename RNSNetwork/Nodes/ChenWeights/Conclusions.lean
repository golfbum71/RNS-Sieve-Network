/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# ChenWeights — a weight that only numbers with at most two prime factors pass

Chen's weighted sieve. Fix a cutoff `y` (the wheels are the primes below it)
and take a number from 1 up to just below the cube of the cutoff. Start from
one, and subtract one half for each wheel dividing the number, one half for
each way of writing the number as a wheel times two primes at least the cutoff
(the smaller of the two first), and one half for each wheel whose square
divides the number. What is left is at most one when the number is a prime or
a product of two primes (counted with repetition), and at most zero otherwise.

So summing this weight over a set of candidates gives a lower bound for the
candidates with at most two prime factors: the weight Chen's theorem sieves
with (Tao, 254A Supplement 5). The finite case split: with no wheel dividing
the number, the number is below the cube of the cutoff and has at most two
prime factors; with exactly one wheel and not its square, the rest is a
product of two large primes; with two or more wheels the weight is already at
most zero.

Proof: `RNSSolutions/ChenWeights.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.ChenWeights

/-- The wheels (primes below `y`) dividing `n`. -/
def small_factors (y n : Nat) : Finset Nat :=
  n.primeFactors.filter (fun p => p < y)

/-- The wheels (primes below `y`) whose square divides `n`. -/
def small_square_factors (y n : Nat) : Finset Nat :=
  n.primeFactors.filter (fun p => p < y ∧ p ^ 2 ∣ n)

/-- The ways of writing `n` as a wheel (a prime below `y`) times two primes at
least `y`, the smaller of the two first. -/
def chen_triples (y n : Nat) : Finset (Nat × Nat × Nat) :=
  (n.primeFactors ×ˢ n.primeFactors ×ˢ n.primeFactors).filter
    (fun t => t.1 < y ∧ y ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 * t.2.1 * t.2.2 = n)

/-- **Chen's weight is at most the indicator of at most two prime factors.**
For `1 ≤ n < y ^ 3`: one minus half the wheels dividing `n`, minus half the
ways of writing `n` as a wheel times two primes at least `y`, minus half the
wheels whose square divides `n`, is at most 1 if `n` has at most two prime
factors (with repetition) and at most 0 otherwise. -/
def chen_weight_le : Prop :=
  ∀ y n : Nat, 1 ≤ n → n < y ^ 3 →
    1 - ((small_factors y n).card : ℝ) / 2 - ((chen_triples y n).card : ℝ) / 2
        - ((small_square_factors y n).card : ℝ) / 2
      ≤ if ArithmeticFunction.cardFactors n ≤ 2 then (1 : ℝ) else 0

end RNS.ChenWeights
