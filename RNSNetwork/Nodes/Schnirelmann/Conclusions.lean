/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import RNSNetwork.Nodes.SelbergTwinRails.Conclusions   -- `goldbach_count`, `pair_factor`
import Mathlib.Combinatorics.Schnirelmann              -- `schnirelmannDensity`
import Mathlib.NumberTheory.PrimeCounting              -- `Nat.primeCounting`

/-!
# Schnirelmann — every number is a sum of boundedly many primes

There is a number `c` such that every number from 2 on is a sum of at most `c`
primes (Schnirelmann 1930). The wheels enter through one input only: Selberg's
upper bound for the Goldbach pairs of a number (`SelbergTwinRails`), which
carries a factor for the wheels from 5 up that divide the number.

The chain of claims:

* **First moment.** The Goldbach pairs of the numbers up to twice `N` total at
  least the square of the number of primes up to `N`.
* **The factor on average.** The square of the Selberg factor, added over the
  numbers from 1 to `N`, is at most a constant times `N`: the wheels dividing
  a number do not pile up on average.
* **Second moment.** From some point on, the squares of the Goldbach pair
  counts of the numbers up to `N`, added up and multiplied by the fourth power
  of log `N`, are at most a constant times the cube of `N`.
* **A positive share.** The numbers that are 0, 1 or a sum of two primes have
  positive Schnirelmann density (Cauchy–Schwarz on the two moments, with
  Chebyshev's lower bound for the number of primes).
* **Schnirelmann's inequality.** For two sets containing 0, the density of the
  sumset is at least the sum of the densities minus their product.
* **Basis.** A set containing 0 with positive density reaches every number
  with a fixed number of summands.
* **The theorem.** Every number from 2 on is a sum of boundedly many primes.

Letters used in the statements: `N` — how far the count runs; `n` — a number;
`A`, `B` — sets of numbers; `h` — a number of summands; `C`, `c` — constants.

Proof: `RNSSolutions/Schnirelmann.lean`. Metadata: `formalization.yaml`.
-/

open scoped Pointwise

namespace RNS.Schnirelmann

open RNS.SelbergTwinRails

/-- The numbers that are 0, 1, or a sum of two primes. -/
def prime_pair_sums : Set ℕ :=
  {n | n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a + b = n}

/-- The sums of `h` members of `A`. -/
def fold_sum (A : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | h + 1 => fold_sum A h + A

/-- **First moment of the Goldbach pairs.** The Goldbach pair counts of the
numbers from 0 to `2 * N` total at least the square of the number of primes up
to `N`. -/
def goldbach_first_moment : Prop :=
  ∀ N : ℕ, Nat.primeCounting N ^ 2 ≤ ∑ n ∈ Finset.range (2 * N + 1), goldbach_count n

/-- **The Selberg factor on average.** There is a constant `C` such that the
squares of the Selberg factor of the numbers from 1 to `N` total at most
`C * N`, for every `N`. -/
def pair_factor_second_moment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∑ n ∈ Finset.Ioc 0 N, pair_factor n ^ 2 ≤ C * N

/-- **Second moment of the Goldbach pairs.** There are a constant `C` and a
starting point `N₀` such that, from `N₀` on, the squares of the Goldbach pair
counts of the numbers from 0 to `N`, added up and multiplied by log⁴ `N`, are
at most `C * N³`. -/
def goldbach_second_moment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (∑ n ∈ Finset.range (N + 1), (goldbach_count n : ℝ) ^ 2) * Real.log N ^ 4
      ≤ C * (N : ℝ) ^ 3

open Classical in
/-- **A positive share of numbers are sums of two primes.** The set of numbers
that are 0, 1 or a sum of two primes has positive Schnirelmann density. -/
def prime_pair_sums_density : Prop :=
  0 < schnirelmannDensity prime_pair_sums

open Classical in
/-- **Schnirelmann's inequality.** For two sets containing 0, the density of
the sumset is at least the sum of the two densities minus their product. -/
def schnirelmann_inequality : Prop :=
  ∀ A B : Set ℕ, 0 ∈ A → 0 ∈ B →
    schnirelmannDensity A + schnirelmannDensity B
        - schnirelmannDensity A * schnirelmannDensity B
      ≤ schnirelmannDensity (A + B)

open Classical in
/-- **Schnirelmann's basis theorem.** A set containing 0 with positive density
reaches every number with some fixed number `h` of summands. -/
def schnirelmann_basis : Prop :=
  ∀ A : Set ℕ, 0 ∈ A → 0 < schnirelmannDensity A → ∃ h : ℕ, fold_sum A h = Set.univ

/-- **Schnirelmann's theorem.** There is a number `c` such that every number
from 2 on is the sum of a list of at most `c` primes. -/
def schnirelmann_bounded_sum : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, 2 ≤ n →
    ∃ l : List ℕ, l.length ≤ c ∧ (∀ p ∈ l, p.Prime) ∧ l.sum = n

end RNS.Schnirelmann
