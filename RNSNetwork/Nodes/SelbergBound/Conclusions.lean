/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ArithmeticFunction.Misc   -- `ArithmeticFunction.cardDistinctFactors`

/-!
# SelbergBound — Selberg's upper bound sieve

A sieve problem in Mathlib's form (`SelbergSieve`): a weighted finite set, the
product of the wheels to sift by, a multiplicative density `ν` with each wheel's
density strictly between 0 and 1, the total mass `X`, and a level. Selberg's
Λ² weights give: the sifted sum is at most `X` over Selberg's bounding sum, plus,
over the divisors `d` of the wheel product up to the level, 3 to the number of
prime factors of `d` times the size of the error at `d`. The bounding sum adds
up the Selberg terms `g(l)` over the divisors `l` with `l²` at most the level.

This is the engine for `SelbergTwinRails`: with the wheels from 5 up and each
wheel's density 2 over the wheel, it bounds the twin columns.

Mathlib states the sieve set-up and diagonalises the main term but stops before
the final bound. The proof here is Arend Mellendijk's from PrimeNumberTheoremAnd
(`Mathlib/NumberTheory/Sieve/Selberg.lean`, `selberg_bound_simple`), ported to
this repository and checked by its build.

Proof: `RNSSolutions/SelbergBound.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.SelbergBound

/-- Selberg's bounding sum: the Selberg terms `g(l)` summed over the divisors
`l` of the wheel product with `l²` at most the level. -/
noncomputable def bounding_sum (s : SelbergSieve) : ℝ :=
  ∑ l ∈ Nat.divisors s.prodPrimes,
    if (l : ℝ) ^ 2 ≤ s.level then s.toBoundingSieve.selbergTerms l else 0

/-- **The bounding sum is positive** (the term `l = 1` is there). -/
def bounding_sum_pos : Prop :=
  ∀ s : SelbergSieve, 0 < bounding_sum s

/-- **Selberg's upper bound sieve.** The sifted sum is at most the total mass
over the bounding sum, plus, over the divisors `d` of the wheel product up to
the level, 3 to the number of prime factors of `d` times the size of the error
at `d`. -/
def selberg_bound : Prop :=
  ∀ s : SelbergSieve,
    BoundingSieve.siftedSum (s := s.toBoundingSieve) ≤
      s.totalMass / bounding_sum s +
        ∑ d ∈ Nat.divisors s.prodPrimes,
          if (d : ℝ) ≤ s.level then
            (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
              |BoundingSieve.rem (s := s.toBoundingSieve) d|
          else 0

end RNS.SelbergBound
