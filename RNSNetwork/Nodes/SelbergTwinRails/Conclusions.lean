/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.ArithmeticFunction.Misc   -- `ArithmeticFunction.cardDistinctFactors`

/-!
# SelbergTwinRails — Selberg's sieve on the twin columns

Take the wheels from 5 up to (not including) a cut-off. A position survives the
twin columns when neither it nor the position two further on has one of these
wheels as a factor. Each wheel blocks two positions of its cycle, so its share
is 2 over the wheel; the wheels 2 and 3 are left out, because there the twin
columns are already fixed (`GapTracks`) and a share must stay below 1.

Stage 1 (this file so far): the wheels form a Selberg sieve problem, and
Selberg's bound (`SelbergBound`) gives, for any level at least 1: the
survivors among the positions 1 to `N` number at most `N` over Selberg's twin
sum, plus, over the divisors of the wheel product up to the level, 6 to the
number of prime factors. Selberg's twin sum adds up, over the divisors `l` of
the wheel product with `l²` at most the level, the product over the prime
factors of `l` of 2 over (the prime − 2). The error 6 = 3 × 2: Selberg's weights
contribute 3 per prime factor, and `BrunTwinCount` bounds the error of each
divisor by 2 per prime factor.

Later stages (planned): a lower bound for the twin sum of order log² of the
level (Ford, Theorem 4.4), giving at most a constant times `N / log² N` twin
pairs, and then the constant four times the twin-prime constant.

Proof: `RNSSolutions/SelbergTwinRails.lean`. Rests on `SelbergBound` and
`BrunTwinCount`. Metadata: `formalization.yaml`.
-/

namespace RNS.SelbergTwinRails

/-- The wheels from 5 up to (not including) `z`. -/
def twin_wheels (z : ℕ) : Finset ℕ := (active_primes z).filter (fun p => 5 ≤ p)

/-- The product of the wheels from 5 up to (not including) `z`. -/
def twin_wheel_product (z : ℕ) : ℕ := ∏ p ∈ twin_wheels z, p

/-- The positions from 1 to `N` that survive the twin columns: neither the
position nor the position plus 2 has a wheel from 5 up to `z` as a factor. -/
def twin_columns_sifted (N z : ℕ) : ℕ :=
  ((Finset.Ioc 0 N).filter
    (fun m => Nat.Coprime (twin_wheel_product z) (m * (m + 2)))).card

/-- Selberg's twin sum: over the divisors `l` of the wheel product with `l²` at
most the level `y`, the product over the prime factors of `l` of 2 over (the
prime − 2). -/
noncomputable def twin_selberg_sum (z : ℕ) (y : ℝ) : ℝ :=
  ∑ l ∈ Nat.divisors (twin_wheel_product z),
    if (l : ℝ) ^ 2 ≤ y then ∏ p ∈ l.primeFactors, (2 : ℝ) / ((p : ℝ) - 2) else 0

/-- **Selberg's bound for the twin columns.** For any level `y` at least 1, the
survivors of the twin columns among the positions 1 to `N` number at most `N`
over Selberg's twin sum, plus, over the divisors `d` of the wheel product up to
the level, 6 to the number of prime factors of `d`. -/
def selberg_twin_columns_bound : Prop :=
  ∀ (N z : ℕ) (y : ℝ), 1 ≤ y →
    (twin_columns_sifted N z : ℝ) ≤ (N : ℝ) / twin_selberg_sum z y +
      ∑ d ∈ Nat.divisors (twin_wheel_product z),
        if (d : ℝ) ≤ y then (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0

end RNS.SelbergTwinRails
