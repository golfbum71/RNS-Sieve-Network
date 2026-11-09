/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import RNSNetwork.Nodes.BrunTwinBound.Conclusions   -- `twin_prime_count`
import Mathlib.NumberTheory.ArithmeticFunction.Misc   -- `ArithmeticFunction.cardDistinctFactors`
import Mathlib.Analysis.SpecialFunctions.Log.Basic    -- `Real.log`

/-!
# SelbergTwinRails — Selberg's sieve on the twin columns

Take the wheels from 5 up to (not including) a cut-off. A position survives the
twin columns when neither it nor the position two further on has one of these
wheels as a factor. Each wheel blocks two positions of its cycle, so its share
is 2 over the wheel; the wheels 2 and 3 are left out, because there the twin
columns are already fixed (`GapTracks`) and a share must stay below 1.

Built so far: the wheels form a Selberg sieve problem, and
Selberg's bound (`SelbergBound`) gives, for any level at least 1: the
survivors among the positions 1 to `N` number at most `N` over Selberg's twin
sum, plus, over the divisors of the wheel product up to the level, 6 to the
number of prime factors. Selberg's twin sum adds up, over the divisors `l` of
the wheel product with `l²` at most the level, the product over the prime
factors of `l` of 2 over (the prime − 2). The error 6 = 3 × 2: Selberg's weights
contribute 3 per prime factor, and `BrunTwinCount` bounds the error of each
divisor by 2 per prime factor.

Also built: a lower bound for the twin sum of order log² of the level (after
Ford, Theorem 4.4). When the level is at least 6⁴ and below the square of the
cut-off, the twin sum is at least (log y − 4 log 6)² / 576. The constant is
crude; the order is the point.

Also built: Selberg's bound for twin primes in order. From `N` at least 5184⁸
on, the twin prime pairs up to `N` number at most 40000 N / log² N: take the
level t² and the cut-off t² + 1, with t the eighth root of `N` rounded down.

Later stage (planned): the constant four times the twin-prime constant.

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

/-- **The twin sum grows like log² of the level.** When the level `y` is at
least 6⁴ and below the square of the cut-off `z`, Selberg's twin sum is at
least (log y − 4 log 6)² / 576. -/
def twin_selberg_sum_lower : Prop :=
  ∀ (z : ℕ) (y : ℝ), (6 : ℝ) ^ 4 ≤ y → y < (z : ℝ) ^ 2 →
    (Real.log y - 4 * Real.log 6) ^ 2 / 576 ≤ twin_selberg_sum z y

/-- **Selberg's bound for twin primes.** From `N` at least 5184⁸ on, the twin
prime pairs whose smaller member is at most `N` number at most
40000 N / log² N. -/
def selberg_twin_bound : Prop :=
  ∀ N : ℕ, (5184 : ℝ) ^ 8 ≤ N →
    (RNS.BrunTwinBound.twin_prime_count N : ℝ) ≤ 40000 * N / Real.log N ^ 2

end RNS.SelbergTwinRails
