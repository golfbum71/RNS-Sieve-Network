/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import RNSNetwork.Nodes.BadWheels.Conclusions   -- `blocked`, `bad_product`
import Mathlib.NumberTheory.ArithmeticFunction.Misc   -- `ArithmeticFunction.cardDistinctFactors`
import Mathlib.Analysis.SpecialFunctions.Log.Basic    -- `Real.log`

/-!
# PatternUpperBound — every pattern of linear forms is at most its conjectured order

A pattern is a finite set of linear forms, each a pair `(a, b)` meaning the form
`a·n + b` (the encoding of `LinearForms` and `BadWheels`). The forms are taken
*primitive*: the leading coefficient is at least 1 and the two coefficients
share no factor. A position fits the pattern when every form is prime there.

The wheel of size `p` blocks the positions (remainders below `p`) where some
form is divisible by `p`. By `BadWheels` it blocks at most one position per
form, and exactly one per form unless the wheel divides the bad product of the
pattern. Take as sieve the wheels below a cut-off that are larger than the
number of forms and block at least one position. Each such wheel keeps its own
share: the number it blocks over the wheel. The bad wheels stay in the sieve
with their smaller share.

Built here, by Selberg's sieve (`SelbergBound`), with `k` the number of forms:

* the multiples count: for any set of prime wheels, the positions 1 to `N`
  where their product divides the product of the forms number `N` times the
  product of their blocked counts over their product, off by at most that
  product of blocked counts (Chinese Remainder Theorem);
* Selberg's bound for the pattern: the survivors number at most `N` over
  Selberg's pattern sum, plus an error of `3k` to the number of prime factors
  for each divisor up to the level;
* the pattern sum grows like the `k`-th power of log of the level: from a
  starting level depending only on `k`, a constant depending only on `k`
  times log^k of the level is at most the pattern sum times the bad factor;
* the count: positions up to `N` where every form is prime number at most a
  constant depending only on `k`, times the bad factor, times N / log^k N,
  from a start depending only on `k`.

The bad factor is the product, over the wheels larger than `k` dividing the bad
product, of (the wheel − the positions it blocks) over (the wheel − `k`). It
depends on the pattern only through its bad wheels. For a prime pair at gap
`h` (the forms `n` and `n + h`) it is the product over the odd wheels dividing
`h` of (wheel − 1) over (wheel − 2): the gap's own correction (`GapConstant`).
For the Sophie Germain pair (`n` and `2n + 1`) it is 1.

This is Ford's Theorem 2.5 with the singular series replaced by the product of
its bad-wheel factors; the constant is not explicit in the statement (it is
explicit in the proof). Admissibility is not assumed: an inadmissible pattern
has finitely many fitting positions and satisfies the bound anyway.

Proof: `RNSSolutions/PatternUpperBound.lean`. Rests on `SelbergBound` and
`BadWheels`. Metadata: `formalization.yaml`.
-/

namespace RNS.PatternUpperBound

open RNS.BadWheels

/-- The product of the forms of `L` at the position `m`. -/
def pattern_value (L : Finset (ℕ × ℕ)) (m : ℕ) : ℕ := ∏ ℓ ∈ L, (ℓ.1 * m + ℓ.2)

/-- The number of positions the wheel of size `p` blocks. -/
def blocked_count (L : Finset (ℕ × ℕ)) (p : ℕ) : ℕ := (blocked L p).card

/-- The product of the blocked counts of the wheels in `D`. -/
def pattern_rho (L : Finset (ℕ × ℕ)) (D : Finset ℕ) : ℕ := ∏ p ∈ D, blocked_count L p

/-- Primitive forms: every leading coefficient is at least 1 and the two
coefficients of each form share no factor. -/
def primitive_forms (L : Finset (ℕ × ℕ)) : Prop := ∀ ℓ ∈ L, 1 ≤ ℓ.1 ∧ Nat.Coprime ℓ.1 ℓ.2

/-- The sieve: the prime wheels below `z`, larger than the number of forms,
that block at least one position. -/
def pattern_wheels (L : Finset (ℕ × ℕ)) (z : ℕ) : Finset ℕ :=
  (active_primes z).filter (fun p => L.card < p ∧ 0 < blocked_count L p)

/-- The product of the sieve wheels. -/
def pattern_wheel_product (L : Finset (ℕ × ℕ)) (z : ℕ) : ℕ := ∏ p ∈ pattern_wheels L z, p

/-- The survivors among the positions 1 to `N`: those where no sieve wheel
divides the product of the forms. -/
def pattern_sifted (L : Finset (ℕ × ℕ)) (N z : ℕ) : ℕ :=
  ((Finset.Ioc 0 N).filter
    (fun m => Nat.Coprime (pattern_wheel_product L z) (pattern_value L m))).card

/-- Selberg's pattern sum: over the divisors `l` of the wheel product with `l²`
at most the level `y`, the product over the prime factors `p` of `l` of the
blocked count over (`p` − the blocked count). -/
noncomputable def pattern_selberg_sum (L : Finset (ℕ × ℕ)) (z : ℕ) (y : ℝ) : ℝ :=
  ∑ l ∈ Nat.divisors (pattern_wheel_product L z),
    if (l : ℝ) ^ 2 ≤ y then
      ∏ p ∈ l.primeFactors, (blocked_count L p : ℝ) / ((p : ℝ) - blocked_count L p)
    else 0

/-- The bad factor: over the wheels larger than the number of forms dividing
the bad product, (the wheel − its blocked count) over (the wheel − the number
of forms). -/
noncomputable def bad_factor (L : Finset (ℕ × ℕ)) : ℝ :=
  ∏ q ∈ (bad_product L).natAbs.primeFactors.filter (fun q => L.card < q),
    ((q : ℝ) - blocked_count L q) / ((q : ℝ) - L.card)

/-- The positions from 1 to `N` where every form is prime. -/
def pattern_count (L : Finset (ℕ × ℕ)) (N : ℕ) : ℕ :=
  ((Finset.Ioc 0 N).filter (fun n => ∀ ℓ ∈ L, (ℓ.1 * n + ℓ.2).Prime)).card

/-- **The multiples count.** For any set of prime wheels `D`, the positions `m`
from 1 to `N` where the product of `D` divides the product of the forms number
`N` times the product of the blocked counts over the product of `D`, off by at
most the product of the blocked counts. -/
def pattern_multiples_count : Prop :=
  ∀ (L : Finset (ℕ × ℕ)) (D : Finset ℕ) (N : ℕ), (∀ p ∈ D, p.Prime) →
    |(((Finset.Ioc 0 N).filter (fun m => D.prod id ∣ pattern_value L m)).card : ℝ)
        - (N : ℝ) * (pattern_rho L D : ℝ) / (D.prod id : ℝ)|
      ≤ (pattern_rho L D : ℝ)

/-- **Selberg's bound for the pattern.** For a nonempty pattern of primitive
forms and any level `y` at least 1, the survivors among the positions 1 to `N`
number at most `N` over Selberg's pattern sum, plus, over the divisors `d` of
the wheel product up to the level, `3k` to the number of prime factors of `d`
(`k` the number of forms). -/
def pattern_sieve_bound : Prop :=
  ∀ L : Finset (ℕ × ℕ), L.Nonempty → primitive_forms L →
    ∀ (N z : ℕ) (y : ℝ), 1 ≤ y →
      (pattern_sifted L N z : ℝ) ≤ (N : ℝ) / pattern_selberg_sum L z y +
        ∑ d ∈ Nat.divisors (pattern_wheel_product L z),
          if (d : ℝ) ≤ y then
            (3 * (L.card : ℝ)) ^ ArithmeticFunction.cardDistinctFactors d
          else 0

/-- **The pattern sum grows like log^k of the level.** For every number of
forms `k ≥ 1` there are a constant `c > 0` and a starting level, depending only
on `k`, such that for every pattern of `k` primitive forms and every level `y`
from the start up to (not including) the square of the cut-off `z`, `c` times
log^k of the level is at most the bad factor times Selberg's pattern sum. -/
def pattern_selberg_sum_lower : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ c y₀ : ℝ, 0 < c ∧ 1 ≤ y₀ ∧
    ∀ L : Finset (ℕ × ℕ), primitive_forms L → L.card = k →
      ∀ (z : ℕ) (y : ℝ), y₀ ≤ y → y < (z : ℝ) ^ 2 →
        c * Real.log y ^ k ≤ bad_factor L * pattern_selberg_sum L z y

/-- **Every pattern at most its conjectured order.** For every number of forms
`k ≥ 1` there are a constant and a start, depending only on `k`, such that for
every pattern of `k` primitive forms and every `N` from the start, the
positions up to `N` where every form is prime number at most the constant
times the bad factor times N / log^k N. -/
def pattern_count_le : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ C N₀ : ℝ,
    ∀ L : Finset (ℕ × ℕ), primitive_forms L → L.card = k →
      ∀ N : ℕ, N₀ ≤ (N : ℝ) →
        (pattern_count L N : ℝ) ≤ C * bad_factor L * N / Real.log N ^ k

end RNS.PatternUpperBound
