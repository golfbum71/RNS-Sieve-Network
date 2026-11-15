/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SelbergTwinRails.Conclusions   -- `gap_pair_count`, `goldbach_count`, `pair_factor`
import RNSNetwork.Nodes.GapConstant.Conclusions        -- `odd_divisor_correction`
import Mathlib.Data.Nat.Totient

/-!
# GapPairs — prime pairs at any gap, and Goldbach pairs, by the gap's own constant

`SelbergTwinRails` bounds the prime pairs at a gap, and the Goldbach pairs of a
number, by 40000 N / log² N times a factor for the wheels dividing the gap: the
product, over the wheels from 5 up dividing it, of the wheel over the wheel
minus 2. This node puts that factor into the standard forms.

The conjectured count of pairs at a gap carries the correction of `GapConstant`:
the product, over the odd wheels dividing the gap, of the wheel minus 1 over the
wheel minus 2. The Selberg factor is at most that correction times the gap over
Euler's phi of the gap. So the pairs at any gap number at most 40000 N / log² N
times the conjectured correction times one extra factor, the gap over its
totient. The extra factor is the price of leaving the wheels that divide the
gap out of the sieve altogether (they block one position each, and the sieve of
`SelbergTwinRails` lets them block none).

In terms of the totient alone: the correction is at most the square of the gap
over its totient, so the pairs number at most 40000 N / log² N times the cube of
the gap over its totient.

Ford's Corollary 2.6 has the first power of the gap over its totient. That
sharper form needs the wheels dividing the gap kept in the sieve
(`PatternUpperBound`) and is not proved here.

Proof: `RNSSolutions/GapPairs.lean`. Rests on `SelbergTwinRails`. Metadata:
`formalization.yaml`.
-/

namespace RNS.GapPairs

open RNS.SelbergTwinRails RNS.GapConstant

/-- A number over its totient (Euler's phi). -/
noncomputable def totient_ratio (h : ℕ) : ℝ := (h : ℝ) / (Nat.totient h : ℝ)

/-- **The Selberg factor against the gap's own constant.** For `h > 0`, the
factor of `SelbergTwinRails` is at most the correction of `GapConstant` times
`h` over its totient. -/
def pair_factor_le_correction : Prop :=
  ∀ h : ℕ, 0 < h → pair_factor h ≤ odd_divisor_correction h * totient_ratio h

/-- **The correction against the totient.** For `h > 0`, the correction of
`GapConstant` is at most the square of `h` over its totient. -/
def correction_le_totient_ratio_sq : Prop :=
  ∀ h : ℕ, 0 < h → odd_divisor_correction h ≤ totient_ratio h ^ 2

/-- **Prime pairs at any gap.** For a gap `h > 0` and `N` at least 5184⁸, the
prime pairs up to `N` at gap `h` number at most 40000 times the gap's
correction times the gap over its totient, times N / log² N. -/
def gap_pair_bound : Prop :=
  ∀ h N : ℕ, 0 < h → (5184 : ℝ) ^ 8 ≤ N →
    (gap_pair_count h N : ℝ) ≤
      40000 * (odd_divisor_correction h * totient_ratio h) * N / Real.log N ^ 2

/-- **Goldbach pairs.** For `N` at least 5184⁸, the ways of writing `N` as a sum
of two primes number at most 40000 times the correction of `N` times `N` over
its totient, times N / log² N. -/
def goldbach_pair_bound : Prop :=
  ∀ N : ℕ, (5184 : ℝ) ^ 8 ≤ N →
    (goldbach_count N : ℝ) ≤
      40000 * (odd_divisor_correction N * totient_ratio N) * N / Real.log N ^ 2

/-- **Prime pairs at any gap, by the totient alone.** The same count is at most
40000 times the cube of the gap over its totient, times N / log² N. -/
def gap_pair_bound_totient : Prop :=
  ∀ h N : ℕ, 0 < h → (5184 : ℝ) ^ 8 ≤ N →
    (gap_pair_count h N : ℝ) ≤ 40000 * totient_ratio h ^ 3 * N / Real.log N ^ 2

/-- **Goldbach pairs, by the totient alone.** -/
def goldbach_pair_bound_totient : Prop :=
  ∀ N : ℕ, (5184 : ℝ) ^ 8 ≤ N →
    (goldbach_count N : ℝ) ≤ 40000 * totient_ratio N ^ 3 * N / Real.log N ^ 2

end RNS.GapPairs

/-! ## Ford's first-power form (added 2026-11-15, from `PatternUpperBound`)

`PatternUpperBound` keeps the wheels dividing the gap in the sieve, each at its
smaller share (one blocked position instead of two). The pair at gap `h` then
carries only its bad factor, which is at most the gap's own correction; and the
correction is at most twice the gap over its totient. -/

namespace RNS.GapPairs

open RNS.SelbergTwinRails RNS.GapConstant

/-- **Prime pairs at any gap, by the gap's own correction alone.** There are a
constant and a start such that for every gap `h > 0` and `N` from the start,
the prime pairs up to `N` at gap `h` number at most the constant times the
gap's correction times N / log² N. -/
def gap_pair_bound_ford : Prop :=
  ∃ C N₀ : ℝ, ∀ h N : ℕ, 0 < h → N₀ ≤ (N : ℝ) →
    (gap_pair_count h N : ℝ) ≤ C * odd_divisor_correction h * N / Real.log N ^ 2

/-- **The correction against the totient, first power.** For `h > 0`, the
correction of `GapConstant` is at most twice `h` over its totient. -/
def correction_le_two_totient_ratio : Prop :=
  ∀ h : ℕ, 0 < h → odd_divisor_correction h ≤ 2 * totient_ratio h

/-- **Prime pairs at any gap, Ford's form** (Ford, Corollary 2.6). There are a
constant and a start such that for every gap `h > 0` and `N` from the start,
the prime pairs up to `N` at gap `h` number at most the constant times the gap
over its totient times N / log² N. -/
def gap_pair_bound_ford_totient : Prop :=
  ∃ C N₀ : ℝ, ∀ h N : ℕ, 0 < h → N₀ ≤ (N : ℝ) →
    (gap_pair_count h N : ℝ) ≤ C * totient_ratio h * N / Real.log N ^ 2

end RNS.GapPairs
