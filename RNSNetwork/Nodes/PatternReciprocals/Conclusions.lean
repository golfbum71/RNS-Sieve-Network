/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GapPairs.Conclusions   -- `gap_pair_bound_totient`
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# PatternReciprocals — reciprocal sums converge for every pattern of two or more

A pattern is a finite set of offsets; a position fits the pattern when the
position plus every offset is prime. Brun's theorem (`BrunTheorem`) says the
reciprocals of the twin positions (the pattern 0, 2) add up to a finite total.
This node does the same for every pattern with at least two offsets: triples
such as 0, 2, 6, quadruples such as 0, 2, 6, 8, pairs at any gap.

The reason is one general fact, proved here first: if the positions with some
property, up to any point past a start, number at most a constant times that
point over the square of its logarithm, then the reciprocals of those
positions add up to a finite total. (The stretch from one power of 2 to the
next adds at most a constant over the square of the exponent, and those add
up.)

A position fitting a pattern with two different offsets puts a prime pair at
the gap between them, so `GapPairs` bounds the count, and the general fact
applies. The pattern need not be admissible: an inadmissible pattern has only
finitely many positions, and the statement holds for it too.

Proof: `RNSSolutions/PatternReciprocals.lean`. Rests on `GapPairs`.
Metadata: `formalization.yaml`.
-/

namespace RNS.PatternReciprocals

open Classical in
/-- The positions from 1 to `N` with the property `P`. -/
noncomputable def position_count (P : ℕ → Prop) (N : ℕ) : ℕ :=
  ((Finset.Ioc 0 N).filter P).card

open Classical in
/-- One over the position when it has the property `P`, and zero otherwise
(also zero at position 0). -/
noncomputable def reciprocal_of (P : ℕ → Prop) (n : ℕ) : ℝ :=
  if P n then 1 / (n : ℝ) else 0

/-- A position fits the pattern of offsets `H` when the position plus every
offset is prime. -/
def fits (H : Finset ℕ) (n : ℕ) : Prop := ∀ h ∈ H, (n + h).Prime

/-- **The general fact.** If, from some start on, the positions with `P` up to
`N` number at most a constant times `N` over log² N, then the reciprocals of
the positions with `P` add up to a finite total. -/
def summable_of_count_bound : Prop :=
  ∀ P : ℕ → Prop, (∃ C N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (position_count P N : ℝ) ≤ C * N / Real.log N ^ 2) →
    Summable (reciprocal_of P)

/-- **Patterns of two or more.** For every pattern with at least two offsets,
the positions fitting it, up to `N`, number at most a constant (depending on
the pattern) times N / log² N from some start on. -/
def pattern_count_bound : Prop :=
  ∀ H : Finset ℕ, 2 ≤ H.card →
    ∃ C N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (position_count (fits H) N : ℝ) ≤ C * N / Real.log N ^ 2

/-- **Reciprocal sums converge for every pattern of two or more.** For every
pattern with at least two offsets, the reciprocals of the positions fitting it
add up to a finite total. -/
def pattern_reciprocal_summable : Prop :=
  ∀ H : Finset ℕ, 2 ≤ H.card → Summable (reciprocal_of (fits H))

end RNS.PatternReciprocals
