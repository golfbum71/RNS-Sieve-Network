/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PileUpLock.Conclusions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# SmallDivisorPulse — every small number divides a speed of any counterexample

The runner to be lonely stands still; the others have the distinct nonzero
speeds in `S`. If some number from 2 up to the number of runners divides none of
the speeds, then at the time one over that number every moving runner sits a
whole number of that number's parts away from the start, never 0 of them, so at
least one part, which is at least one over the number of runners
(`small_divisor_time_works`). So in a set of speeds that is never lonely, each
number from 2 up to the number of runners divides some speed, and their least
common multiple divides the product of the speeds
(`counterexample_lcm_dvd_product`).

Rosenfeld 2025, Lemma 4 (arXiv 2509.14111). The general form of the even/odd
pulse. Uses only the vocabulary of `PileUpLock` (no claim of it).

Proof: `RNSSolutions/SmallDivisorPulse.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.SmallDivisorPulse

open RNS.PileUpLock

/-- **One over a small number works when it divides no speed.** If `j` is from
2 up to the number of runners and divides none of the speeds, the time `1 / j`
is lonely for the runner standing still. -/
def small_divisor_time_works : Prop :=
  ∀ (S : Finset ℤ) (j : ℕ), 2 ≤ j → j ≤ S.card + 1 → (∀ v ∈ S, ¬ (j : ℤ) ∣ v) →
    lonely_at S j 1

/-- **The small numbers divide the product of a counterexample's speeds.** If
the runner standing still never has a lonely moment, the least common multiple
of 2 up to the number of runners divides the product of the speeds. -/
def counterexample_lcm_dvd_product : Prop :=
  ∀ S : Finset ℤ, ¬ has_lonely_time S →
    (Finset.Icc 2 (S.card + 1)).lcm (fun j : ℕ => (j : ℤ)) ∣ ∏ v ∈ S, v

end RNS.SmallDivisorPulse
