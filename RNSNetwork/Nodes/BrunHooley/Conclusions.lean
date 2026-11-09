/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic

/-!
# BrunHooley — the product of upper sieves over ranges of wheels

Hooley's form of Brun's sieve splits the wheels into ranges, chooses an upper
sieve for each range (inclusion–exclusion stopped early for the large wheels,
late for the small ones), and multiplies them. This node proves the first
step, Ford's Lemma 2.1: the product of upper sieves is an upper sieve for all
the wheels together.

An upper sieve for a set of wheels gives a weight to each set of its wheels.
At a number, add the weights of the sets all of whose wheels divide it (the
sieve sum); the sieve is an upper sieve when that sum is at least 1 at every
number no wheel divides, and at least 0 at every other number.

* **The expansion.** The product of the sieve sums of the ranges is the sum,
  over every choice of one set of wheels from each range, of the product of
  their weights, counted at the numbers divisible by every chosen wheel: the
  combined sieve, whose weight on a choice is the product of the weights.
* **The product is an upper sieve.** The combined sieve sum is at least 1 at
  every number that no wheel of any range divides, and at least 0 elsewhere.

The bounds that make the sieve useful (Ford's Theorems 2.3 and 2.4: the
survivor count at most the length times the share times a small factor, plus
remainders) are planned, not proved here.

The wheels need not be primes, and the ranges need not be disjoint.

Proof: `RNSSolutions/BrunHooley.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.BrunHooley

/-- The sieve sum at `n` of the weights `wt` on the sets of wheels of `P`:
the weights of the sets all of whose wheels divide `n`. -/
noncomputable def sieve_sum (P : Finset ℕ) (wt : Finset ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ D ∈ P.powerset, if (∀ q ∈ D, q ∣ n) then wt D else 0

/-- `wt` is an upper sieve for the wheels `P`: its sieve sum is at least 1 at
every number no wheel of `P` divides, and at least 0 at every other number. -/
def is_upper_sieve (P : Finset ℕ) (wt : Finset ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if ∀ q ∈ P, ¬ q ∣ n then (1 : ℝ) else 0) ≤ sieve_sum P wt n

/-- The combined sieve sum at `n` for the ranges `P i` (`i` in `I`) with
weights `wt i`: over every choice `c` of one set of wheels `c i` from each
range, the product of the weights of the chosen sets, each counted when all
its wheels divide `n`. -/
noncomputable def combined_sieve_sum (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (wt : ℕ → Finset ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c ∈ I.pi (fun i => (P i).powerset),
    ∏ x ∈ I.attach, (if ∀ q ∈ c x.1 x.2, q ∣ n then wt x.1 (c x.1 x.2) else 0)

/-- **The expansion.** The combined sieve sum is the product of the sieve sums
of the ranges. -/
def combined_eq_product : Prop :=
  ∀ (I : Finset ℕ) (P : ℕ → Finset ℕ) (wt : ℕ → Finset ℕ → ℝ) (n : ℕ),
    combined_sieve_sum I P wt n = ∏ i ∈ I, sieve_sum (P i) (wt i) n

/-- **The product of upper sieves is an upper sieve** (Ford, Lemma 2.1). If
each range has an upper sieve, the combined sieve sum is at least 1 at every
number no wheel of any range divides, and at least 0 at every other number. -/
def product_upper_sieve : Prop :=
  ∀ (I : Finset ℕ) (P : ℕ → Finset ℕ) (wt : ℕ → Finset ℕ → ℝ),
    (∀ i ∈ I, is_upper_sieve (P i) (wt i)) →
    ∀ n : ℕ, (if ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ n then (1 : ℝ) else 0) ≤ combined_sieve_sum I P wt n

end RNS.BrunHooley
