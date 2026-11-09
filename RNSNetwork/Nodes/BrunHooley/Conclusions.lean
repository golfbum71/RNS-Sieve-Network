/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
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

/-! ## The Brun–Hooley bound (Ford, Theorem 2.3)

Sift a finite set of positions `S`, each carrying a value `val n`, by prime
wheels split into ranges `P i` (`i` in `I`). In range `i` use Brun's sieve
stopped after the sets of at most `b i` wheels, with `b i` even. Write each
multiple count as `X` times a product of shares `g q` over the chosen wheels,
plus a remainder. Then the survivors are at most `X` times, over the ranges,
the product of one minus the shares plus the total share to the power
`b i + 1` over its factorial, plus the remainders of all choices of at most
`b i` wheels from each range. -/

namespace RNS.BrunHooley

/-- The sets of at most `b` wheels of `P`. -/
def small_sets (P : Finset ℕ) (b : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun D => D.card ≤ b)

/-- The positions of `S` whose values no wheel of any range divides. -/
def sifted_positions (I : Finset ℕ) (P : ℕ → Finset ℕ) (S : Finset ℕ) (val : ℕ → ℕ) :
    Finset ℕ :=
  S.filter (fun n => ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ val n)

/-- The multiple count of a choice `c` of one set of wheels from each range:
the positions of `S` whose values every chosen wheel divides. -/
def choice_count (I : Finset ℕ) (S : Finset ℕ) (val : ℕ → ℕ)
    (c : (i : ℕ) → i ∈ I → Finset ℕ) : ℕ :=
  (S.filter (fun n => ∀ x ∈ I.attach, ∀ q ∈ c x.1 x.2, q ∣ val n)).card

/-- The remainder of a choice: its multiple count minus `X` times the product
of the shares of the chosen wheels. -/
noncomputable def choice_remainder (I : Finset ℕ) (S : Finset ℕ) (val : ℕ → ℕ) (X : ℝ)
    (g : ℕ → ℝ) (c : (i : ℕ) → i ∈ I → Finset ℕ) : ℝ :=
  (choice_count I S val c : ℝ) - X * ∏ x ∈ I.attach, ∏ q ∈ c x.1 x.2, g q

/-- **The Brun–Hooley bound** (Ford, Theorem 2.3, before the exponential
step). For prime wheels in ranges, even stopping points, `X ≥ 0` and shares
between 0 and 1: the sifted positions are at most `X` times the product over
the ranges of (the product of one minus the shares, plus the total share to
the power `b i + 1` over `(b i + 1)!`), plus the absolute remainders of the
choices of at most `b i` wheels from each range. -/
def brun_hooley_bound : Prop :=
  ∀ (I : Finset ℕ) (P : ℕ → Finset ℕ) (b : ℕ → ℕ) (S : Finset ℕ) (val : ℕ → ℕ) (X : ℝ)
    (g : ℕ → ℝ),
    (∀ i ∈ I, Even (b i)) → (∀ i ∈ I, ∀ q ∈ P i, q.Prime) → 0 ≤ X →
    (∀ i ∈ I, ∀ q ∈ P i, 0 ≤ g q ∧ g q ≤ 1) →
    ((sifted_positions I P S val).card : ℝ) ≤
      X * ∏ i ∈ I, (∏ q ∈ P i, (1 - g q) +
        (∑ q ∈ P i, g q) ^ (b i + 1) / ((b i + 1).factorial : ℝ)) +
      ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)), |choice_remainder I S val X g c|

end RNS.BrunHooley

/-! ## The exponential form (Ford, Theorem 2.3) -/

namespace RNS.BrunHooley

/-- **Each range's error as a factor.** For positive `V i` and nonnegative
`E i`, the product of `V i + E i` is at most the product of the `V i` times e
to the sum of `E i / V i`. -/
def product_exp_bound : Prop :=
  ∀ (I : Finset ℕ) (V E : ℕ → ℝ), (∀ i ∈ I, 0 < V i) → (∀ i ∈ I, 0 ≤ E i) →
    ∏ i ∈ I, (V i + E i) ≤ (∏ i ∈ I, V i) * Real.exp (∑ i ∈ I, E i / V i)

/-- **The Brun–Hooley bound, exponential form** (Ford, Theorem 2.3). With the
shares also below 1: the sifted positions are at most `X` times the product
over the ranges of the products of one minus the shares, times e to the sum
over the ranges of (total share to the power `b i + 1` over `(b i + 1)!`)
divided by the range's product, plus the absolute remainders. -/
def brun_hooley_bound_exp : Prop :=
  ∀ (I : Finset ℕ) (P : ℕ → Finset ℕ) (b : ℕ → ℕ) (S : Finset ℕ) (val : ℕ → ℕ) (X : ℝ)
    (g : ℕ → ℝ),
    (∀ i ∈ I, Even (b i)) → (∀ i ∈ I, ∀ q ∈ P i, q.Prime) → 0 ≤ X →
    (∀ i ∈ I, ∀ q ∈ P i, 0 ≤ g q ∧ g q ≤ 1) → (∀ i ∈ I, ∀ q ∈ P i, g q < 1) →
    ((sifted_positions I P S val).card : ℝ) ≤
      X * (∏ i ∈ I, ∏ q ∈ P i, (1 - g q)) *
        Real.exp (∑ i ∈ I, ((∑ q ∈ P i, g q) ^ (b i + 1) / ((b i + 1).factorial : ℝ)) /
          ∏ q ∈ P i, (1 - g q)) +
      ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)), |choice_remainder I S val X g c|

end RNS.BrunHooley

/-! ## Bounded ranges give a bounded factor (the general step of Ford, Theorem 2.4) -/

namespace RNS.BrunHooley

/-- **Bounded ranges.** If the stopping points are distinct even numbers, each
range's total share is at most `L` (with `L ≥ 0`), each range's product of
one minus the shares is at least `v > 0`, and the shares are below 1, then the
sifted positions are at most `X` times the product over all the ranges, times
e to the power `e ^ L / v`, plus the absolute remainders. The factor depends
only on `L` and `v`, not on the number of ranges. -/
def brun_hooley_order : Prop :=
  ∀ (I : Finset ℕ) (P : ℕ → Finset ℕ) (b : ℕ → ℕ) (S : Finset ℕ) (val : ℕ → ℕ) (X : ℝ)
    (g : ℕ → ℝ) (L v : ℝ),
    (∀ i ∈ I, Even (b i)) → Set.InjOn b I → (∀ i ∈ I, ∀ q ∈ P i, q.Prime) → 0 ≤ X →
    (∀ i ∈ I, ∀ q ∈ P i, 0 ≤ g q ∧ g q < 1) → 0 ≤ L → (∀ i ∈ I, ∑ q ∈ P i, g q ≤ L) →
    0 < v → (∀ i ∈ I, v ≤ ∏ q ∈ P i, (1 - g q)) →
    ((sifted_positions I P S val).card : ℝ) ≤
      X * (∏ i ∈ I, ∏ q ∈ P i, (1 - g q)) * Real.exp (Real.exp L / v) +
      ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)), |choice_remainder I S val X g c|

/-- **The size of a choice.** If every wheel of range `i` is at most `y i`
(each `y i ≥ 1`), the product of the wheels of any choice of at most `b i`
wheels from each range is at most the product of `y i ^ b i`: this is how
the remainders are kept to moduli up to a set level. -/
def choice_product_le : Prop :=
  ∀ (I : Finset ℕ) (P : ℕ → Finset ℕ) (b y : ℕ → ℕ), (∀ i ∈ I, 1 ≤ y i) →
    (∀ i ∈ I, ∀ q ∈ P i, q ≤ y i) →
    ∀ c ∈ I.pi (fun i => small_sets (P i) (b i)),
      ∏ x ∈ I.attach, ∏ q ∈ c x.1 x.2, q ≤ ∏ i ∈ I, y i ^ b i

end RNS.BrunHooley
