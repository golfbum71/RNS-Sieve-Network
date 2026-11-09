/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset

/-!
# SieveDataLimits — what the multiple counts alone can decide

A sieve sees a set of numbers only through its multiple counts: how many of
the numbers each set of wheels divides. This node shows what that data can
and cannot decide about the survivor count.

* **The worked case.** If 100 numbers have 60 even and 10 divisible by 3, the
  numbers surviving both wheels are between 30 and 40, and both ends occur:
  the data leaves an interval, not a value.
* **Every sieve is a bound.** Give each known multiple count a weight. If, for
  every set of wheels a number could be divisible by, the weights of the known
  sets inside it add up to at least 1 when that set is empty and at least 0
  otherwise (an upper sieve), the weighted multiple counts bound the survivors
  from above; with "at most" in place of "at least" (a lower sieve), from
  below. This is the weak half of the duality in Tao's Theorem 5: every upper
  or lower sieve gives a valid bound, whatever the set. The strong half (the
  best sieve reaches the best bound) is linear-programming duality and is not
  proved here.

The wheels need not be primes: divisibility by each wheel is all that is used.

Proof: `RNSSolutions/SieveDataLimits.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.SieveDataLimits

/-- The members of `A` that survive the wheels 2 and 3. -/
def survive_two_three (A : Finset Nat) : Finset Nat :=
  A.filter (fun a => ¬ 2 ∣ a ∧ ¬ 3 ∣ a)

/-- **The worked case: the data pins the survivors to an interval.** If `A`
has 100 members, 60 of them even and 10 divisible by 3, between 30 and 40 of
them survive the wheels 2 and 3. -/
def two_three_bounds : Prop :=
  ∀ A : Finset Nat, A.card = 100 → (A.filter (fun a => 2 ∣ a)).card = 60 →
    (A.filter (fun a => 3 ∣ a)).card = 10 →
    30 ≤ (survive_two_three A).card ∧ (survive_two_three A).card ≤ 40

/-- **Both ends occur.** There are sets with that data and exactly 30
survivors, and sets with that data and exactly 40. -/
def two_three_ends : Prop :=
  (∃ A : Finset Nat, A.card = 100 ∧ (A.filter (fun a => 2 ∣ a)).card = 60 ∧
      (A.filter (fun a => 3 ∣ a)).card = 10 ∧ (survive_two_three A).card = 30) ∧
    (∃ A : Finset Nat, A.card = 100 ∧ (A.filter (fun a => 2 ∣ a)).card = 60 ∧
      (A.filter (fun a => 3 ∣ a)).card = 10 ∧ (survive_two_three A).card = 40)

/-- The multiple count of the set of wheels `D`: the members of `A` that every
wheel of `D` divides. -/
def multiple_count (A D : Finset Nat) : Nat :=
  (A.filter (fun a => ∀ q ∈ D, q ∣ a)).card

/-- The members of `A` that no wheel of `W` divides. -/
def survivors_in (W A : Finset Nat) : Finset Nat :=
  A.filter (fun a => ∀ q ∈ W, ¬ q ∣ a)

/-- **Every upper sieve bounds the survivors from above.** The known data are
the multiple counts of the sets of wheels in `Ds` (each inside `W`), with
weights `wt`. If, for every set `S` of wheels in `W`, the weights of the known
sets inside `S` add up to at least 1 when `S` is empty and at least 0
otherwise, then the survivors of `W` in `A` are at most the weighted sum of
the known multiple counts. -/
def upper_sieve_bound : Prop :=
  ∀ (W A : Finset Nat) (Ds : Finset (Finset Nat)) (wt : Finset Nat → ℝ),
    (∀ D ∈ Ds, D ⊆ W) →
    (∀ S ⊆ W, (if S = ∅ then (1 : ℝ) else 0) ≤ ∑ D ∈ Ds.filter (fun D => D ⊆ S), wt D) →
    ((survivors_in W A).card : ℝ) ≤ ∑ D ∈ Ds, wt D * (multiple_count A D : ℝ)

/-- **Every lower sieve bounds the survivors from below.** The same with "at
most" in place of "at least". -/
def lower_sieve_bound : Prop :=
  ∀ (W A : Finset Nat) (Ds : Finset (Finset Nat)) (wt : Finset Nat → ℝ),
    (∀ D ∈ Ds, D ⊆ W) →
    (∀ S ⊆ W, ∑ D ∈ Ds.filter (fun D => D ⊆ S), wt D ≤ (if S = ∅ then (1 : ℝ) else 0)) →
    ∑ D ∈ Ds, wt D * (multiple_count A D : ℝ) ≤ ((survivors_in W A).card : ℝ)

end RNS.SieveDataLimits
