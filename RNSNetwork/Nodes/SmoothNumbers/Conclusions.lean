/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# SmoothNumbers — numbers built only from the wheels

The survivors of a set of wheels are the numbers no wheel divides; the smooth
numbers are the opposite: the numbers every one of whose prime factors is a
wheel. Three finite facts about them.

* **Rankin's bound.** The smooth numbers up to `x` are at most `x` to a power
  `α` times the product, over the wheels, of one over one minus the wheel to
  the minus `α`, for every positive `α`. At `α = 1` the product is the
  reciprocal of the survivor share of the wheels.
* **A lower bound.** If every wheel is at most `y` and `y` to the `u` is at
  most `x`, every product of at most `u` distinct wheels is a smooth number up
  to `x`, and distinct sets of wheels give distinct products, so there are at
  least as many smooth numbers as sets of at most `u` wheels.
* **The Buchstab-type recurrence.** Bringing in one more wheel adds exactly the
  numbers it divides, and those, divided by it, are the smooth numbers for the
  enlarged set of wheels up to `x` divided by the new wheel.

Proof: `RNSSolutions/SmoothNumbers.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.SmoothNumbers

/-- The numbers from 1 to `x` all of whose prime factors are in `W`. -/
def smooth_upto (W : Finset Nat) (x : Nat) : Finset Nat :=
  (Finset.Icc 1 x).filter (fun n => n.primeFactors ⊆ W)

/-- **Rankin's bound.** -/
def rankin_upper : Prop :=
  ∀ (W : Finset Nat) (x : Nat) (α : ℝ), (∀ p ∈ W, p.Prime) → 0 < α →
    ((smooth_upto W x).card : ℝ) ≤ (x : ℝ) ^ α * ∏ p ∈ W, (1 - (p : ℝ) ^ (-α))⁻¹

/-- **The lower bound from products of distinct wheels.** If every wheel is at
most `y` (with `y ≥ 1`) and `y ^ u ≤ x`, the smooth numbers up to `x` are at
least the number of sets of at most `u` wheels. -/
def smooth_count_lower : Prop :=
  ∀ (W : Finset Nat) (y u x : Nat), (∀ p ∈ W, p.Prime) → (∀ p ∈ W, p ≤ y) → 1 ≤ y →
    y ^ u ≤ x → ∑ j ∈ Finset.range (u + 1), W.card.choose j ≤ (smooth_upto W x).card

/-- **The Buchstab-type recurrence.** For a prime `p` not in `W`, the smooth
numbers for `W` and `p` up to `x` are the smooth numbers for `W` up to `x`
plus the smooth numbers for `W` and `p` up to `x / p`. -/
def smooth_buchstab : Prop :=
  ∀ (W : Finset Nat) (p x : Nat), p.Prime → p ∉ W →
    (smooth_upto (insert p W) x).card =
      (smooth_upto W x).card + (smooth_upto (insert p W) (x / p)).card

end RNS.SmoothNumbers
