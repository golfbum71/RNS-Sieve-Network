/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SieveDataLimits.Conclusions
import Mathlib

/-!
# Proofs for SieveDataLimits

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. The worked case: the even numbers and the multiples of 3 together
number 60 + 10 minus those in both, and at most 10 are in both, so between 60
and 70 numbers are hit and between 30 and 40 survive. Two explicit sets of
100 numbers below 600 reach the two ends (checked by the kernel).

The sieve bounds: write each weighted multiple count as a sum over the
members of `A`. For a member, the known sets of wheels dividing it are the
known sets inside the set of wheels that divide it. Swapping the two sums,
each member contributes the sum of the weights of the known sets inside its
set of dividing wheels, which the sieve condition compares with 1 for a
survivor (no wheel divides it) and 0 for the rest.
-/

namespace RNS.SieveDataLimits

theorem two_three_bounds_holds : two_three_bounds := by
  intro A hA hE hT
  have h1 := Finset.card_union_add_card_inter (A.filter (fun a => 2 ∣ a))
    (A.filter (fun a => 3 ∣ a))
  have h2 : (A.filter (fun a => 2 ∣ a) ∩ A.filter (fun a => 3 ∣ a)).card ≤ 10 := by
    rw [← hT]
    exact Finset.card_le_card Finset.inter_subset_right
  have h3 : (A.filter (fun a => 2 ∣ a ∨ 3 ∣ a)).card +
      (A.filter (fun a => ¬ (2 ∣ a ∨ 3 ∣ a))).card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have h5 : A.filter (fun a => 2 ∣ a ∨ 3 ∣ a) =
      A.filter (fun a => 2 ∣ a) ∪ A.filter (fun a => 3 ∣ a) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [h5] at h3
  have h4 : A.filter (fun a => ¬ (2 ∣ a ∨ 3 ∣ a)) = survive_two_three A :=
    Finset.filter_congr (fun a _ => not_or)
  rw [h4] at h3
  omega

theorem two_three_ends_holds : two_three_ends := by
  refine ⟨⟨(Finset.range 600).filter (fun n => (n % 6 = 2 ∧ n < 300) ∨ (n % 6 = 4 ∧ n < 60) ∨
      (n % 6 = 3 ∧ n < 60) ∨ (n % 6 = 1 ∧ n < 180)), ?_⟩,
    ⟨(Finset.range 600).filter (fun n => (n % 6 = 0 ∧ 0 < n ∧ n ≤ 60) ∨ (n % 6 = 2 ∧ n < 300) ∨
      (n % 6 = 1 ∧ n < 240)), ?_⟩⟩
  · unfold survive_two_three
    decide +kernel
  · unfold survive_two_three
    decide +kernel

/-- A weighted multiple count as a sum over the members of `A`. -/
private theorem expand (W A D : Finset Nat) (hD : D ⊆ W) (c : ℝ) :
    c * (multiple_count A D : ℝ) =
      ∑ a ∈ A, if D ⊆ W.filter (fun q => q ∣ a) then c else 0 := by
  have hset : A.filter (fun a => ∀ q ∈ D, q ∣ a) =
      A.filter (fun a => D ⊆ W.filter (fun q => q ∣ a)) := by
    apply Finset.filter_congr
    intro a _
    constructor
    · intro h q hq
      exact Finset.mem_filter.mpr ⟨hD hq, h q hq⟩
    · intro h q hq
      exact (Finset.mem_filter.mp (h hq)).2
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, multiple_count, hset, mul_comm]

/-- A member survives exactly when the set of wheels dividing it is empty. -/
private theorem indicator_eq (W : Finset Nat) (a : Nat) :
    (if (∀ q ∈ W, ¬ q ∣ a) then (1 : ℝ) else 0) =
      if W.filter (fun q => q ∣ a) = ∅ then 1 else 0 := by
  have h : (∀ q ∈ W, ¬ q ∣ a) ↔ W.filter (fun q => q ∣ a) = ∅ :=
    ⟨fun h => Finset.filter_eq_empty_iff.mpr (fun x hx => h x hx),
     fun h x hx => Finset.filter_eq_empty_iff.mp h hx⟩
  by_cases hs : ∀ q ∈ W, ¬ q ∣ a
  · rw [if_pos hs, if_pos (h.mp hs)]
  · rw [if_neg hs, if_neg (fun h' => hs (h.mpr h'))]

/-- Both sides of the sieve bounds as sums over the members of `A`. -/
private theorem swap (W A : Finset Nat) (Ds : Finset (Finset Nat)) (wt : Finset Nat → ℝ)
    (hsub : ∀ D ∈ Ds, D ⊆ W) :
    ∑ D ∈ Ds, wt D * (multiple_count A D : ℝ) =
      ∑ a ∈ A, ∑ D ∈ Ds.filter (fun D => D ⊆ W.filter (fun q => q ∣ a)), wt D := by
  have h : ∑ D ∈ Ds, wt D * (multiple_count A D : ℝ) =
      ∑ D ∈ Ds, ∑ a ∈ A, if D ⊆ W.filter (fun q => q ∣ a) then wt D else 0 :=
    Finset.sum_congr rfl (fun D hD => expand W A D (hsub D hD) (wt D))
  rw [h, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_filter]

private theorem card_eq (W A : Finset Nat) :
    ((survivors_in W A).card : ℝ) =
      ∑ a ∈ A, if W.filter (fun q => q ∣ a) = ∅ then (1 : ℝ) else 0 := by
  rw [survivors_in, Finset.natCast_card_filter]
  exact Finset.sum_congr rfl (fun a _ => indicator_eq W a)

theorem upper_sieve_bound_holds : upper_sieve_bound := by
  intro W A Ds wt hsub hwt
  rw [swap W A Ds wt hsub, card_eq]
  exact Finset.sum_le_sum (fun a _ => hwt _ (Finset.filter_subset _ _))

theorem lower_sieve_bound_holds : lower_sieve_bound := by
  intro W A Ds wt hsub hwt
  rw [swap W A Ds wt hsub, card_eq]
  exact Finset.sum_le_sum (fun a _ => hwt _ (Finset.filter_subset _ _))

#print axioms RNS.SieveDataLimits.two_three_bounds_holds
#print axioms RNS.SieveDataLimits.two_three_ends_holds
#print axioms RNS.SieveDataLimits.upper_sieve_bound_holds
#print axioms RNS.SieveDataLimits.lower_sieve_bound_holds

end RNS.SieveDataLimits
