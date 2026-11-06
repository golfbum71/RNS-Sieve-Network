/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.TuranCycle.Conclusions
import Mathlib.Data.Nat.Factorization.Basic          -- `Nat.Ioc_filter_dvd_card_eq_div`
import Mathlib.Algebra.Order.BigOperators.Ring.Finset -- `Finset.sum_le_sum_of_subset_of_nonneg`
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma -- `Finset.sum_comm`
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Proofs for TuranCycle

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. Write each hit count as a sum, over the wheels, of 1 or 0; swap the
order of summation; then each wheel contributes its number of multiples among
the positions (`Nat.Ioc_filter_dvd_card_eq_div`). Squaring gives a double sum
over pairs of wheels, and a position is a multiple of both exactly when it is a
multiple of their least common multiple. For Turán's inequality, expand the
total of (size of `s` times `f` minus the total of `f`) squared; it equals the
right-hand side, and the points where `f` is zero alone contribute the left.
-/

namespace RNS.TuranCycle

theorem hits_sum_holds : hits_sum := by
  intro W N
  unfold hits
  simp only [Finset.card_filter]
  rw [Finset.sum_comm (s := Finset.Ioc 0 N)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.card_filter, Nat.Ioc_filter_dvd_card_eq_div]

theorem hits_sq_sum_holds : hits_sq_sum := by
  intro W N
  have key : ∀ m, (hits W m) ^ 2 =
      ∑ q ∈ W, ∑ r ∈ W, if Nat.lcm q r ∣ m then 1 else 0 := by
    intro m
    unfold hits
    rw [Finset.card_filter, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
    by_cases hq : q ∣ m <;> by_cases hr : r ∣ m <;> simp [hq, hr, Nat.lcm_dvd_iff]
  simp only [key]
  rw [Finset.sum_comm (s := Finset.Ioc 0 N)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm (s := Finset.Ioc 0 N)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.card_filter, Nat.Ioc_filter_dvd_card_eq_div]

theorem turan_inequality_holds : turan_inequality := by
  intro s f
  have hpt : ∀ m ∈ s, ((s.card : ℤ) * (f m : ℤ) - ∑ k ∈ s, (f k : ℤ)) ^ 2 =
      (s.card : ℤ) ^ 2 * (f m : ℤ) ^ 2 - 2 * (s.card : ℤ) * (∑ k ∈ s, (f k : ℤ)) * (f m : ℤ)
        + (∑ k ∈ s, (f k : ℤ)) ^ 2 := fun m _ => by ring
  have hexp : ∑ m ∈ s, ((s.card : ℤ) * (f m : ℤ) - ∑ k ∈ s, (f k : ℤ)) ^ 2 =
      (s.card : ℤ) * ((s.card : ℤ) * (∑ m ∈ s, (f m : ℤ) ^ 2) - (∑ m ∈ s, (f m : ℤ)) ^ 2) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  have hle : ∑ m ∈ s.filter (fun m => f m = 0),
        ((s.card : ℤ) * (f m : ℤ) - ∑ k ∈ s, (f k : ℤ)) ^ 2
      ≤ ∑ m ∈ s, ((s.card : ℤ) * (f m : ℤ) - ∑ k ∈ s, (f k : ℤ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).1)
      (fun _ _ _ => sq_nonneg _)
  have hzero : ∀ m ∈ s.filter (fun m => f m = 0),
      ((s.card : ℤ) * (f m : ℤ) - ∑ k ∈ s, (f k : ℤ)) ^ 2 = (∑ k ∈ s, (f k : ℤ)) ^ 2 := by
    intro m hm
    rw [(Finset.mem_filter.mp hm).2, Nat.cast_zero, mul_zero, zero_sub, neg_sq]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const, nsmul_eq_mul, hexp] at hle
  exact hle

theorem turan_wheels_holds : turan_wheels := by
  intro W N
  have h := turan_inequality_holds (Finset.Ioc 0 N) (hits W)
  have hS : (Finset.Ioc 0 N).filter (fun m => hits W m = 0) = survivors_upto W N := by
    ext m
    simp only [survivors_upto, hits, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, by intro q hq; exact h3 hq⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, by intro q hq; exact h3 q hq⟩
  have h1 : (∑ m ∈ Finset.Ioc 0 N, (hits W m : ℤ)) = ∑ q ∈ W, ((N / q : Nat) : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, hits_sum_holds W N]
  have h2 : (∑ m ∈ Finset.Ioc 0 N, (hits W m : ℤ) ^ 2) =
      ∑ q ∈ W, ∑ r ∈ W, ((N / Nat.lcm q r : Nat) : ℤ) := by
    have := hits_sq_sum_holds W N
    have e1 : (∑ m ∈ Finset.Ioc 0 N, (hits W m : ℤ) ^ 2) =
        ((∑ m ∈ Finset.Ioc 0 N, (hits W m) ^ 2 : Nat) : ℤ) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun m _ => (Nat.cast_pow _ _).symm
    have e2 : (∑ q ∈ W, ∑ r ∈ W, ((N / Nat.lcm q r : Nat) : ℤ)) =
        ((∑ q ∈ W, ∑ r ∈ W, N / Nat.lcm q r : Nat) : ℤ) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun q _ => (Nat.cast_sum _ _).symm
    rw [e1, e2, this]
  rw [hS, h1, h2, Nat.card_Ioc, Nat.sub_zero] at h
  exact h

end RNS.TuranCycle

#print axioms RNS.TuranCycle.hits_sum_holds
#print axioms RNS.TuranCycle.hits_sq_sum_holds
#print axioms RNS.TuranCycle.turan_inequality_holds
#print axioms RNS.TuranCycle.turan_wheels_holds
