/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunTruncation.Conclusions
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset -- `Finset.sum_powerset_insert`
import Mathlib.Algebra.BigOperators.Ring.Finset            -- `Finset.mul_sum`
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset -- `Finset.prod_le_one₀`
import Mathlib.Algebra.Order.BigOperators.Ring.Finset      -- `Finset.prod_nonneg`
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Proofs for BrunTruncation

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. Add one wheel at a time. Adding a wheel with share `a` multiplies the
product by one minus `a`. In the stopped sum, the sets that leave the new
wheel out give the old stopped sum, and the sets that use it give minus `a`
times the old sum stopped one step earlier. So the signed error for the
bigger set of wheels is the old signed error plus `a` times the old signed
error one step earlier. Both are at least zero, which gives the lower bound;
each is at most its sum over sets of one more wheel, and those two sums add
up to the new one, which gives the upper bound.

For the power bound: adding a wheel with share `a` to wheels with total `S`,
the sets of `k + 1` wheels give the old ones plus `a` times the old sets of
`k` wheels. The binomial expansion of the new total to the power `k + 1`
starts with `S` to that power plus `k + 1` times `a` times `S` to the `k`,
which covers both.
-/

namespace RNS.BrunTruncation

open Finset

/-! ### Adding one wheel -/

theorem trunc_prod_ite (W : Finset ℕ) (x : ℕ → ℝ) (t : ℕ) :
    trunc_prod W x t =
      ∑ D ∈ W.powerset, if D.card ≤ t then (-1 : ℝ) ^ D.card * ∏ p ∈ D, x p else 0 := by
  unfold trunc_prod
  rw [Finset.sum_filter]

theorem esymm_ite (W : Finset ℕ) (x : ℕ → ℝ) (k : ℕ) :
    esymm_k W x k = ∑ D ∈ W.powerset, if D.card = k then ∏ p ∈ D, x p else 0 := by
  unfold esymm_k
  rw [Finset.sum_filter]

theorem filter_card_zero (W : Finset ℕ) :
    W.powerset.filter (fun D => D.card = 0) = {∅} := by
  ext D
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton, Finset.card_eq_zero]
  constructor
  · exact fun h => h.2
  · rintro rfl
    exact ⟨Finset.empty_subset _, rfl⟩

theorem trunc_prod_zero (W : Finset ℕ) (x : ℕ → ℝ) : trunc_prod W x 0 = 1 := by
  unfold trunc_prod
  have h : W.powerset.filter (fun D => D.card ≤ 0) = W.powerset.filter (fun D => D.card = 0) :=
    Finset.filter_congr (fun D _ => Nat.le_zero)
  rw [h, filter_card_zero, Finset.sum_singleton]
  simp

theorem esymm_zero (W : Finset ℕ) (x : ℕ → ℝ) : esymm_k W x 0 = 1 := by
  unfold esymm_k
  rw [filter_card_zero, Finset.sum_singleton]
  simp

theorem trunc_prod_insert (s : Finset ℕ) (a : ℕ) (ha : a ∉ s) (x : ℕ → ℝ) (t : ℕ) :
    trunc_prod (insert a s) x (t + 1) = trunc_prod s x (t + 1) - x a * trunc_prod s x t := by
  rw [trunc_prod_ite, trunc_prod_ite, trunc_prod_ite, Finset.sum_powerset_insert ha,
    Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  have haD : a ∉ D := fun h => ha (Finset.mem_powerset.mp hD h)
  rw [Finset.card_insert_of_notMem haD, Finset.prod_insert haD]
  by_cases h : D.card ≤ t
  · rw [if_pos (show D.card + 1 ≤ t + 1 by omega), if_pos h]
    ring
  · rw [if_neg (show ¬ (D.card + 1 ≤ t + 1) by omega), if_neg h]
    ring

theorem esymm_insert (s : Finset ℕ) (a : ℕ) (ha : a ∉ s) (x : ℕ → ℝ) (k : ℕ) :
    esymm_k (insert a s) x (k + 1) = esymm_k s x (k + 1) + x a * esymm_k s x k := by
  rw [esymm_ite, esymm_ite, esymm_ite, Finset.sum_powerset_insert ha, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  have haD : a ∉ D := fun h => ha (Finset.mem_powerset.mp hD h)
  rw [Finset.card_insert_of_notMem haD, Finset.prod_insert haD]
  by_cases h : D.card = k
  · rw [if_pos (show D.card + 1 = k + 1 by omega), if_pos h]
  · rw [if_neg (show ¬ (D.card + 1 = k + 1) by omega), if_neg h]
    ring

theorem trunc_prod_empty (x : ℕ → ℝ) (t : ℕ) : trunc_prod ∅ x t = 1 := by
  rw [trunc_prod_ite, Finset.powerset_empty, Finset.sum_singleton]
  simp

theorem esymm_empty_succ (x : ℕ → ℝ) (k : ℕ) : esymm_k ∅ x (k + 1) = 0 := by
  rw [esymm_ite, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty,
    if_neg (show ¬ (0 = k + 1) by omega)]

/-! ### Stopping early -/

theorem truncation_error_holds : truncation_error := by
  intro W x
  induction W using Finset.induction_on with
  | empty =>
    intro t _
    rw [trunc_prod_empty, Finset.prod_empty, sub_self, mul_zero, esymm_empty_succ]
    exact ⟨le_refl 0, le_refl 0⟩
  | insert a s ha ih =>
    intro t hx
    have hxs : ∀ p ∈ s, 0 ≤ x p ∧ x p ≤ 1 := fun p hp => hx p (Finset.mem_insert_of_mem hp)
    have hxa0 : 0 ≤ x a := (hx a (Finset.mem_insert_self a s)).1
    have hxa1 : x a ≤ 1 := (hx a (Finset.mem_insert_self a s)).2
    have hP0 : 0 ≤ ∏ p ∈ s, (1 - x p) :=
      Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hxs p hp).2)
    have hP1 : ∏ p ∈ s, (1 - x p) ≤ 1 :=
      Finset.prod_le_one₀ (fun p hp => sub_nonneg.mpr (hxs p hp).2)
        (fun p hp => by linarith [(hxs p hp).1])
    rw [Finset.prod_insert ha]
    cases t with
    | zero =>
      rw [trunc_prod_zero, pow_zero, one_mul, esymm_insert s a ha x 0, esymm_zero]
      obtain ⟨h1, h2⟩ := ih 0 hxs
      rw [trunc_prod_zero, pow_zero, one_mul] at h1 h2
      constructor
      · nlinarith [mul_nonneg hxa0 hP0]
      · nlinarith [mul_nonneg hxa0 (sub_nonneg.mpr hP1)]
    | succ t =>
      rw [trunc_prod_insert s a ha x t, esymm_insert s a ha x (t + 1)]
      obtain ⟨h1, h2⟩ := ih (t + 1) hxs
      obtain ⟨h3, h4⟩ := ih t hxs
      have key : (-1 : ℝ) ^ (t + 1) * (trunc_prod s x (t + 1) - x a * trunc_prod s x t
            - (1 - x a) * ∏ p ∈ s, (1 - x p))
          = (-1 : ℝ) ^ (t + 1) * (trunc_prod s x (t + 1) - ∏ p ∈ s, (1 - x p))
            + x a * ((-1 : ℝ) ^ t * (trunc_prod s x t - ∏ p ∈ s, (1 - x p))) := by
        ring
      rw [key]
      constructor
      · nlinarith [mul_nonneg hxa0 h3]
      · nlinarith [mul_le_mul_of_nonneg_left h4 hxa0]

/-! ### The power bound -/

/-- The first two terms of the binomial expansion. -/
theorem pow_add_ge (S y : ℝ) (hS : 0 ≤ S) (hy : 0 ≤ y) (k : ℕ) :
    S ^ (k + 1) + ((k : ℝ) + 1) * y * S ^ k ≤ (S + y) ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hSk : 0 ≤ S ^ k := pow_nonneg hS k
    have h := mul_le_mul_of_nonneg_right ih (add_nonneg hS hy)
    have e1 : S ^ (k + 1 + 1) = S ^ k * S * S := by ring
    have e2 : S ^ (k + 1) = S ^ k * S := by ring
    have e3 : (S + y) ^ (k + 1 + 1) = (S + y) ^ (k + 1) * (S + y) := by ring
    rw [e1, e2, e3]
    rw [e2] at h
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    nlinarith [mul_nonneg hk (mul_nonneg (mul_nonneg hy hy) hSk)]

theorem esymm_power_bound_holds : esymm_power_bound := by
  intro W x
  induction W using Finset.induction_on with
  | empty =>
    intro k _
    cases k with
    | zero => rw [esymm_zero]; simp
    | succ k => rw [esymm_empty_succ]; simp
  | insert a s ha ih =>
    intro k hx
    have hxs : ∀ p ∈ s, 0 ≤ x p := fun p hp => hx p (Finset.mem_insert_of_mem hp)
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have hS : 0 ≤ ∑ p ∈ s, x p := Finset.sum_nonneg hxs
    cases k with
    | zero => rw [esymm_zero]; simp
    | succ k =>
      rw [esymm_insert s a ha x k, Finset.sum_insert ha]
      have ih1 := ih (k + 1) hxs
      have ih2 := ih k hxs
      have hF : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
      have hF1 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hF2 : (0 : ℝ) < ((k : ℝ) + 1) * (k.factorial : ℝ) := by positivity
      rw [hF1] at ih1 ⊢
      rw [le_div_iff₀ hF2]
      have ih1' := (le_div_iff₀ hF2).mp ih1
      have ih2' := (le_div_iff₀ hF).mp ih2
      have hpow := pow_add_ge (∑ p ∈ s, x p) (x a) hS hxa k
      have hk : (0 : ℝ) ≤ ((k : ℝ) + 1) * x a := by positivity
      have h3 := mul_le_mul_of_nonneg_left ih2' hk
      have e : x a + ∑ p ∈ s, x p = ∑ p ∈ s, x p + x a := add_comm _ _
      rw [e]
      nlinarith [h3, ih1', hpow]

end RNS.BrunTruncation

#print axioms RNS.BrunTruncation.truncation_error_holds
#print axioms RNS.BrunTruncation.esymm_power_bound_holds
