/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunHooley.Conclusions
import Mathlib

/-!
# Proofs for BrunHooley

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. The expansion is distributivity: a product of sums is the sum over one
choice from each factor of the product of the choices (`Finset.prod_sum`).
For the upper-sieve property: each range's sieve sum is at least its
indicator (1 if no wheel of the range divides the number, 0 otherwise), and
these indicators are at least 0, so the product of the sieve sums is at least
the product of the indicators, which is 1 exactly when no wheel of any range
divides the number, and at least 0 otherwise.
-/

namespace RNS.BrunHooley

theorem combined_eq_product_holds : combined_eq_product := by
  intro I P wt n
  unfold combined_sieve_sum sieve_sum
  exact (Finset.prod_sum I (fun i => (P i).powerset)
    (fun i D => if (∀ q ∈ D, q ∣ n) then wt i D else 0)).symm

theorem product_upper_sieve_holds : product_upper_sieve := by
  intro I P wt hup n
  rw [combined_eq_product_holds]
  have hind : ∀ i ∈ I, (0 : ℝ) ≤ if ∀ q ∈ P i, ¬ q ∣ n then (1 : ℝ) else 0 := by
    intro i _
    split_ifs <;> norm_num
  calc (if ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ n then (1 : ℝ) else 0)
      ≤ ∏ i ∈ I, (if ∀ q ∈ P i, ¬ q ∣ n then (1 : ℝ) else 0) := by
        by_cases h : ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ n
        · rw [if_pos h]
          exact le_of_eq (Finset.prod_eq_one (fun i hi => if_pos (h i hi))).symm
        · rw [if_neg h]
          exact Finset.prod_nonneg hind
    _ ≤ ∏ i ∈ I, sieve_sum (P i) (wt i) n :=
        Finset.prod_le_prod₀ hind (fun i hi => hup i hi n)

#print axioms RNS.BrunHooley.combined_eq_product_holds
#print axioms RNS.BrunHooley.product_upper_sieve_holds

end RNS.BrunHooley
