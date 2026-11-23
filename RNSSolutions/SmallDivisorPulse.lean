/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SmallDivisorPulse.Conclusions
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Proofs for SmallDivisorPulse

Draft (2026-11-23).

At the time `1 / j`, a speed not divisible by `j` leaves a remainder from 1 to
`j - 1`, so the runner is at least one `j`-th of a lap from the start both ways,
and one `j`-th is at least one over the number of runners. For the product:
each small number either divides some speed, hence the product, or gives a
lonely time by the first claim.
-/

namespace RNS.SmallDivisorPulse

open RNS.PileUpLock

theorem small_divisor_time_works_holds : small_divisor_time_works := by
  intro S j hj2 hjc hnd
  refine ⟨by omega, fun v hv => ?_⟩
  have hj : (0 : ℤ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjc' : (j : ℤ) ≤ (S.card : ℤ) + 1 := by exact_mod_cast hjc
  have hr0 : 0 ≤ v % (j : ℤ) := Int.emod_nonneg v (ne_of_gt hj)
  have hr1 : v % (j : ℤ) < j := Int.emod_lt_of_pos v hj
  have hrne : v % (j : ℤ) ≠ 0 := fun h => hnd v hv (Int.dvd_of_emod_eq_zero h)
  have hr2 : 1 ≤ v % (j : ℤ) := by omega
  have hr3 : 1 ≤ (j : ℤ) - v % (j : ℤ) := by omega
  unfold far
  rw [mul_one]
  push_cast
  constructor <;> nlinarith

theorem counterexample_lcm_dvd_product_step (h : small_divisor_time_works) :
    counterexample_lcm_dvd_product := by
  intro S hS
  apply Finset.lcm_dvd
  intro j hj
  rw [Finset.mem_Icc] at hj
  by_cases hex : ∃ v ∈ S, (j : ℤ) ∣ v
  · obtain ⟨v, hv, hjv⟩ := hex
    exact dvd_trans hjv (Finset.dvd_prod_of_mem (fun w : ℤ => w) hv)
  · exfalso
    have hnd : ∀ v ∈ S, ¬ (j : ℤ) ∣ v := fun v hv h' => hex ⟨v, hv, h'⟩
    exact hS ⟨j, 1, h S j hj.1 hj.2 hnd⟩

theorem counterexample_lcm_dvd_product_holds : counterexample_lcm_dvd_product :=
  counterexample_lcm_dvd_product_step small_divisor_time_works_holds

end RNS.SmallDivisorPulse

#print axioms RNS.SmallDivisorPulse.small_divisor_time_works_holds
#print axioms RNS.SmallDivisorPulse.counterexample_lcm_dvd_product_holds
