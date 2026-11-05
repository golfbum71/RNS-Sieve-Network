/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RNSNetwork.Nodes.SurvivorCount.Conclusions
import RNSNetwork.Nodes.TwinShare.Conclusions

/-!
# Proofs for TwinShare

Imports claims only, never other nodes' proofs. `twin_share_eq_prod` is
proved as a step from `SurvivorCount`'s `twin_survivor_count` and
`general_survivor_count`, taken as named hypotheses; `twin_share_split` is
proved directly.
-/

namespace RNS.TwinShare

open RNS.SurvivorCount

/-- An active wheel other than 2 is a prime of size at least 3. -/
private theorem three_le_of_mem_erase {limit q : Nat} (hq : q ∈ (active_primes limit).erase 2) :
    q.Prime ∧ 3 ≤ q := by
  have hq2 : q ≠ 2 := Finset.ne_of_mem_erase hq
  have hqp : q.Prime := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2
  have := hqp.two_le
  exact ⟨hqp, by omega⟩

/-- The pattern `{0}` occupies one position on every wheel. -/
private theorem w_zero (q : Nat) : w ({0} : Finset Nat) q = 1 := by
  simp [w]

/-- **The twin share of the cycle**, as a step from the two survivor counts. -/
theorem twin_share_eq_prod_step (htwin : twin_survivor_count) (hgen : general_survivor_count) :
    twin_share_eq_prod := by
  intro limit
  rw [htwin limit, hgen {0} limit]
  simp only [w_zero]
  push_cast
  rw [← Finset.prod_div_distrib]
  refine Eq.trans (Finset.prod_erase (active_primes limit) (a := 2) ?_).symm ?_
  · simp
  · refine Finset.prod_congr rfl (fun q hq => ?_)
    obtain ⟨_, h3⟩ := three_le_of_mem_erase hq
    rw [if_neg (by omega), Nat.cast_sub (by omega : 2 ≤ q), Nat.cast_sub (by omega : 1 ≤ q)]
    push_cast
    ring

/-- **The twin share, split**, proved. -/
theorem twin_share_split_holds : twin_share_split := by
  intro limit
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  obtain ⟨_, h3⟩ := three_le_of_mem_erase hq
  have h3' : (3 : Real) ≤ q := by exact_mod_cast h3
  have h1 : (q : Real) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h0 : (q : Real) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

end RNS.TwinShare

#print axioms RNS.TwinShare.twin_share_split_holds
