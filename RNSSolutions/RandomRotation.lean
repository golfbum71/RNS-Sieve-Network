/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.CRT.Conclusions
import RNSNetwork.Nodes.SurvivorCount.Conclusions
import RNSNetwork.Nodes.RandomRotation.Conclusions
import Mathlib

/-!
# Proofs for RandomRotation

Imports claims only, never other nodes' proofs. Both claims are steps: they
take `CRT.crt_map_bijective` and `SurvivorCount.general_survivor_count` as
named hypotheses, joined in `RNSSolutions/Assemble.lean`.

Idea. A bijection has exactly one preimage for every value. For the share:
the surviving shifts number the product of the wheel size minus `w`
(`general_survivor_count`), the cycle length is the product of the wheel
sizes, and a product of quotients is the quotient of the products. On each
wheel the pattern occupies at most as many positions as the wheel has, so the
subtraction is exact.
-/

namespace RNS.RandomRotation

theorem rotation_is_shift_step (h : RNS.CRT.crt_map_bijective) : rotation_is_shift :=
  fun limit s => (h limit).existsUnique s

/-- A pattern occupies at most `q` positions on the wheel of size `q`. -/
private theorem w_le (T : Finset Nat) {q : Nat} (hq : 0 < q) : w T q ≤ q := by
  unfold w
  calc (T.image (fun t => t % q)).card ≤ (Finset.range q).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (Nat.mod_lt t hq)
    _ = q := Finset.card_range q

theorem random_rotation_survival_step (h : RNS.SurvivorCount.general_survivor_count) :
    random_rotation_survival := by
  intro T limit
  rw [h T limit]
  unfold primorial_modulus
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hqp : q.Prime := (Finset.mem_filter.mp hq).2
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqp.ne_zero
  rw [Nat.cast_sub (w_le T hqp.pos)]
  try simp only [id]
  rw [sub_div, div_self hq0]

#print axioms RNS.RandomRotation.rotation_is_shift_step
#print axioms RNS.RandomRotation.random_rotation_survival_step

end RNS.RandomRotation
