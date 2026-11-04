/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.Field.ZMod        -- remainders modulo a prime form a field
import Mathlib.Tactic.Push               -- `push Not`
import RNSNetwork.Nodes.SurvivorCount.Conclusions
import RNSNetwork.Nodes.Pruning.Conclusions

/-!
# Proof for Pruning

Imports claims only. The conclusion is proved as a step from
`SurvivorCount.general_survivor_count`, taken as the hypothesis `h_gen`.

Tactic proofs: `w_ap_offsets_of_dvd` and `w_ap_offsets_of_gt_not_dvd` are
copied from `rns_sieve_6.lean` (Parts D and E). In the main step, the
source's two `ite` rewrites (which its own comment flags as unverified) are
replaced by `simp [hqd]`, which settles the `if` from the case hypothesis.
-/

namespace RNS.Pruning

private theorem mem_active_primes_is_prime (limit : Nat) (q : Nat)
    (hq : q ∈ active_primes limit) : q.Prime := by
  unfold active_primes at hq
  exact (Finset.mem_filter.mp hq).2

private theorem w_ap_offsets_of_dvd (d k p : Nat) (_hp : p.Prime) (hdvd : p ∣ d)
    (hk : 1 ≤ k) : w (ap_offsets d k) p = 1 := by
  unfold w ap_offsets
  rw [Finset.image_image]
  show ((Finset.range k).image (fun i => i * d % p)).card = 1
  have himg : (Finset.range k).image (fun i => i * d % p) = {0} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨i, _, rfl⟩
      obtain ⟨c, hc⟩ := hdvd.mul_left i
      rw [hc]
      exact Nat.mul_mod_right p c
    · rintro rfl
      exact ⟨0, by omega, by simp⟩
  rw [himg]
  exact Finset.card_singleton 0

private theorem w_ap_offsets_of_gt_not_dvd (d k q : Nat) (hq : q.Prime) (hnd : ¬ q ∣ d)
    (hkq : k ≤ q) : w (ap_offsets d k) q = k := by
  have : Fact q.Prime := ⟨hq⟩
  unfold w ap_offsets
  rw [Finset.image_image]
  show ((Finset.range k).image (fun i => i * d % q)).card = k
  have hinj : Set.InjOn (fun i => i * d % q) ↑(Finset.range k) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    dsimp only at hij
    have hdne : (d : ZMod q) ≠ 0 := fun h => hnd ((ZMod.natCast_eq_zero_iff d q).mp h)
    have hcast : ((i * d : ℕ) : ZMod q) = ((j * d : ℕ) : ZMod q) := by
      rw [← ZMod.natCast_mod (i * d) q, ← ZMod.natCast_mod (j * d) q, hij]
    push_cast at hcast
    have hicast : (i : ZMod q) = (j : ZMod q) := mul_right_cancel₀ hdne hcast
    have hival : (i : ZMod q).val = i := ZMod.val_cast_of_lt (lt_of_lt_of_le hi hkq)
    have hjval : (j : ZMod q).val = j := ZMod.val_cast_of_lt (lt_of_lt_of_le hj hkq)
    rw [hicast, hjval] at hival
    exact hival.symm
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **Step:** the whole-cycle survivor count implies the exact pruning
count. -/
theorem valid_starting_residues_card_formula_step
    (h_gen : RNS.SurvivorCount.general_survivor_count) :
    valid_starting_residues_card_formula := by
  unfold valid_starting_residues_card_formula
  intro d k L _hd hk hfloor
  rw [h_gen (ap_offsets d k) L]
  apply Finset.prod_congr rfl
  intro q hq
  have hqp : q.Prime := mem_active_primes_is_prime L q hq
  by_cases hqd : q ∣ d
  · rw [w_ap_offsets_of_dvd d k q hqp hqd hk]
    simp [hqd]
  · have hqk : k < q := by
      by_contra hcon
      push Not at hcon
      exact hqd (hfloor q hqp hcon)
    rw [w_ap_offsets_of_gt_not_dvd d k q hqp hqd (le_of_lt hqk)]
    simp [hqd]

end RNS.Pruning

#print axioms RNS.Pruning.valid_starting_residues_card_formula_step
