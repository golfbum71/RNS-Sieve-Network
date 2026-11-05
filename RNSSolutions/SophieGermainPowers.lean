/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SophieGermainPowers.Conclusions
import Mathlib.FieldTheory.Finite.Basic       -- `ZMod.pow_card_sub_one_eq_one` (Fermat)
import Mathlib.Tactic.LinearCombination

/-!
# Proofs for SophieGermainPowers

Imports claims only, never other nodes' proofs. Rests on no other node.
Built clean by the GitHub Actions build on 2026-11-05.
`three_powers_blocked` uses `pth_power_positions` from this same node.
-/

namespace RNS.SophieGermainPowers

/-- On the wheel of size `2p + 1` (prime), a position other than 0, raised to
the `p`-th power, is at 1 or -1: its square is the `2p`-th power, which is 1
by Fermat's little theorem. -/
private theorem pow_cases {p : Nat} [Fact (2 * p + 1).Prime] (a : ZMod (2 * p + 1))
    (ha : a ≠ 0) : a ^ p = 1 ∨ a ^ p = -1 := by
  have h := ZMod.pow_card_sub_one_eq_one ha
  have e : 2 * p + 1 - 1 = p + p := by omega
  rw [e, pow_add] at h
  exact mul_self_eq_one_iff.mp h

/-- **Three positions for p-th powers**, proved. -/
theorem pth_power_positions_holds : pth_power_positions := by
  intro p hp hq t
  have : Fact (2 * p + 1).Prime := ⟨hq⟩
  push_cast
  by_cases ht : (t : ZMod (2 * p + 1)) = 0
  · left
    rw [ht, zero_pow hp.ne_zero]
  · right
    exact pow_cases _ ht

/-- The wheel of size `2p + 1` does not block 3. -/
private theorem three_ne_zero_on_wheel {p : Nat} (hp : p.Prime) [Fact (2 * p + 1).Prime] :
    (3 : ZMod (2 * p + 1)) ≠ 0 := by
  intro h
  have h' : ((3 : Nat) : ZMod (2 * p + 1)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := hp.two_le
  omega

/-- **Three p-th powers: the wheel blocks one**, proved. -/
theorem three_powers_blocked_holds : three_powers_blocked := by
  intro p hp hq x y z hsum
  have : Fact (2 * p + 1).Prime := ⟨hq⟩
  by_contra hnone
  have hx : ¬ ((2 * p + 1 : Nat) : Int) ∣ x := fun h => hnone (Or.inl h)
  have hy : ¬ ((2 * p + 1 : Nat) : Int) ∣ y := fun h => hnone (Or.inr (Or.inl h))
  have hz : ¬ ((2 * p + 1 : Nat) : Int) ∣ z := fun h => hnone (Or.inr (Or.inr h))
  have unblocked : ∀ t : Int, ¬ ((2 * p + 1 : Nat) : Int) ∣ t →
      (t : ZMod (2 * p + 1)) ^ p = 1 ∨ (t : ZMod (2 * p + 1)) ^ p = -1 := by
    intro t ht
    apply pow_cases
    intro h0
    exact ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t (2 * p + 1)).mp h0)
  have hs : ((x ^ p + y ^ p + z ^ p : Int) : ZMod (2 * p + 1)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 * p + 1)).mpr hsum
  push_cast at hs
  have h3 := three_ne_zero_on_wheel hp
  rcases unblocked x hx with ex | ex <;> rcases unblocked y hy with ey | ey <;>
    rcases unblocked z hz with ez | ez <;> rw [ex, ey, ez] at hs <;>
    first
      | exact one_ne_zero (by linear_combination hs)
      | exact one_ne_zero (by linear_combination -hs)
      | exact h3 (by linear_combination hs)
      | exact h3 (by linear_combination -hs)

end RNS.SophieGermainPowers

#print axioms RNS.SophieGermainPowers.pth_power_positions_holds
#print axioms RNS.SophieGermainPowers.three_powers_blocked_holds
