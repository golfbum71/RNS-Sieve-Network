/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.KanoldBound.Conclusions
import Mathlib.Tactic

/-!
# Proofs for KanoldBound

Draft, 2026-11-22. Kanold's bound itself (`stretch_holds_survivor`) stays cited.

Progressions: multiply the progression by an inverse of its step on the
combined cycle of the wheels. That turns it into a stretch of consecutive
numbers, and a survivor of the stretch pulls back to a survivor of the
progression, because each wheel divides a progression term only if it divides
the matching number of the stretch.

Adding a wheel: of the first two numbers of the stretch, one is not divisible
by the new wheel. The progression that starts there and steps by the new wheel
has `L` terms inside the stretch, none of them divisible by the new wheel, and
by the progression form one of them survives the old wheels.
-/

namespace RNS.KanoldBound

theorem progression_holds_survivor_holds : progression_holds_survivor := by
  intro W hW L hL a d hd
  have hP0 : (∏ q ∈ W, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hW q hq).ne_zero
  haveI : NeZero (∏ q ∈ W, q) := ⟨hP0⟩
  have hc : Nat.Coprime d (∏ q ∈ W, q) := by
    rw [Nat.coprime_prod_right_iff]
    intro q hq
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (hW q hq)).mpr (hd q hq))
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = (((ZMod.unitOfCoprime d hc)⁻¹ : (ZMod (∏ q ∈ W, q))ˣ) :
      ZMod (∏ q ∈ W, q)).val := ⟨_, rfl⟩
  have hdu : (d * u) % (∏ q ∈ W, q) = 1 % (∏ q ∈ W, q) := by
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one,
      ← ZMod.coe_unitOfCoprime d hc, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨i, hi, hsurv⟩ := hL (u * a)
  refine ⟨i, hi, fun q hq hdiv => hsurv q hq ?_⟩
  have hqP : q ∣ ∏ q ∈ W, q := Finset.dvd_prod_of_mem (fun q => q) hq
  have hmod : d * u ≡ 1 [MOD q] := by
    unfold Nat.ModEq
    rw [← Nat.mod_mod_of_dvd (d * u) hqP, hdu, Nat.mod_mod_of_dvd 1 hqP]
  have h2 : u * a + i * (d * u) ≡ u * a + i * 1 [MOD q] := (hmod.mul_left i).add_left (u * a)
  have h3 : q ∣ u * a + i * (d * u) := by
    have e : u * a + i * (d * u) = u * (a + i * d) := by ring
    rw [e]
    exact Dvd.dvd.mul_left hdiv u
  rw [mul_one] at h2
  exact Nat.modEq_zero_iff_dvd.mp (h2.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3))

theorem add_wheel_stretch_step (h : progression_holds_survivor) : add_wheel_stretch := by
  intro W hW L hL r hr hrW x
  have hL1 : 1 ≤ L := by
    obtain ⟨i, hi, _⟩ := hL 0
    omega
  obtain ⟨s, hs0, hs⟩ : ∃ s, s ≤ 1 ∧ ¬ r ∣ x + s := by
    by_cases h0 : r ∣ x
    · refine ⟨1, le_rfl, fun h1 => ?_⟩
      have h01 := Nat.dvd_sub' h1 h0
      rw [Nat.add_sub_cancel_left] at h01
      exact hr.one_lt.ne' (Nat.dvd_one.mp h01)
    · exact ⟨0, Nat.zero_le _, by simpa using h0⟩
  have hd : ∀ q ∈ W, ¬ q ∣ r := by
    intro q hq hqr
    have e := (Nat.prime_dvd_prime_iff_eq (hW q hq) hr).mp hqr
    exact hrW (e ▸ hq)
  obtain ⟨i, hi, hsurv⟩ := h W hW L hL (x + s) r hd
  refine ⟨s + i * r, ?_, ?_⟩
  · have hir : i * r ≤ (L - 1) * r := Nat.mul_le_mul_right r (by omega)
    have hcomm : (L - 1) * r = r * (L - 1) := Nat.mul_comm _ _
    omega
  · intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with hqr | hq
    · rw [hqr]
      intro hdiv
      rw [← add_assoc] at hdiv
      have hxs := Nat.dvd_sub' hdiv (dvd_mul_left r i)
      rw [Nat.add_sub_cancel] at hxs
      exact hs hxs
    · rw [← add_assoc]
      exact hsurv q hq

theorem add_wheel_stretch_holds : add_wheel_stretch :=
  add_wheel_stretch_step progression_holds_survivor_holds

end RNS.KanoldBound

#print axioms RNS.KanoldBound.progression_holds_survivor_holds
#print axioms RNS.KanoldBound.add_wheel_stretch_holds
