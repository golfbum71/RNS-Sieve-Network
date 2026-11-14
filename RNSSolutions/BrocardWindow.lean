/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib
import RNSNetwork.Nodes.BrocardWindow.Conclusions

/-!
# Proofs for BrocardWindow

Rests on no other node. Built clean on GitHub (standard axioms only,
2026-11-14).

The mark formula is the difference of two squares. The window condition is
the same identity moved across an inequality. The collision rule is: two
different primes dividing a number have their product dividing it; the
cofactor is above 1 because the product alone is below the window, and 2, 3
and 4 are off the 6n±1 tracks. The row rules compare the mark with the
wheel's cube or fourth power.
-/

namespace RNS.BrocardWindow

theorem mark_formula_holds : mark_formula := by
  intro q d i
  ring

theorem mark_in_window_iff_holds : mark_in_window_iff := by
  intro q d i g
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith [h1, h2]
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith [h1, h2]

theorem collision_product_holds : collision_product := by
  intro q₁ q₂ n h₁ h₂ hne hd₁ hd₂
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes h₁ h₂).mpr hne) hd₁ hd₂

theorem collision_cofactor_holds : collision_cofactor := by
  intro p q₁ q₂ t hprod hwin h2 h3
  have ht : 2 ≤ t := by
    by_contra hcon
    have h1 : t ≤ 1 := by omega
    have hle : q₁ * q₂ * t ≤ q₁ * q₂ * 1 := Nat.mul_le_mul (Nat.le_refl (q₁ * q₂)) h1
    linarith [hprod, hwin, hle]
  omega

theorem no_collision_large_product_holds : no_collision_large_product := by
  intro p N q₁ q₂ t hbig hprod hwin h2 h3
  have h5 : 5 ≤ t := collision_cofactor_holds p q₁ q₂ t hprod hwin h2 h3
  have hle : q₁ * q₂ * 5 ≤ q₁ * q₂ * t := Nat.mul_le_mul (Nat.le_refl (q₁ * q₂)) h5
  linarith [hbig, hle]

theorem large_wheel_row_holds : large_wheel_row := by
  intro q a b N hq ha hb
  have h1 : q * q ≤ a * b := Nat.mul_le_mul ha hb
  have h2 : q * (q * q) ≤ q * (a * b) := Nat.mul_le_mul (Nat.le_refl q) h1
  linarith [hq, h2]

theorem middle_wheel_row_holds : middle_wheel_row := by
  intro q a b e N hq ha hb he
  have h1 : q * q ≤ a * b := Nat.mul_le_mul ha hb
  have h2 : q * q * q ≤ a * b * e := Nat.mul_le_mul h1 he
  have h3 : q * (q * q * q) ≤ q * (a * b * e) := Nat.mul_le_mul (Nat.le_refl q) h2
  linarith [hq, h3]

end RNS.BrocardWindow

#print axioms RNS.BrocardWindow.mark_formula_holds
#print axioms RNS.BrocardWindow.mark_in_window_iff_holds
#print axioms RNS.BrocardWindow.collision_product_holds
#print axioms RNS.BrocardWindow.collision_cofactor_holds
#print axioms RNS.BrocardWindow.no_collision_large_product_holds
#print axioms RNS.BrocardWindow.large_wheel_row_holds
#print axioms RNS.BrocardWindow.middle_wheel_row_holds
