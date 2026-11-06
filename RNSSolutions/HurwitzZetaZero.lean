/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.HurwitzZetaZero.Conclusions
import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# Proofs for HurwitzZetaZero

Imports claims only, never other nodes' proofs. The value of the Hurwitz zeta
function at 0 rests on the node's cited claim `sin_zeta_at_one`, taken as a
named hypothesis.

Idea. Mathlib's Hurwitz zeta function is its even part plus its odd part. At 0
the even part is `-1/2` at the point 0 of the circle and 0 elsewhere
(`hurwitzZetaEven_apply_zero`). The functional equation
(`hurwitzZetaOdd_one_sub` at `s = 1`) makes the odd part at 0 equal to
`sinZeta` at 1 divided by π. At `x = 1`, the point 0 of the circle, `sinZeta`
vanishes, being odd; for `0 < x < 1` the cited claim gives `π (1/2 - x)`.

Built clean by `lake build RNSSolutions` on 2026-11-05; `#print axioms` shows only
the standard three.
-/

namespace RNS.HurwitzZetaZero

open HurwitzZeta

/-- At 0, the odd part of the Hurwitz zeta function is `sinZeta` at 1 divided
by π. -/
private theorem odd_at_zero (a : UnitAddCircle) :
    hurwitzZetaOdd a 0 = sinZeta a 1 / (Real.pi : ℂ) := by
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have h2 : (1 : ℝ) = -(n : ℝ) := by simpa using congrArg Complex.re h
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := hurwitzZetaOdd_one_sub a hs
  rw [sub_self, Complex.cpow_neg_one, Complex.Gamma_one, mul_one, mul_one,
    Complex.sin_pi_div_two] at h
  rw [h, mul_inv, div_eq_mul_inv]
  ring

theorem hurwitz_zeta_at_zero_step (h_sin : sin_zeta_at_one) : hurwitz_zeta_at_zero := by
  intro x hx0 hx1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold HurwitzZeta.hurwitzZeta
  rw [hurwitzZetaEven_apply_zero, odd_at_zero]
  rcases hx1.lt_or_eq with hlt | rfl
  · -- `0 < x < 1`: not the point 0 of the circle
    have hne : (x : UnitAddCircle) ≠ 0 := by
      intro h0
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_of_pos_iff (1 : ℝ) one_pos hx0).mp h0
      have hn' : (n : ℝ) = x := by simpa using hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp at hn'
        linarith
      · have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hpos
        linarith
    simp only [hne, ↓reduceIte]
    rw [h_sin x hx0 hlt, zero_add]
    exact mul_div_cancel_left₀ _ hπ
  · -- `x = 1`: the point 0 of the circle, where `sinZeta` vanishes
    have h0 : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period (1 : ℝ)
    have hs0 : sinZeta (0 : UnitAddCircle) 1 = 0 := by
      have h := sinZeta_neg (0 : UnitAddCircle) 1
      rw [neg_zero] at h
      linear_combination h / 2
    simp only [h0, ↓reduceIte]
    rw [hs0, zero_div]
    norm_num

end RNS.HurwitzZetaZero

#print axioms RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_step
