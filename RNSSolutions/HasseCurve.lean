/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.HasseCurve.Conclusions
import RNSNetwork.Nodes.StepanovWeil.Conclusions
import Mathlib.Tactic

/-!
# Proofs for HasseCurve

Draft, 2026-11-22.

Shifted by one, the product of three consecutive positions is
(y − 1) · y · (y + 1), an odd function of y. When the wheel size leaves
remainder 3 on dividing by 4, −1 is not a square, so the character sum of an
odd function is 0 (Mathlib's `quadraticChar_sum_comp_eq_zero_of_odd`). Each
first coordinate then has one plus the character many second coordinates
(`quadraticChar_card_sqrts`), so the count is the wheel size.

Hasse's bound is a step from Weil's bound (`StepanovWeil.weil_pattern_bound`,
cited) for the pattern 0, 1, 2, whose three members sit on different positions
of every wheel from 3 on.
-/

namespace RNS.HasseCurve

open Finset

theorem three_consecutive_sum_zero_holds : three_consecutive_sum_zero := by
  intro p _ hp4
  have hns : ¬ IsSquare (-1 : ZMod p) := by
    rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
    omega
  have h1 : ∑ x : ZMod p, quadraticChar (ZMod p) (x * (x + 1) * (x + 2)) =
      ∑ y : ZMod p, quadraticChar (ZMod p) ((y - 1) * y * (y + 1)) := by
    refine Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun x => ?_)
    simp only [Equiv.coe_addRight]
    congr 1
    ring
  rw [h1]
  exact quadraticChar_sum_comp_eq_zero_of_odd hns (f := fun y => (y - 1) * y * (y + 1))
    (fun a => by
      show (-a - 1) * -a * (-a + 1) = -((a - 1) * a * (a + 1))
      ring)

theorem three_consecutive_point_count_step (h : three_consecutive_sum_zero) :
    three_consecutive_point_count := by
  intro p _ hp4
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hcount : ∀ a : ZMod p, ((univ.filter (fun y : ZMod p => y ^ 2 = a)).card : ℤ) =
      quadraticChar (ZMod p) a + 1 := by
    intro a
    rw [← quadraticChar_card_sqrts hp2 a]
    congr 2
    ext y
    simp
  have key : ((univ.filter (fun q : ZMod p × ZMod p =>
      q.2 ^ 2 = q.1 * (q.1 + 1) * (q.1 + 2))).card : ℤ) = p := by
    rw [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_boole]
    simp_rw [hcount]
    rw [Finset.sum_add_distrib, h p hp4]
    simp [ZMod.card]
  exact_mod_cast key

theorem hasse_bound_step (h : RNS.StepanovWeil.weil_pattern_bound) : hasse_bound := by
  intro p _ hp2
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hw : w ({0, 1, 2} : Finset ℕ) p = ({0, 1, 2} : Finset ℕ).card := by
    unfold w
    have himg : ({0, 1, 2} : Finset ℕ).image (fun t => t % p) = {0, 1, 2} := by
      simp [Finset.image_insert, Nat.mod_eq_of_lt (by omega : 1 < p),
        Nat.mod_eq_of_lt (by omega : 2 < p)]
    rw [himg]
  have hb := h p hp2 {0, 1, 2} (by decide) hw
  have hprod : ∀ x : ZMod p, ∏ t ∈ ({0, 1, 2} : Finset ℕ), (x + (t : ZMod p)) =
      x * (x + 1) * (x + 2) := by
    intro x
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
    push_cast
    ring
  simp only [hprod] at hb
  have hc : ((({0, 1, 2} : Finset ℕ).card : ℕ) : ℤ) = 3 := by decide
  rw [hc] at hb
  linarith

end RNS.HasseCurve

#print axioms RNS.HasseCurve.three_consecutive_sum_zero_holds
#print axioms RNS.HasseCurve.three_consecutive_point_count_step
#print axioms RNS.HasseCurve.hasse_bound_step
