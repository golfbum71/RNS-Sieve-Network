/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.QuadraticCharSum.Conclusions
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Tactic

/-!
# Proofs for QuadraticCharSum

Draft, 2026-11-22.

Over any finite field of odd characteristic. For a nonzero step: scaling by
the step turns the sum into the one for step 1; turning the wheel backwards
makes it the character of −1 times the Jacobi sum of the quadratic character
with itself, which Mathlib evaluates (`jacobiSum_nontrivial_inv`) as minus
the character of −1. Two different offsets are a nonzero step after a shift.

A quadratic with nonzero discriminant: four times it is a square minus the
discriminant, after the bijection x ↦ 2x + b. Counting square roots
(`quadraticChar_card_sqrts`) turns the sum over squares into a sum over all
positions, which splits into the step sum and a full character sum (0).
-/

namespace RNS.QuadraticCharSum

open Finset

section General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_mul_add_eq (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    ∑ x : F, quadraticChar F (x * (x + d)) = -1 := by
  have h1 : ∑ x : F, quadraticChar F (x * (x + d)) =
      ∑ t : F, quadraticChar F (t * (t + 1)) := by
    symm
    refine Fintype.sum_equiv (Equiv.mulLeft₀ d hd) _ _ (fun t => ?_)
    simp only [Equiv.mulLeft₀_apply]
    rw [show d * t * (d * t + d) = d ^ 2 * (t * (t + 1)) by ring, map_mul,
      quadraticChar_sq_one' hd, one_mul]
  have h2 : ∑ t : F, quadraticChar F (t * (t + 1)) =
      quadraticChar F (-1) * jacobiSum (quadraticChar F) (quadraticChar F) := by
    rw [jacobiSum, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.neg F) _ _ (fun t => ?_)
    simp only [Equiv.neg_apply]
    rw [show t * (t + 1) = -1 * (-t * (1 - -t)) by ring, map_mul, map_mul]
  have h3 : jacobiSum (quadraticChar F) (quadraticChar F) = -quadraticChar F (-1) := by
    have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic F).inv] at h
  rw [h1, h2, h3, mul_neg, ← sq, quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)]

theorem pair_sum (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ x : F, quadraticChar F ((x + a) * (x + b)) = -1 := by
  rw [← sum_mul_add_eq hF (sub_ne_zero.mpr (Ne.symm hab))]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ (fun x => ?_)
  simp only [Equiv.coe_addRight]
  congr 1
  ring

theorem sq_sum (a : F) :
    ∑ x : F, quadraticChar F ((x + a) * (x + a)) = (Fintype.card F : ℤ) - 1 := by
  have h1 : ∑ x : F, quadraticChar F ((x + a) * (x + a)) = ∑ y : F, quadraticChar F (y * y) :=
    Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)
  rw [h1]
  have h2 : ∀ y : F, quadraticChar F (y * y) = 1 - (if y = 0 then 1 else 0) := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · rw [if_neg hy, sub_zero, ← sq, quadraticChar_sq_one' hy]
  simp [h2, Finset.sum_sub_distrib]

/-- A sum over squares, as a sum over all positions weighted by the number of
square roots. -/
theorem sum_sq_fiber (g : F → ℤ) :
    ∑ y : F, g (y ^ 2) = ∑ z : F, ((univ.filter (fun y : F => y ^ 2 = z)).card : ℤ) * g z := by
  rw [← Finset.sum_fiberwise Finset.univ (fun y : F => y ^ 2) (fun y => g (y ^ 2))]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun y hy => by
    simp only [Finset.mem_filter] at hy
    rw [hy.2]

theorem quad_sum (hF : ringChar F ≠ 2) {b c : F} (hdisc : b ^ 2 - 4 * c ≠ 0) :
    ∑ x : F, quadraticChar F (x ^ 2 + b * x + c) = -1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h1 : ∑ x : F, quadraticChar F (x ^ 2 + b * x + c) =
      ∑ y : F, quadraticChar F (y ^ 2 - (b ^ 2 - 4 * c)) := by
    refine Fintype.sum_equiv ((Equiv.mulLeft₀ (2 : F) h2).trans (Equiv.addRight b)) _ _
      (fun x => ?_)
    simp only [Equiv.trans_apply, Equiv.mulLeft₀_apply, Equiv.coe_addRight]
    rw [show (2 * x + b) ^ 2 - (b ^ 2 - 4 * c) = 2 ^ 2 * (x ^ 2 + b * x + c) by ring, map_mul,
      quadraticChar_sq_one' h2, one_mul]
  have hcount : ∀ z : F, ((univ.filter (fun y : F => y ^ 2 = z)).card : ℤ) =
      quadraticChar F z + 1 := by
    intro z
    rw [← quadraticChar_card_sqrts hF z]
    congr 2
    ext y
    simp
  have hfib := sum_sq_fiber (fun z : F => quadraticChar F (z - (b ^ 2 - 4 * c)))
  simp only at hfib
  rw [h1, hfib]
  simp_rw [hcount, add_mul, one_mul, Finset.sum_add_distrib]
  have hshift : ∑ z : F, quadraticChar F (z - (b ^ 2 - 4 * c)) = ∑ z : F, quadraticChar F z :=
    Fintype.sum_equiv (Equiv.subRight (b ^ 2 - 4 * c)) _ _ (fun _ => rfl)
  rw [hshift, quadraticChar_sum_zero hF, add_zero,
    ← sum_mul_add_eq hF (neg_ne_zero.mpr hdisc)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul, sub_eq_add_neg]

end General

theorem ringChar_ne_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp2

theorem pair_char_sum_distinct_holds : pair_char_sum_distinct := by
  intro p _ hp2 a b hab
  exact pair_sum (ringChar_ne_two hp2) hab

theorem pair_char_sum_equal_holds : pair_char_sum_equal := by
  intro p _ a
  rw [sq_sum, ZMod.card]

theorem quadratic_char_sum_holds : quadratic_char_sum := by
  intro p _ hp2 b c hdisc
  exact quad_sum (ringChar_ne_two hp2) hdisc

end RNS.QuadraticCharSum

#print axioms RNS.QuadraticCharSum.pair_char_sum_distinct_holds
#print axioms RNS.QuadraticCharSum.pair_char_sum_equal_holds
#print axioms RNS.QuadraticCharSum.quadratic_char_sum_holds
