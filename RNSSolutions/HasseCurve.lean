/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.HasseCurve.Conclusions
import RNSNetwork.Nodes.StepanovWeil.Conclusions
import RNSNetwork.Nodes.QuadraticCharSum.Conclusions
import Mathlib.Tactic

/-!
# Proofs for HasseCurve

Built clean by `lake build RNSSolutions` on 2026-11-22; `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

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

/-! ## Hasse's bound from Jacobsthal's sums (added 2026-11-22, draft)

The twist by a square comes from turning the wheel by the nonzero factor. For
the second moment, the square of a twisted sum is a double sum over two
positions; summing over the twist first gives, for each pair, the two-offset
sum of `QuadraticCharSum` at the offsets minus their squares: −1 unless the
squares agree, the wheel size minus 1 when they do. The −1 part adds up to the
square of a full character sum, 0; the other part counts each nonzero position
with itself and with its negative. For the bound, each nonzero square is hit by
two positions, so the twists by squares carry at most twice the second moment,
and each of them has the same square as the untwisted sum. -/

namespace RNS.HasseCurve

open Finset

theorem jacobsthal_twist_holds : jacobsthal_twist := by
  intro p _ n t ht
  unfold jacobsthal_sum
  rw [Finset.mul_sum]
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft₀ t ht) _ _ (fun y => ?_)
  simp only [Equiv.mulLeft₀_apply]
  rw [show (t * y) ^ 3 - n * t ^ 2 * (t * y) = t ^ 2 * (t * (y ^ 3 - n * y)) by ring,
    map_mul (quadraticChar (ZMod p)) (t ^ 2) (t * (y ^ 3 - n * y)), quadraticChar_sq_one' ht,
    one_mul, map_mul]

/-- The two-offset sum at the offsets minus two given positions. -/
theorem inner_sum (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (h1 : RNS.QuadraticCharSum.pair_char_sum_distinct)
    (h2 : RNS.QuadraticCharSum.pair_char_sum_equal) (u v : ZMod p) :
    ∑ n : ZMod p, quadraticChar (ZMod p) ((u - n) * (v - n)) =
      if u = v then (p : ℤ) - 1 else -1 := by
  have e : ∀ n : ZMod p, (u - n) * (v - n) = (n + -u) * (n + -v) := fun n => by ring
  simp_rw [e]
  split_ifs with huv
  · rw [huv]
    exact h2 p (-v)
  · exact h1 p hp2 (-u) (-v) (fun h => huv (neg_injective h))

theorem char_cube (p : ℕ) [Fact p.Prime] (n x : ZMod p) :
    quadraticChar (ZMod p) (x ^ 3 - n * x) =
      quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x ^ 2 - n) := by
  rw [show x ^ 3 - n * x = x * (x ^ 2 - n) by ring, map_mul]

theorem sum_comm3 {α : Type*} [Fintype α] (F : α → α → α → ℤ) :
    ∑ n, ∑ x, ∑ y, F n x y = ∑ x, ∑ y, ∑ n, F n x y := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

theorem jacobsthal_second_moment_step (h1 : RNS.QuadraticCharSum.pair_char_sum_distinct)
    (h2 : RNS.QuadraticCharSum.pair_char_sum_equal) : jacobsthal_second_moment := by
  intro p _ hp2
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hsq : ∀ n : ZMod p, jacobsthal_sum p n ^ 2 = ∑ x : ZMod p, ∑ y : ZMod p,
      quadraticChar (ZMod p) x * quadraticChar (ZMod p) y *
        quadraticChar (ZMod p) ((x ^ 2 - n) * (y ^ 2 - n)) := by
    intro n
    unfold jacobsthal_sum
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [char_cube, char_cube, map_mul]
    ring
  simp_rw [hsq]
  refine (sum_comm3 _).trans ?_
  have hC : ∀ x y : ZMod p, ∑ n : ZMod p, quadraticChar (ZMod p) x * quadraticChar (ZMod p) y *
      quadraticChar (ZMod p) ((x ^ 2 - n) * (y ^ 2 - n)) =
      quadraticChar (ZMod p) x * quadraticChar (ZMod p) y *
        (if x ^ 2 = y ^ 2 then (p : ℤ) - 1 else -1) := by
    intro x y
    rw [← Finset.mul_sum, inner_sum p hp2 h1 h2]
  simp_rw [hC]
  have hD : ∀ x y : ZMod p, quadraticChar (ZMod p) x * quadraticChar (ZMod p) y *
      (if x ^ 2 = y ^ 2 then (p : ℤ) - 1 else -1) =
      -(quadraticChar (ZMod p) x * quadraticChar (ZMod p) y) +
        (if x ^ 2 = y ^ 2 then (p : ℤ) * (quadraticChar (ZMod p) x * quadraticChar (ZMod p) y)
          else 0) := by
    intro x y
    split_ifs <;> ring
  have hz : ∑ x : ZMod p, ∑ y : ZMod p, quadraticChar (ZMod p) x * quadraticChar (ZMod p) y = 0 := by
    rw [← Finset.sum_mul_sum, quadraticChar_sum_zero hF, zero_mul]
  simp_rw [hD, Finset.sum_add_distrib, Finset.sum_neg_distrib, hz, neg_zero, zero_add]
  have hE : ∀ x : ZMod p, ∑ y : ZMod p, (if x ^ 2 = y ^ 2 then
      (p : ℤ) * (quadraticChar (ZMod p) x * quadraticChar (ZMod p) y) else 0) =
      (p : ℤ) * (1 + quadraticChar (ZMod p) (-1)) -
        (if x = 0 then (p : ℤ) * (1 + quadraticChar (ZMod p) (-1)) else 0) := by
    intro x
    rw [← Finset.sum_filter]
    by_cases hx : x = 0
    · subst hx
      simp
    · simp only [hx, ↓reduceIte, sub_zero]
      have hfil : (univ.filter (fun y : ZMod p => x ^ 2 = y ^ 2)) = {x, -x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro h
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
          · left
            exact h.symm
          · right
            rw [h, neg_neg]
        · rintro (h | h) <;> subst h <;> ring
      have hne : x ≠ -x := fun h => hx ((Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h.symm)
      rw [hfil, Finset.sum_pair hne]
      have hxx : quadraticChar (ZMod p) x * quadraticChar (ZMod p) x = 1 := by
        rw [← sq]
        exact quadraticChar_sq_one hx
      have hneg : quadraticChar (ZMod p) (-x) =
          quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) x := by
        rw [← map_mul, neg_one_mul]
      rw [hneg]
      linear_combination (p : ℤ) * (1 + quadraticChar (ZMod p) (-1)) * hxx
  rw [Finset.sum_congr rfl fun x _ => hE x, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte, nsmul_eq_mul]
  ring

/-- A sum over squares, as a sum over all positions weighted by the number of
square roots (the same counting step as in `QuadraticCharSum`'s proof file). -/
theorem sum_sq_fiber' (p : ℕ) [Fact p.Prime] (g : ZMod p → ℤ) :
    ∑ y : ZMod p, g (y ^ 2) =
      ∑ z : ZMod p, ((univ.filter (fun y : ZMod p => y ^ 2 = z)).card : ℤ) * g z := by
  rw [← Finset.sum_fiberwise Finset.univ (fun y : ZMod p => y ^ 2) (fun y => g (y ^ 2))]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun y hy => by
    simp only [Finset.mem_filter] at hy
    rw [hy.2]

theorem hasse_bound_of_moment_step (ht : jacobsthal_twist) (hm : jacobsthal_second_moment) :
    hasse_bound := by
  intro p _ hp2
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hS : ∑ x : ZMod p, quadraticChar (ZMod p) (x * (x + 1) * (x + 2)) = jacobsthal_sum p 1 := by
    unfold jacobsthal_sum
    refine Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun x => ?_)
    simp only [Equiv.coe_addRight]
    congr 1
    ring
  rw [hS]
  have hlow : ((p : ℤ) - 1) * jacobsthal_sum p 1 ^ 2 ≤
      ∑ t : ZMod p, jacobsthal_sum p (t ^ 2) ^ 2 := by
    have hterm : ∀ t : ZMod p, (jacobsthal_sum p 1 ^ 2 -
        if t = 0 then jacobsthal_sum p 1 ^ 2 else 0) ≤ jacobsthal_sum p (t ^ 2) ^ 2 := by
      intro t
      by_cases h0 : t = 0
      · simp only [h0, ↓reduceIte, sub_self]
        positivity
      · simp only [h0, ↓reduceIte, sub_zero]
        have htw := ht p 1 t h0
        rw [one_mul] at htw
        simp only [htw, mul_pow, quadraticChar_sq_one h0, one_mul, le_refl]
    calc ((p : ℤ) - 1) * jacobsthal_sum p 1 ^ 2 =
        ∑ t : ZMod p, (jacobsthal_sum p 1 ^ 2 - if t = 0 then jacobsthal_sum p 1 ^ 2 else 0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
            Finset.sum_ite_eq']
          simp only [Finset.mem_univ, ↓reduceIte, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum fun t _ => hterm t
  have hcount : ∀ a : ZMod p, ((univ.filter (fun y : ZMod p => y ^ 2 = a)).card : ℤ) =
      quadraticChar (ZMod p) a + 1 := by
    intro a
    rw [← quadraticChar_card_sqrts hF a]
    congr 2
    ext y
    simp
  have hup : ∑ t : ZMod p, jacobsthal_sum p (t ^ 2) ^ 2 ≤
      2 * ∑ n : ZMod p, jacobsthal_sum p n ^ 2 := by
    have hf := sum_sq_fiber' p (fun n => jacobsthal_sum p n ^ 2)
    rw [hf, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [hcount n]
    have hnn : 0 ≤ jacobsthal_sum p n ^ 2 := by positivity
    rcases quadraticChar_isQuadratic (ZMod p) n with h | h | h <;> rw [h] <;> linarith
  have hmom := hm p hp2
  have hc : quadraticChar (ZMod p) (-1) ≤ 1 := by
    rcases quadraticChar_isQuadratic (ZMod p) (-1) with h | h | h <;> rw [h] <;> norm_num
  have hp1 : (0 : ℤ) < (p : ℤ) - 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  have h3 : 2 * ((p : ℤ) * ((p : ℤ) - 1) * (1 + quadraticChar (ZMod p) (-1))) ≤
      ((p : ℤ) - 1) * (4 * (p : ℤ)) := by
    nlinarith [mul_nonneg (mul_nonneg hp0 hp1.le) (sub_nonneg.mpr hc)]
  have key : ((p : ℤ) - 1) * jacobsthal_sum p 1 ^ 2 ≤ ((p : ℤ) - 1) * (4 * (p : ℤ)) := by
    calc ((p : ℤ) - 1) * jacobsthal_sum p 1 ^ 2 ≤ ∑ t : ZMod p, jacobsthal_sum p (t ^ 2) ^ 2 := hlow
      _ ≤ 2 * ∑ n : ZMod p, jacobsthal_sum p n ^ 2 := hup
      _ = 2 * ((p : ℤ) * ((p : ℤ) - 1) * (1 + quadraticChar (ZMod p) (-1))) := by rw [hmom]
      _ ≤ _ := h3
  exact le_of_mul_le_mul_left key hp1

end RNS.HasseCurve

#print axioms RNS.HasseCurve.jacobsthal_twist_holds
#print axioms RNS.HasseCurve.jacobsthal_second_moment_step
#print axioms RNS.HasseCurve.hasse_bound_of_moment_step

