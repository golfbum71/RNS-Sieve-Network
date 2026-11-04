/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Tactic.Ring
import RNSNetwork.Nodes.UniformSubdivision.Conclusions
import RNSNetwork.Nodes.LehmerSplit.Conclusions

/-!
# Proofs for LehmerSplit

Imports claims only, never other nodes' proofs. Both conclusions are proved
as steps from claims of `UniformSubdivision`, taken as named hypotheses;
`RNSSolutions/Assemble.lean` plugs in the finished proofs.
-/

namespace RNS.LehmerSplit

open RNS.UniformSubdivision

/-- The arithmetic behind the split. If the rotating prime is `k * t + 1` and
`M` is `k` times a quotient `m` plus a remainder below `k`, then `M` times the
prime, divided by `k`, rounds down to `M * t + m`, and that, divided by the
prime, rounds down to `m`. -/
private theorem lehmer_floor (M k t m b : Nat) (hab : k * m + b = M) (hb : b < k) :
    M * (k * t + 1) / k = M * t + m ∧ (M * t + m) / (k * t + 1) = m := by
  subst hab
  have hbt : b * t ≤ k * t := Nat.mul_le_mul (Nat.le_of_lt hb) (Nat.le_refl t)
  have e2 : (k * m + b) * (k * t + 1) = k * (k * (m * t)) + k * (b * t) + k * m + b := by ring
  have e5 : (k * m + b) * t + m = k * (m * t) + b * t + m := by ring
  constructor
  · apply Nat.div_eq_of_lt_le
    · have e1 : ((k * m + b) * t + m) * k = k * (k * (m * t)) + k * (b * t) + k * m := by ring
      rw [e1, e2]
      omega
    · have e3 : ((k * m + b) * t + m + 1) * k = k * (k * (m * t)) + k * (b * t) + k * m + k := by
        ring
      rw [e2, e3]
      omega
  · apply Nat.div_eq_of_lt_le
    · have e4 : m * (k * t + 1) = k * (m * t) + m := by ring
      rw [e4, e5]
      omega
    · have e6 : (m + 1) * (k * t + 1) = k * (m * t) + m + k * t + 1 := by ring
      rw [e5, e6]
      omega

/-- A prime leaving remainder 1 on division by `k` forces `k` to be positive
and the prime to be `k * t + 1` for some `t`. -/
private theorem prime_eq_mul_add_one (p k : Nat) (hp : p.Prime) (hpk : p % k = 1) :
    0 < k ∧ ∃ t, k * t + 1 = p := by
  refine ⟨?_, p / k, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mod_zero] at hpk
      have := hp.one_lt
      omega
    · exact h
  · have := Nat.div_add_mod p k
    omega

/-- Nothing survives up to 0. -/
private theorem survivors_upto_zero (W : Finset Nat) : (survivors_upto W 0).card = 0 := by
  rw [Finset.card_eq_zero]
  unfold survivors_upto
  rw [Finset.filter_eq_empty_iff]
  intro k hk
  simp only [Finset.mem_Icc] at hk
  omega

/-- Nothing survives up to 0, in any column. -/
private theorem column_survivors_upto_zero (W : Finset Nat) (r : Nat) :
    (column_survivors_upto W r 0).card = 0 := by
  rw [Finset.card_eq_zero]
  unfold column_survivors_upto survivors_upto
  rw [Finset.filter_eq_empty_iff]
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_Icc] at hk
  omega

/-- **Lehmer's even split**, as a step from `frozen_wheels_repeat` and
`one_wheel_removed`. -/
theorem lehmer_even_split_step (h_rep : frozen_wheels_repeat) (h_rem : one_wheel_removed) :
    lehmer_even_split := by
  intro W p k a hp hW hpW hpk
  obtain ⟨hk, t, hpt⟩ := prime_eq_mul_add_one p k hp hpk
  obtain ⟨hE, hEp⟩ := lehmer_floor (a * W.prod id) k t (a * W.prod id / k)
    (a * W.prod id % k) (Nat.div_add_mod _ _) (Nat.mod_lt _ hk)
  rw [hpt] at hE hEp
  -- The end of the `a`-th interval is `a * t` frozen cycles plus an overhang.
  have hend : a * (W.prod id * p) / k = a * t * W.prod id + a * W.prod id / k := by
    rw [← Nat.mul_assoc, hE, Nat.mul_right_comm]
  have hEp' : (a * t * W.prod id + a * W.prod id / k) / p = a * W.prod id / k := by
    rw [Nat.mul_right_comm] at hEp
    exact hEp
  -- Survivors up to the end of the `a`-th interval.
  have hcount : (survivors_upto (insert p W) (a * (W.prod id * p) / k)).card
      = a * t * (survivors_upto W (W.prod id)).card := by
    rw [hend, h_rem W p _ hp hW hpW, hEp', h_rep W (a * t) _]
    omega
  -- Survivors of the whole cycle.
  have htotal : (survivors_upto (insert p W) (W.prod id * p)).card
      = k * t * (survivors_upto W (W.prod id)).card := by
    have hQp : W.prod id * p / p = W.prod id := Nat.mul_div_cancel _ hp.pos
    have hrep := h_rep W p 0
    rw [Nat.add_zero, Nat.mul_comm p (W.prod id), survivors_upto_zero, Nat.add_zero] at hrep
    have hpφ : p * (survivors_upto W (W.prod id)).card
        = k * t * (survivors_upto W (W.prod id)).card + (survivors_upto W (W.prod id)).card := by
      rw [← hpt]
      ring
    rw [h_rem W p _ hp hW hpW, hQp, hrep]
    omega
  rw [hcount, htotal]
  ring

/-- **Lehmer's even split, within one column**, as a step from
`column_frozen_repeat` and `column_one_wheel_removed`. -/
theorem lehmer_even_split_column_step (h_rep : column_frozen_repeat)
    (h_rem : column_one_wheel_removed) : lehmer_even_split_column := by
  intro W p k a r hp hW hpW h2 h3 hpk hp6
  obtain ⟨hk, t, hpt⟩ := prime_eq_mul_add_one p k hp hpk
  obtain ⟨hE, hEp⟩ := lehmer_floor (a * W.prod id) k t (a * W.prod id / k)
    (a * W.prod id % k) (Nat.div_add_mod _ _) (Nat.mod_lt _ hk)
  rw [hpt] at hE hEp
  have hend : a * (W.prod id * p) / k = a * t * W.prod id + a * W.prod id / k := by
    rw [← Nat.mul_assoc, hE, Nat.mul_right_comm]
  have hEp' : (a * t * W.prod id + a * W.prod id / k) / p = a * W.prod id / k := by
    rw [Nat.mul_right_comm] at hEp
    exact hEp
  -- A wheel on the 6n+1 side keeps every column in place.
  have hr : ∀ j, p * j % 6 = r ↔ j % 6 = r := by
    intro j
    rw [Nat.mul_mod, hp6]
    omega
  have hcount : (column_survivors_upto (insert p W) r (a * (W.prod id * p) / k)).card
      = a * t * (column_survivors_upto W r (W.prod id)).card := by
    have hA := h_rem W p (a * (W.prod id * p) / k) r r hp hW hpW hr
    rw [hend, hEp', h_rep W r (a * t) _ h2 h3] at hA
    rw [hend]
    omega
  have htotal : (column_survivors_upto (insert p W) r (W.prod id * p)).card
      = k * t * (column_survivors_upto W r (W.prod id)).card := by
    have hQp : W.prod id * p / p = W.prod id := Nat.mul_div_cancel _ hp.pos
    have hrep := h_rep W r p 0 h2 h3
    rw [Nat.add_zero, Nat.mul_comm p (W.prod id), column_survivors_upto_zero, Nat.add_zero]
      at hrep
    have hpφ : p * (column_survivors_upto W r (W.prod id)).card
        = k * t * (column_survivors_upto W r (W.prod id)).card
          + (column_survivors_upto W r (W.prod id)).card := by
      rw [← hpt]
      ring
    have hA := h_rem W p (W.prod id * p) r r hp hW hpW hr
    rw [hQp, hrep] at hA
    omega
  rw [hcount, htotal]
  ring

end RNS.LehmerSplit

#print axioms RNS.LehmerSplit.lehmer_even_split_step
#print axioms RNS.LehmerSplit.lehmer_even_split_column_step
