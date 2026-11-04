/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.Order.Interval.Finset.Basic -- `Finset.map_add_right_Icc`
import Mathlib.Tactic.Ring
import RNSNetwork.Nodes.UniformSubdivision.Conclusions

/-!
# Proofs for UniformSubdivision

Imports claims only, never other nodes' proofs. So far this file proves
`frozen_wheels_repeat` and `one_wheel_removed`; the node's other claims are
still planned.

Both rest on no other node, so each is proved directly as a `_holds`
theorem.
-/

namespace RNS.UniformSubdivision

/-- Adding the length of the combined cycle does not change whether a number
survives: every wheel size divides the cycle length. -/
private theorem survives_add_prod (W : Finset Nat) (k : Nat) :
    (∀ q ∈ W, ¬ q ∣ k + W.prod id) ↔ (∀ q ∈ W, ¬ q ∣ k) := by
  constructor
  · intro h q hq hdvd
    exact h q hq ((Nat.dvd_add_left (Finset.dvd_prod_of_mem id hq)).mpr hdvd)
  · intro h q hq hdvd
    exact h q hq ((Nat.dvd_add_left (Finset.dvd_prod_of_mem id hq)).mp hdvd)

/-- Splitting off one full cycle: the survivors up to one cycle plus `N` are
the survivors of the first cycle plus the survivors up to `N`. -/
private theorem card_survivors_prod_add (W : Finset Nat) (N : Nat) :
    (survivors_upto W (W.prod id + N)).card
      = (survivors_upto W (W.prod id)).card + (survivors_upto W N).card := by
  unfold survivors_upto
  -- The range up to one cycle plus `N` is the first cycle together with the
  -- range up to `N` slid up by one cycle.
  have hsplit : Finset.Icc 1 (W.prod id + N)
      = Finset.Icc 1 (W.prod id) ∪ (Finset.Icc 1 N).map (addRightEmbedding (W.prod id)) := by
    rw [Finset.map_add_right_Icc]
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (W.prod id))
      ((Finset.Icc 1 N).map (addRightEmbedding (W.prod id))) := by
    rw [Finset.map_add_right_Icc, Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_Icc] at hk hk'
    omega
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
    Finset.filter_map, Finset.card_map]
  congr 1
  congr 1
  exact Finset.filter_congr (fun k _ => by
    simp only [Function.comp_apply, addRightEmbedding_apply]
    exact survives_add_prod W k)

/-- **Frozen wheels repeat**, proved. -/
theorem frozen_wheels_repeat_holds : frozen_wheels_repeat := by
  intro W m r
  induction m with
  | zero => simp
  | succ m ih =>
    have h : (m + 1) * W.prod id + r = W.prod id + (m * W.prod id + r) := by ring
    rw [h, card_survivors_prod_add, ih]
    ring

end RNS.UniformSubdivision

#print axioms RNS.UniformSubdivision.frozen_wheels_repeat_holds

/-! ## One wheel removed (Meissel's identity) -/

namespace RNS.UniformSubdivision

/-- The survivors of the wheels `W` together with a new wheel `p` are the
survivors of `W` that `p` does not divide. -/
private theorem survivors_insert (W : Finset Nat) (p N : Nat) :
    survivors_upto (insert p W) N = (survivors_upto W N).filter (fun k => ¬ p ∣ k) := by
  ext k
  simp only [survivors_upto, Finset.mem_filter, Finset.forall_mem_insert]
  tauto

/-- The survivors of `W` that the new prime `p` divides are exactly `p` times
the survivors of `W` up to `N / p`. -/
private theorem multiples_eq_image (W : Finset Nat) (p N : Nat) (hp : p.Prime)
    (hW : ∀ q ∈ W, q.Prime) (hpW : p ∉ W) :
    (survivors_upto W N).filter (fun k => p ∣ k)
      = (survivors_upto W (N / p)).image (fun j => p * j) := by
  ext k
  simp only [survivors_upto, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hk1, hkN⟩, hsurv⟩, hpk⟩
    have hcancel : p * (k / p) = k := Nat.mul_div_cancel' hpk
    refine ⟨k / p, ⟨⟨?_, Nat.div_le_div_right hkN⟩, ?_⟩, hcancel⟩
    · rcases Nat.eq_zero_or_pos (k / p) with h0 | h0
      · rw [h0, Nat.mul_zero] at hcancel
        omega
      · omega
    · intro q hq hqj
      have hqk : q ∣ p * (k / p) := Nat.dvd_mul_left_of_dvd hqj p
      rw [hcancel] at hqk
      exact hsurv q hq hqk
  · rintro ⟨j, ⟨⟨hj1, hjN⟩, hsurv⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Nat.dvd_mul_right p j⟩
    · have hpos : 0 < p * j := Nat.mul_pos hp.pos (by omega)
      omega
    · calc p * j ≤ p * (N / p) := Nat.mul_le_mul (Nat.le_refl p) hjN
        _ ≤ N := Nat.mul_div_le N p
    · intro q hq hqd
      rcases (hW q hq).dvd_mul.mp hqd with h | h
      · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq (hW q hq) hp).mp h
        exact hpW (by rw [← hqp]; exact hq)
      · exact hsurv q hq h

/-- **One wheel removed**, proved. -/
theorem one_wheel_removed_holds : one_wheel_removed := by
  intro W p N hp hW hpW
  have hsplit : ((survivors_upto W N).filter (fun k => p ∣ k)).card
      + ((survivors_upto W N).filter (fun k => ¬ p ∣ k)).card = (survivors_upto W N).card :=
    Finset.card_filter_add_card_filter_not _
  have h1 : (survivors_upto (insert p W) N).card
      = ((survivors_upto W N).filter (fun k => ¬ p ∣ k)).card := by
    rw [survivors_insert]
  have hinj : Function.Injective (fun j : Nat => p * j) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hp.pos hab
  have h2 : ((survivors_upto W N).filter (fun k => p ∣ k)).card
      = (survivors_upto W (N / p)).card := by
    rw [multiples_eq_image W p N hp hW hpW, Finset.card_image_of_injective _ hinj]
  omega

end RNS.UniformSubdivision

#print axioms RNS.UniformSubdivision.one_wheel_removed_holds
