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
`frozen_wheels_repeat`; the node's other claims are still planned.

`frozen_wheels_repeat` rests on no other node, so it is proved directly as a
`_holds` theorem.
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
