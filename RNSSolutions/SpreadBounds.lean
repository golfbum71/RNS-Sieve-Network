/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Data.Nat.ModEq -- `Nat.add_div_le_add_div`, `Nat.add_div_le_div_add_div_add_one`
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RNSNetwork.Nodes.Sawtooth.Conclusions
import RNSNetwork.Nodes.SpreadBounds.Conclusions

/-!
# Proofs for SpreadBounds

Imports claims only, never other nodes' proofs. `interval_spread_bound` is
proved as a step from `Sawtooth`'s `legendre_count`, taken as a named
hypothesis; `RNSSolutions/Assemble.lean` plugs in the finished proof.
-/

namespace RNS.SpreadBounds

open RNS.Sawtooth

/-- The multiples of a number in a stretch of length `L` number the length
divided by it (rounded down), or one more. -/
private theorem window_bounds (x L d : Nat) :
    ((L / d : Nat) : Int) ≤ (((x + L) / d : Nat) : Int) - ((x / d : Nat) : Int) ∧
      (((x + L) / d : Nat) : Int) - ((x / d : Nat) : Int) ≤ ((L / d : Nat) : Int) + 1 := by
  have h1 := Nat.add_div_le_add_div x L d
  have h2 := Nat.add_div_le_div_add_div_add_one x L d
  constructor
  · have : ((x / d + L / d : Nat) : Int) ≤ (((x + L) / d : Nat) : Int) := by exact_mod_cast h1
    push_cast at this
    linarith
  · have : (((x + L) / d : Nat) : Int) ≤ ((x / d + L / d + 1 : Nat) : Int) := by
      exact_mod_cast h2
    push_cast at this
    linarith

/-- A sign times a number between -1 and 1 is at most 1. -/
private theorem signed_le_one (n : Nat) (g : Int) (hlo : -1 ≤ g) (hhi : g ≤ 1) :
    (-1 : Int) ^ n * g ≤ 1 := by
  rcases neg_one_pow_eq_or Int n with h | h
  · rw [h]
    linarith
  · rw [h]
    linarith

/-- **The spread bound**, as a step from Legendre's count. -/
theorem interval_spread_bound_step (hL : legendre_count) : interval_spread_bound := by
  intro W x y L hW
  have key : ∀ S ∈ W.powerset,
      (-1 : Int) ^ S.card * ((((x + L) / S.prod id : Nat) : Int) - ((x / S.prod id : Nat) : Int)
        - ((((y + L) / S.prod id : Nat) : Int) - ((y / S.prod id : Nat) : Int))) ≤ 1 := by
    intro S _
    obtain ⟨a1, a2⟩ := window_bounds x L (S.prod id)
    obtain ⟨b1, b2⟩ := window_bounds y L (S.prod id)
    exact signed_le_one _ _ (by linarith) (by linarith)
  have hsum : ((survivors_upto W (x + L)).card : Int) - (survivors_upto W x).card
      - (((survivors_upto W (y + L)).card : Int) - (survivors_upto W y).card)
      = ∑ S ∈ W.powerset, (-1 : Int) ^ S.card *
          ((((x + L) / S.prod id : Nat) : Int) - ((x / S.prod id : Nat) : Int)
            - ((((y + L) / S.prod id : Nat) : Int) - ((y / S.prod id : Nat) : Int))) := by
    rw [hL W (x + L) hW, hL W x hW, hL W (y + L) hW, hL W y hW]
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring
  have hle : ∑ S ∈ W.powerset, (-1 : Int) ^ S.card *
          ((((x + L) / S.prod id : Nat) : Int) - ((x / S.prod id : Nat) : Int)
            - ((((y + L) / S.prod id : Nat) : Int) - ((y / S.prod id : Nat) : Int)))
      ≤ ∑ S ∈ W.powerset, (1 : Int) := Finset.sum_le_sum key
  have hcard : ∑ S ∈ W.powerset, (1 : Int) = 2 ^ W.card := by
    rw [Finset.sum_const, Finset.card_powerset]
    simp
  linarith

end RNS.SpreadBounds
