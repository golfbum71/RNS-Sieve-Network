/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.BigOperators.Intervals -- `Finset.sum_Icc_succ_top`
import Mathlib.Data.Nat.ModEq -- `Nat.add_div_le_div_add_div_add_one`
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RNSNetwork.Nodes.Sawtooth.Conclusions
import RNSNetwork.Nodes.SpreadBounds.Conclusions

/-!
# Proofs for SpreadBounds

Imports claims only, never other nodes' proofs. `interval_spread_bound` is
proved as a step from `Sawtooth`'s `legendre_count`, and
`column_imbalance_bound` as a step from `Sawtooth`'s `column_legendre_count`,
each taken as a named hypothesis; `RNSSolutions/Assemble.lean` plugs in the
finished proofs.
-/

namespace RNS.SpreadBounds

open RNS.Sawtooth

/-- The multiples of a number in a stretch of length `L` number the length
divided by it (rounded down), or one more. -/
private theorem window_bounds (x L d : Nat) :
    ((L / d : Nat) : Int) ≤ (((x + L) / d : Nat) : Int) - ((x / d : Nat) : Int) ∧
      (((x + L) / d : Nat) : Int) - ((x / d : Nat) : Int) ≤ ((L / d : Nat) : Int) + 1 := by
  have h1 : x / d + L / d ≤ (x + L) / d := Nat.div_add_div_le_add_div
  have h2 := Nat.add_div_le_div_add_div_add_one x L d
  constructor
  · have : ((x / d + L / d : Nat) : Int) ≤ (((x + L) / d : Nat) : Int) := by exact_mod_cast h1
    simp only [Nat.cast_add] at this
    linarith
  · have : (((x + L) / d : Nat) : Int) ≤ ((x / d + L / d + 1 : Nat) : Int) := by
      exact_mod_cast h2
    simp only [Nat.cast_add, Nat.cast_one] at this
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

/-- From 1 to `X`, the numbers in column `r` (1 or 5) number `X + 6 - r`
divided by 6, rounded down. -/
private theorem class_count (X r : Nat) (hr : r = 1 ∨ r = 5) :
    ((Finset.Icc 1 X).filter (fun m => m % 6 = r)).card = (X + 6 - r) / 6 := by
  induction X with
  | zero => rcases hr with rfl | rfl <;> simp
  | succ X ih =>
    rw [Finset.card_filter, Finset.sum_Icc_succ_top (by omega), ← Finset.card_filter, ih]
    split_ifs with h <;> omega

/-- A prime wheel other than 2 and 3 leaves remainder 1 or 5 on division by 6. -/
private theorem prime_mod_six {q : Nat} (hqp : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    q % 6 = 1 ∨ q % 6 = 5 := by
  have n2 : ¬ 2 ∣ q := fun h => hq2 ((hqp.eq_one_or_self_of_dvd 2 h).resolve_left (by norm_num)).symm
  have n3 : ¬ 3 ∣ q := fun h => hq3 ((hqp.eq_one_or_self_of_dvd 3 h).resolve_left (by norm_num)).symm
  omega

/-- A product of numbers each leaving remainder 1 or 5 on division by 6 does
too. -/
private theorem prod_mod_six (S : Finset Nat) (h : ∀ q ∈ S, q % 6 = 1 ∨ q % 6 = 5) :
    S.prod id % 6 = 1 ∨ S.prod id % 6 = 5 := by
  refine Finset.prod_induction id (fun d => d % 6 = 1 ∨ d % 6 = 5) ?_ ?_ ?_
  · intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> (rw [Nat.mul_mod, ha, hb]; decide)
  · decide
  · intro q hq
    exact h q hq

/-- For a multiplier `d` leaving remainder 1 or 5 on division by 6, the
multipliers from 1 to `X` putting `d`'s multiple in the 6n-1 column and in the
6n+1 column differ by at most one. -/
private theorem column_pair (d X : Nat) (hd : d % 6 = 1 ∨ d % 6 = 5) :
    ((((Finset.Icc 1 X).filter (fun m => (d * m) % 6 = 5)).card : Int)
        - ((Finset.Icc 1 X).filter (fun m => (d * m) % 6 = 1)).card ≤ 1) ∧
      (-1 ≤ (((Finset.Icc 1 X).filter (fun m => (d * m) % 6 = 5)).card : Int)
        - ((Finset.Icc 1 X).filter (fun m => (d * m) % 6 = 1)).card) := by
  have hm := fun m => Nat.mul_mod d m 6
  rcases hd with hd | hd
  · have e5 : (Finset.Icc 1 X).filter (fun m => (d * m) % 6 = 5)
        = (Finset.Icc 1 X).filter (fun m => m % 6 = 5) :=
      Finset.filter_congr (fun m _ => by have := hm m; rw [hd] at this; omega)
    have e1 : (Finset.Icc 1 X).filter (fun m => (d * m) % 6 = 1)
        = (Finset.Icc 1 X).filter (fun m => m % 6 = 1) :=
      Finset.filter_congr (fun m _ => by have := hm m; rw [hd] at this; omega)
    rw [e5, e1, class_count X 5 (Or.inr rfl), class_count X 1 (Or.inl rfl)]
    omega
  · have e5 : (Finset.Icc 1 X).filter (fun m => (d * m) % 6 = 5)
        = (Finset.Icc 1 X).filter (fun m => m % 6 = 1) :=
      Finset.filter_congr (fun m _ => by have := hm m; rw [hd] at this; omega)
    have e1 : (Finset.Icc 1 X).filter (fun m => (d * m) % 6 = 1)
        = (Finset.Icc 1 X).filter (fun m => m % 6 = 5) :=
      Finset.filter_congr (fun m _ => by have := hm m; rw [hd] at this; omega)
    rw [e5, e1, class_count X 5 (Or.inr rfl), class_count X 1 (Or.inl rfl)]
    omega

/-- **The column-imbalance bound**, as a step from the column form of
Legendre's count. -/
theorem column_imbalance_bound_step (hC : column_legendre_count) : column_imbalance_bound := by
  intro W x hW h2 h3
  have hdS : ∀ S ∈ ((W.erase 2).erase 3).powerset, S.prod id % 6 = 1 ∨ S.prod id % 6 = 5 := by
    intro S hS
    refine prod_mod_six S (fun q hq => ?_)
    have hq' := Finset.mem_powerset.mp hS hq
    have hq3 : q ≠ 3 := Finset.ne_of_mem_erase hq'
    have hqW := Finset.mem_of_mem_erase hq'
    exact prime_mod_six (hW q (Finset.mem_of_mem_erase hqW)) (Finset.ne_of_mem_erase hqW) hq3
  have hcard : ((W.erase 2).erase 3).card = W.card - 2 := by
    have h3' : 3 ∈ W.erase 2 := Finset.mem_erase.mpr ⟨by norm_num, h3⟩
    rw [Finset.card_erase_of_mem h3', Finset.card_erase_of_mem h2]
    omega
  have hdiff : ((column_survivors_upto W 5 x).card : Int) - (column_survivors_upto W 1 x).card
      = ∑ S ∈ ((W.erase 2).erase 3).powerset, (-1 : Int) ^ S.card *
          ((((Finset.Icc 1 (x / S.prod id)).filter (fun m => (S.prod id * m) % 6 = 5)).card : Int)
            - ((Finset.Icc 1 (x / S.prod id)).filter (fun m => (S.prod id * m) % 6 = 1)).card) := by
    rw [hC W 5 x hW h2 h3 (Or.inr rfl), hC W 1 x hW h2 h3 (Or.inl rfl)]
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring
  have hup : ∀ S ∈ ((W.erase 2).erase 3).powerset, (-1 : Int) ^ S.card *
      ((((Finset.Icc 1 (x / S.prod id)).filter (fun m => (S.prod id * m) % 6 = 5)).card : Int)
        - ((Finset.Icc 1 (x / S.prod id)).filter (fun m => (S.prod id * m) % 6 = 1)).card) ≤ 1 := by
    intro S hS
    obtain ⟨a1, a2⟩ := column_pair (S.prod id) (x / S.prod id) (hdS S hS)
    exact signed_le_one _ _ a2 a1
  have hlo : ∀ S ∈ ((W.erase 2).erase 3).powerset, (-1 : Int) ^ S.card *
      (-((((Finset.Icc 1 (x / S.prod id)).filter (fun m => (S.prod id * m) % 6 = 5)).card : Int)
        - ((Finset.Icc 1 (x / S.prod id)).filter (fun m => (S.prod id * m) % 6 = 1)).card)) ≤ 1 := by
    intro S hS
    obtain ⟨a1, a2⟩ := column_pair (S.prod id) (x / S.prod id) (hdS S hS)
    exact signed_le_one _ _ (by linarith) (by linarith)
  have hsum1 : ∑ S ∈ ((W.erase 2).erase 3).powerset, (1 : Int) = 2 ^ (W.card - 2) := by
    rw [Finset.sum_const, Finset.card_powerset, hcard]
    simp
  have hU := Finset.sum_le_sum hup
  have hL := Finset.sum_le_sum hlo
  simp only [mul_neg, Finset.sum_neg_distrib] at hL
  constructor <;> linarith

end RNS.SpreadBounds
