/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunTheorem.Conclusions
import Mathlib.Algebra.BigOperators.Intervals              -- `Finset.sum_range_add_sum_Ico`
import Mathlib.Algebra.Order.BigOperators.Group.Finset     -- `Finset.sum_le_card_nsmul`
import Mathlib.Algebra.Order.Ring.Pow                      -- `one_add_mul_le_pow`
import Mathlib.Analysis.PSeries                            -- `Real.summable_one_div_nat_rpow`
import Mathlib.Topology.Algebra.InfiniteSum.Real           -- `summable_of_sum_range_le`
import Mathlib.Topology.Algebra.InfiniteSum.Order          -- `Summable.sum_le_tsum`
import Mathlib.Order.Interval.Finset.Nat                   -- `Nat.card_Ioc`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Proofs for BrunTheorem

Built clean by `lake build RNSSolutions` on 2026-11-06; `#print axioms` shows only
the standard three.

Imports claims only. The theorem is a step from `BrunAnalytic.twin_prime_count_bound`,
taken as a named hypothesis; the arrow is joined in `RNSSolutions/Assemble.lean`.

Idea. The sum up to `2ᴷ` is the sum of the stretches from `2ᵏ` to `2ᵏ⁺¹` for
`k` below `K` (position 0 adds nothing). A stretch adds at most `2 / 2ᵏ` per
twin pair in it, and its twin pairs are among those up to `2ᵏ⁺¹`. So a
stretch adds at most 4 always, and at most a constant over `k` to the three
halves once `2ᵏ⁺¹` passes the starting point of `BrunAnalytic`'s bound. Those
bounds have a finite total, so the partial sums stay below it.
-/

namespace RNS.BrunTheorem

open RNS.BrunTwinBound RNS.BrunAnalytic

theorem twin_reciprocal_nonneg (n : ℕ) : 0 ≤ twin_reciprocal n := by
  unfold twin_reciprocal
  split_ifs <;> positivity

theorem twin_reciprocal_zero : twin_reciprocal 0 = 0 := by
  unfold twin_reciprocal
  simp [Nat.not_prime_zero]

/-- The stretch from `2ᵏ` to `2ᵏ⁺¹`. -/
noncomputable def block (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), twin_reciprocal n

theorem sum_dyadic (K : ℕ) :
    ∑ n ∈ Finset.range (2 ^ K), twin_reciprocal n = ∑ k ∈ Finset.range K, block k := by
  induction K with
  | zero => simp [twin_reciprocal_zero]
  | succ K ih =>
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right K 1)),
      ih, Finset.sum_range_succ]
    all_goals rfl

theorem le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem twin_prime_count_le (M : ℕ) : (twin_prime_count M : ℝ) ≤ (M : ℝ) := by
  have h : twin_prime_count M ≤ M := by
    unfold twin_prime_count
    calc ((Finset.Ioc 0 M).filter (fun n => n.Prime ∧ (n + 2).Prime)).card
        ≤ (Finset.Ioc 0 M).card := Finset.card_filter_le _ _
      _ = M := by simp
  exact_mod_cast h

theorem block_le (k : ℕ) : block k ≤ (twin_prime_count (2 ^ (k + 1)) : ℝ) * (2 / 2 ^ k) := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  unfold block twin_reciprocal
  rw [← Finset.sum_filter]
  have h1 : ∀ n : ℕ, n ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => n.Prime ∧ (n + 2).Prime) →
      1 / (n : ℝ) + 1 / ((n : ℝ) + 2) ≤ 2 / 2 ^ k := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    have hn1 : (2 : ℝ) ^ k ≤ (n : ℝ) := by exact_mod_cast hn.1.1
    have ha : 1 / (n : ℝ) ≤ 1 / 2 ^ k := one_div_le_one_div_of_le hk hn1
    have hb : 1 / ((n : ℝ) + 2) ≤ 1 / 2 ^ k := one_div_le_one_div_of_le hk (by linarith)
    have hc : (2 : ℝ) / 2 ^ k = 1 / 2 ^ k + 1 / 2 ^ k := by ring
    linarith
  have h2 := Finset.sum_le_card_nsmul _ _ _ h1
  rw [nsmul_eq_mul] at h2
  have h3 : ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => n.Prime ∧ (n + 2).Prime)).card
      ≤ twin_prime_count (2 ^ (k + 1)) := by
    unfold twin_prime_count
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [Finset.mem_Ioc]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    exact ⟨by omega, hn.2.le⟩
  have h3' : (((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
      (fun n => n.Prime ∧ (n + 2).Prime)).card : ℝ) ≤ (twin_prime_count (2 ^ (k + 1)) : ℝ) := by
    exact_mod_cast h3
  have h4 := mul_le_mul_of_nonneg_right h3' (show (0 : ℝ) ≤ 2 / 2 ^ k by positivity)
  linarith

theorem block_le_four (k : ℕ) : block k ≤ 4 := by
  have h1 := block_le k
  have h2 := twin_prime_count_le (2 ^ (k + 1))
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ 2 / 2 ^ k by positivity)
  have h4 : ((2 ^ (k + 1) : ℕ) : ℝ) * (2 / 2 ^ k) = 4 := by
    push_cast
    rw [pow_succ]
    field_simp
    try ring
  linarith

/-- Once `2ᵏ⁺¹` passes the starting point, a stretch adds at most a constant
over `(k + 1)` to the three halves. -/
theorem block_le_tail (C N₀ : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (twin_prime_count N : ℝ) ≤ C * N / Real.log N ^ ((3 : ℝ) / 2))
    (k : ℕ) (hk : N₀ ≤ ((2 ^ (k + 1) : ℕ) : ℝ)) :
    block k ≤ 4 * C / Real.log 2 ^ ((3 : ℝ) / 2) * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
  have h1 := block_le k
  have h2 := hC (2 ^ (k + 1)) hk
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) = ((k : ℝ) + 1) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    try ring
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsplit : Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) ^ ((3 : ℝ) / 2)
      = ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) * Real.log 2 ^ ((3 : ℝ) / 2) := by
    rw [hlog, Real.mul_rpow hk1.le hl2.le]
  rw [hsplit] at h2
  have hq : (0 : ℝ) < ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hk1 _
  have hA : (0 : ℝ) < Real.log 2 ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hl2 _
  have hpk : (0 : ℝ) < 2 ^ k := by positivity
  have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ 2 / 2 ^ k by positivity)
  have h4 : C * ((2 ^ (k + 1) : ℕ) : ℝ)
        / (((k : ℝ) + 1) ^ ((3 : ℝ) / 2) * Real.log 2 ^ ((3 : ℝ) / 2)) * (2 / 2 ^ k)
      = 4 * C / Real.log 2 ^ ((3 : ℝ) / 2) * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
    push_cast
    rw [pow_succ]
    field_simp
    try ring
  linarith

theorem brun_theorem_step (h : twin_prime_count_bound) : brun_theorem := by
  obtain ⟨C, N₀, hC⟩ := h
  -- use a nonnegative constant
  have hC' : ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (twin_prime_count N : ℝ) ≤ max C 0 * N / Real.log N ^ ((3 : ℝ) / 2) := by
    intro N hN
    have h1 := hC N hN
    have h2 : C * N / Real.log N ^ ((3 : ℝ) / 2) ≤ max C 0 * N / Real.log N ^ ((3 : ℝ) / 2) := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
      exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Nat.cast_nonneg N)
    linarith
  have hC0 : 0 ≤ max C 0 := le_max_right C 0
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = ⌈N₀⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 4 * max C 0 / Real.log 2 ^ ((3 : ℝ) / 2) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hD]
    positivity
  -- the majorant
  let g : ℕ → ℝ := fun k => (if k < k₀ then (4 : ℝ) else 0) + D * (1 / (k : ℝ) ^ ((3 : ℝ) / 2))
  have hpser : Summable (fun k : ℕ => 1 / (k : ℝ) ^ ((3 : ℝ) / 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hfin : Summable (fun k : ℕ => if k < k₀ then (4 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.range k₀)
    intro b hb
    rw [Finset.mem_range] at hb
    exact if_neg hb
  have hg : Summable g := hfin.add (hpser.mul_left D)
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    have h1 : (0 : ℝ) ≤ if k < k₀ then (4 : ℝ) else 0 := by split_ifs <;> norm_num
    have h2 : 0 ≤ D * (1 / (k : ℝ) ^ ((3 : ℝ) / 2)) :=
      mul_nonneg hD0 (by have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) k) ((3 : ℝ) / 2); positivity)
    exact add_nonneg h1 h2
  have hblock : ∀ k, block k ≤ g k := by
    intro k
    have h2 : 0 ≤ D * (1 / (k : ℝ) ^ ((3 : ℝ) / 2)) :=
      mul_nonneg hD0 (by have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) k) ((3 : ℝ) / 2); positivity)
    by_cases hk : k < k₀
    · show block k ≤ (if k < k₀ then (4 : ℝ) else 0) + D * (1 / (k : ℝ) ^ ((3 : ℝ) / 2))
      rw [if_pos hk]
      linarith [block_le_four k]
    · show block k ≤ (if k < k₀ then (4 : ℝ) else 0) + D * (1 / (k : ℝ) ^ ((3 : ℝ) / 2))
      rw [if_neg hk, zero_add]
      have hkk : k₀ ≤ k := by omega
      have hk1 : 1 ≤ k := by omega
      -- `2ᵏ⁺¹` is past the starting point
      have hceil : N₀ ≤ (⌈N₀⌉₊ : ℝ) := Nat.le_ceil N₀
      have hkR : ((⌈N₀⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
        have : ⌈N₀⌉₊ + 1 ≤ k := by omega
        exact_mod_cast this
      have hpow : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := le_two_pow (k + 1)
      have hpowR : ((k : ℝ) + 1) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hpow
      have hpow' : N₀ ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by linarith
      have ht := block_le_tail (max C 0) N₀ hC0 hC' k hpow'
      -- `1 / (k + 1)^(3/2) ≤ 1 / k^(3/2)`
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hr : (k : ℝ) ^ ((3 : ℝ) / 2) ≤ ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hkpos.le (by linarith) (by norm_num)
      have hr' : 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ 1 / (k : ℝ) ^ ((3 : ℝ) / 2) :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hkpos _) hr
      have := mul_le_mul_of_nonneg_left hr' hD0
      rw [← hD] at ht
      linarith
  apply summable_of_sum_range_le twin_reciprocal_nonneg (c := ∑' k, g k)
  intro n
  calc ∑ i ∈ Finset.range n, twin_reciprocal i
      ≤ ∑ i ∈ Finset.range (2 ^ n), twin_reciprocal i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_subset_range.mpr (le_two_pow n)
        · intro i _ _
          exact twin_reciprocal_nonneg i
    _ = ∑ k ∈ Finset.range n, block k := sum_dyadic n
    _ ≤ ∑ k ∈ Finset.range n, g k := Finset.sum_le_sum (fun k _ => hblock k)
    _ ≤ ∑' k, g k := hg.sum_le_tsum _ (fun k _ => hg0 k)

end RNS.BrunTheorem

#print axioms RNS.BrunTheorem.brun_theorem_step
