/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PatternReciprocals.Conclusions
import Mathlib.Algebra.BigOperators.Intervals              -- `Finset.sum_range_add_sum_Ico`
import Mathlib.Algebra.Order.BigOperators.Group.Finset     -- `Finset.sum_le_card_nsmul`
import Mathlib.Analysis.PSeries                            -- `Real.summable_one_div_nat_pow`
import Mathlib.Topology.Algebra.InfiniteSum.Real           -- `summable_of_sum_range_le`
import Mathlib.Topology.Algebra.InfiniteSum.Order          -- `Summable.sum_le_tsum`
import Mathlib.Order.Interval.Finset.Nat                   -- `Nat.card_Ioc`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Proofs for PatternReciprocals

Imports claims only. `summable_of_count_bound` is proved outright (Mathlib only),
by the stretch argument of `BrunTheorem`: the sum up to `2ᴷ` is the sum of the
stretches from `2ᵏ` to `2ᵏ⁺¹`; a stretch adds at most one over `2ᵏ` per position
in it, so at most 2 always, and at most a constant over `(k + 1)²` once `2ᵏ⁺¹`
passes the start of the count bound.

`pattern_count_bound` is a step from `GapPairs.gap_pair_bound_totient`: take two
offsets, the smaller and a larger one; a position fitting the pattern, moved up
by the smaller offset, is the smaller member of a prime pair at the gap between
them. `pattern_reciprocal_summable` joins the two.
-/

namespace RNS.PatternReciprocals

open Classical

theorem reciprocal_nonneg (P : ℕ → Prop) (n : ℕ) : 0 ≤ reciprocal_of P n := by
  unfold reciprocal_of
  split_ifs <;> positivity

theorem reciprocal_zero (P : ℕ → Prop) : reciprocal_of P 0 = 0 := by
  unfold reciprocal_of
  split_ifs <;> simp

/-- The stretch from `2ᵏ` to `2ᵏ⁺¹`. -/
noncomputable def block (P : ℕ → Prop) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), reciprocal_of P n

theorem sum_dyadic (P : ℕ → Prop) (K : ℕ) :
    ∑ n ∈ Finset.range (2 ^ K), reciprocal_of P n = ∑ k ∈ Finset.range K, block P k := by
  induction K with
  | zero => simp [reciprocal_zero]
  | succ K ih =>
    rw [← Finset.sum_range_add_sum_Ico _
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right K 1)),
      ih, Finset.sum_range_succ]
    all_goals rfl

theorem le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem position_count_le (P : ℕ → Prop) (M : ℕ) : (position_count P M : ℝ) ≤ (M : ℝ) := by
  have h : position_count P M ≤ M := by
    unfold position_count
    calc ((Finset.Ioc 0 M).filter P).card ≤ (Finset.Ioc 0 M).card := Finset.card_filter_le _ _
      _ = M := by simp
  exact_mod_cast h

theorem block_le (P : ℕ → Prop) (k : ℕ) :
    block P k ≤ (position_count P (2 ^ (k + 1)) : ℝ) * (1 / 2 ^ k) := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  unfold block reciprocal_of
  rw [← Finset.sum_filter]
  have h1 : ∀ n : ℕ, n ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter P →
      1 / (n : ℝ) ≤ 1 / 2 ^ k := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    have hn1 : (2 : ℝ) ^ k ≤ (n : ℝ) := by exact_mod_cast hn.1.1
    exact one_div_le_one_div_of_le hk hn1
  have h2 := Finset.sum_le_card_nsmul _ _ _ h1
  rw [nsmul_eq_mul] at h2
  have h3 : ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter P).card ≤ position_count P (2 ^ (k + 1)) := by
    unfold position_count
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [Finset.mem_Ioc]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    exact ⟨by omega, hn.2.le⟩
  have h3' : (((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter P).card : ℝ) ≤
      (position_count P (2 ^ (k + 1)) : ℝ) := by exact_mod_cast h3
  have h4 := mul_le_mul_of_nonneg_right h3' (show (0 : ℝ) ≤ 1 / 2 ^ k by positivity)
  linarith

theorem block_le_two (P : ℕ → Prop) (k : ℕ) : block P k ≤ 2 := by
  have h1 := block_le P k
  have h2 := position_count_le P (2 ^ (k + 1))
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ 1 / 2 ^ k by positivity)
  have h4 : ((2 ^ (k + 1) : ℕ) : ℝ) * (1 / 2 ^ k) = 2 := by
    push_cast
    rw [pow_succ]
    field_simp
  linarith

/-- Once `2ᵏ⁺¹` passes the start, a stretch adds at most a constant over `(k + 1)²`. -/
theorem block_le_tail (P : ℕ → Prop) (C N₀ : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ, N₀ ≤ (N : ℝ) → (position_count P N : ℝ) ≤ C * N / Real.log N ^ 2)
    (k : ℕ) (hk : N₀ ≤ ((2 ^ (k + 1) : ℕ) : ℝ)) :
    block P k ≤ 2 * C / Real.log 2 ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
  have h1 := block_le P k
  have h2 := hC (2 ^ (k + 1)) hk
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) = ((k : ℝ) + 1) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog] at h2
  have hpk : (0 : ℝ) < 2 ^ k := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ 1 / 2 ^ k by positivity)
  have h4 : C * ((2 ^ (k + 1) : ℕ) : ℝ) / (((k : ℝ) + 1) * Real.log 2) ^ 2 * (1 / 2 ^ k)
      = 2 * C / Real.log 2 ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    push_cast
    rw [pow_succ]
    field_simp
    try ring
  linarith

theorem summable_of_count_bound_holds : summable_of_count_bound := by
  intro P hP
  obtain ⟨C, N₀, hC⟩ := hP
  have hC' : ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (position_count P N : ℝ) ≤ max C 0 * N / Real.log N ^ 2 := by
    intro N hN
    have h1 := hC N hN
    have h2 : C * N / Real.log N ^ 2 ≤ max C 0 * N / Real.log N ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Nat.cast_nonneg N)
    linarith
  have hC0 : 0 ≤ max C 0 := le_max_right C 0
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = ⌈N₀⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * max C 0 / Real.log 2 ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    positivity
  let g : ℕ → ℝ := fun k => (if k < k₀ then (2 : ℝ) else 0) + D * (1 / (k : ℝ) ^ 2)
  have hpser : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hfin : Summable (fun k : ℕ => if k < k₀ then (2 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.range k₀)
    intro b hb
    rw [Finset.mem_range] at hb
    exact ite_eq_right hb
  have hg : Summable g := hfin.add (hpser.mul_left D)
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    have h1 : (0 : ℝ) ≤ if k < k₀ then (2 : ℝ) else 0 := by split_ifs <;> norm_num
    have h2 : 0 ≤ D * (1 / (k : ℝ) ^ 2) := mul_nonneg hD0 (by positivity)
    exact add_nonneg h1 h2
  have hblock : ∀ k, block P k ≤ g k := by
    intro k
    have h2 : 0 ≤ D * (1 / (k : ℝ) ^ 2) := mul_nonneg hD0 (by positivity)
    by_cases hk : k < k₀
    · show block P k ≤ (if k < k₀ then (2 : ℝ) else 0) + D * (1 / (k : ℝ) ^ 2)
      rw [ite_eq_left hk]
      linarith [block_le_two P k]
    · show block P k ≤ (if k < k₀ then (2 : ℝ) else 0) + D * (1 / (k : ℝ) ^ 2)
      rw [ite_eq_right hk, zero_add]
      have hkk : k₀ ≤ k := by omega
      have hk1 : 1 ≤ k := by omega
      have hceil : N₀ ≤ (⌈N₀⌉₊ : ℝ) := Nat.le_ceil N₀
      have hkR : ((⌈N₀⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
        have : ⌈N₀⌉₊ + 1 ≤ k := by omega
        exact_mod_cast this
      have hpow : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := le_two_pow (k + 1)
      have hpowR : ((k : ℝ) + 1) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hpow
      have hpow' : N₀ ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by linarith
      have ht := block_le_tail P (max C 0) N₀ hC0 hC' k hpow'
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hr : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hkpos.le (by linarith) 2
      have hr' : 1 / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) hr
      have := mul_le_mul_of_nonneg_left hr' hD0
      rw [← hD] at ht
      linarith
  apply summable_of_sum_range_le (reciprocal_nonneg P) (c := ∑' k, g k)
  intro n
  calc ∑ i ∈ Finset.range n, reciprocal_of P i
      ≤ ∑ i ∈ Finset.range (2 ^ n), reciprocal_of P i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_subset_range.mpr (le_two_pow n)
        · intro i _ _
          exact reciprocal_nonneg P i
    _ = ∑ k ∈ Finset.range n, block P k := sum_dyadic P n
    _ ≤ ∑ k ∈ Finset.range n, g k := Finset.sum_le_sum (fun k _ => hblock k)
    _ ≤ ∑' k, g k := hg.sum_le_tsum _ (fun k _ => hg0 k)

/-- A position fitting the pattern, moved up by the smaller offset `u`, is the
smaller member of a prime pair at the gap `v − u`. -/
theorem fits_count_le (H : Finset ℕ) {u v : ℕ} (hu : u ∈ H) (hv : v ∈ H) (huv : u < v)
    (N : ℕ) : position_count (fits H) N ≤ RNS.SelbergTwinRails.gap_pair_count (v - u) (N + u) := by
  unfold position_count RNS.SelbergTwinRails.gap_pair_count
  refine Finset.card_le_card_of_injOn (fun n => n + u) ?_ ?_
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    have hI := Finset.mem_Ioc.mp hn'.1
    have hpu := hn'.2 u hu
    have hpv := hn'.2 v hv
    have he : n + u + (v - u) = n + v := by omega
    refine ⟨⟨by omega, by omega⟩, hpu, ?_⟩
    rw [he]
    exact hpv
  · intro a _ b _ h
    have h' : a + u = b + u := h
    omega

theorem pattern_count_bound_step (h_gap : RNS.GapPairs.gap_pair_bound_totient) :
    pattern_count_bound := by
  intro H hH
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < H.card by omega)
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ H, ∃ v ∈ H, u < v := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact ⟨a, ha, b, hb, h⟩
    · exact ⟨b, hb, a, ha, h⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 40000 * RNS.GapPairs.totient_ratio (v - u) ^ 3 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    unfold RNS.GapPairs.totient_ratio
    positivity
  refine ⟨2 * A, max ((5184 : ℝ) ^ 8) (u : ℝ), ?_⟩
  intro N hN
  have hN1 : (5184 : ℝ) ^ 8 ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hNu : (u : ℝ) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hNpos : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN1
  have hcount := fits_count_le H hu hv huv N
  have hcountR : (position_count (fits H) N : ℝ) ≤
      (RNS.SelbergTwinRails.gap_pair_count (v - u) (N + u) : ℝ) := by exact_mod_cast hcount
  have hNu' : (5184 : ℝ) ^ 8 ≤ ((N + u : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
  have hg := h_gap (v - u) (N + u) (by omega) hNu'
  rw [← hA] at hg
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hNpos
  have hLle : Real.log (N : ℝ) ≤ Real.log ((N + u : ℕ) : ℝ) := by
    apply Real.log_le_log (by linarith)
    push_cast
    linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
  have hsq : Real.log (N : ℝ) ^ 2 ≤ Real.log ((N + u : ℕ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ hL.le hLle 2
  have hinv : 1 / Real.log ((N + u : ℕ) : ℝ) ^ 2 ≤ 1 / Real.log (N : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hsq
  have hnum : A * ((N + u : ℕ) : ℝ) ≤ A * (2 * N) := by
    apply mul_le_mul_of_nonneg_left _ hA0
    push_cast
    linarith
  have hnum0 : 0 ≤ A * (2 * (N : ℝ)) := by positivity
  calc (position_count (fits H) N : ℝ)
      ≤ A * ((N + u : ℕ) : ℝ) / Real.log ((N + u : ℕ) : ℝ) ^ 2 := hcountR.trans hg
    _ = A * ((N + u : ℕ) : ℝ) * (1 / Real.log ((N + u : ℕ) : ℝ) ^ 2) := by ring
    _ ≤ A * (2 * N) * (1 / Real.log (N : ℝ) ^ 2) :=
        mul_le_mul hnum hinv (by positivity) hnum0
    _ = 2 * A * N / Real.log N ^ 2 := by ring

theorem pattern_reciprocal_summable_step (h_sum : summable_of_count_bound)
    (h_count : pattern_count_bound) : pattern_reciprocal_summable := by
  intro H hH
  exact h_sum (fits H) (h_count H hH)

end RNS.PatternReciprocals

#print axioms RNS.PatternReciprocals.summable_of_count_bound_holds
#print axioms RNS.PatternReciprocals.pattern_count_bound_step
#print axioms RNS.PatternReciprocals.pattern_reciprocal_summable_step
