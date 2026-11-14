/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GapPairs.Conclusions
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset   -- `Finset.prod_le_prod_of_subset_of_one_le₀`
import Mathlib.Algebra.BigOperators.Ring.Finset                  -- `Nat.cast_prod`
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proofs for GapPairs

Draft (2026-11-14): not yet built.

Imports claims only. `pair_factor_le_correction` and
`correction_le_totient_ratio_sq` are proved outright (Mathlib only): a number
over its totient is the product, over its prime factors, of the prime over the
prime minus 1, and the three products are compared wheel by wheel.
`gap_pair_bound` and `goldbach_pair_bound` are steps from
`SelbergTwinRails.selberg_gap_bound` / `selberg_goldbach_bound` and
`pair_factor_le_correction`, taken as named hypotheses; the totient forms take
`correction_le_totient_ratio_sq` as well.
-/

namespace RNS.GapPairs

open RNS.SelbergTwinRails RNS.GapConstant

/-- A number over its totient is the product over its prime factors of
p / (p − 1). -/
private theorem totient_ratio_eq {h : ℕ} (hh : 0 < h) :
    totient_ratio h = ∏ p ∈ h.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hcast : (h.totient : ℝ) * ∏ p ∈ h.primeFactors, (p : ℝ)
      = (h : ℝ) * ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) := by
    have key := congrArg (Nat.cast : ℕ → ℝ) (Nat.totient_mul_prod_primeFactors h)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at key
    rw [key]
    congr 1
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  have hφ : (0 : ℝ) < (h.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hh
  have hB : (0 : ℝ) < ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  unfold totient_ratio
  rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hB.ne']
  linarith [hcast]

private theorem totient_ratio_nonneg (h : ℕ) : 0 ≤ totient_ratio h := by
  unfold totient_ratio
  positivity

/-- p / (p − 2) = (p − 1) / (p − 2) · p / (p − 1). -/
private theorem frac_split {p : ℕ} (hp : 3 ≤ p) :
    (p : ℝ) / ((p : ℝ) - 2) = ((p : ℝ) - 1) / ((p : ℝ) - 2) * ((p : ℝ) / ((p : ℝ) - 1)) := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  rw [div_mul_div_comm, div_eq_div_iff h2.ne' (mul_ne_zero h2.ne' h1.ne')]
  ring

private theorem one_le_corr {p : ℕ} (hp : 3 ≤ p) :
    (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  rw [le_div_iff₀ (by linarith)]
  linarith

private theorem one_le_ratio {p : ℕ} (hp : 2 ≤ p) :
    (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- (p − 1) / (p − 2) ≤ (p / (p − 1))² for p ≥ 3. -/
private theorem corr_le_sq {p : ℕ} (hp : 3 ≤ p) :
    ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  rw [div_pow, div_le_div_iff₀ h2 (pow_pos h1 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h3) (by linarith : (0 : ℝ) ≤ (p : ℝ))]

private theorem three_le_of_mem {h p : ℕ}
    (hp : p ∈ h.primeFactors.filter (fun p => p ≠ 2)) : 3 ≤ p := by
  obtain ⟨hpf, hne⟩ := Finset.mem_filter.mp hp
  have := (Nat.prime_of_mem_primeFactors hpf).two_le
  omega

private theorem five_sub (h : ℕ) :
    h.primeFactors.filter (fun p => 5 ≤ p) ⊆ h.primeFactors.filter (fun p => p ≠ 2) := by
  intro p hp
  obtain ⟨hpf, h5⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpf, by omega⟩

theorem pair_factor_le_correction_holds : pair_factor_le_correction := by
  intro h hh
  rw [totient_ratio_eq hh]
  show (∏ p ∈ h.primeFactors.filter (fun p => 5 ≤ p), (p : ℝ) / ((p : ℝ) - 2)) ≤
    (∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
      ∏ p ∈ h.primeFactors, (p : ℝ) / ((p : ℝ) - 1)
  have hsplit : (∏ p ∈ h.primeFactors.filter (fun p => 5 ≤ p), (p : ℝ) / ((p : ℝ) - 2))
      = (∏ p ∈ h.primeFactors.filter (fun p => 5 ≤ p), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        ∏ p ∈ h.primeFactors.filter (fun p => 5 ≤ p), (p : ℝ) / ((p : ℝ) - 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    exact frac_split (by have := (Finset.mem_filter.mp hp).2; omega)
  have hA : (∏ p ∈ h.primeFactors.filter (fun p => 5 ≤ p), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      ≤ ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) - 1) / ((p : ℝ) - 2) :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (five_sub h)
      (fun p hp => le_trans zero_le_one (one_le_corr (three_le_of_mem (five_sub h hp))))
      (fun p hp _ => one_le_corr (three_le_of_mem hp))
  have hB : (∏ p ∈ h.primeFactors.filter (fun p => 5 ≤ p), (p : ℝ) / ((p : ℝ) - 1))
      ≤ ∏ p ∈ h.primeFactors, (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
      (fun p hp => le_trans zero_le_one
        (one_le_ratio (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le))
      (fun p hp _ => one_le_ratio (Nat.prime_of_mem_primeFactors hp).two_le)
  have hB0 : (0 : ℝ) ≤ ∏ p ∈ h.primeFactors.filter (fun p => 5 ≤ p), (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_nonneg (fun p hp => le_trans zero_le_one
      (one_le_ratio (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le))
  have hA0 : (0 : ℝ) ≤ ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2),
      ((p : ℝ) - 1) / ((p : ℝ) - 2) :=
    Finset.prod_nonneg (fun p hp => le_trans zero_le_one (one_le_corr (three_le_of_mem hp)))
  rw [hsplit]
  exact mul_le_mul hA hB hB0 hA0

theorem correction_le_totient_ratio_sq_holds : correction_le_totient_ratio_sq := by
  intro h hh
  rw [totient_ratio_eq hh, ← Finset.prod_pow]
  show (∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤
    ∏ p ∈ h.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2
  have h1 : (∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      ≤ ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 :=
    Finset.prod_le_prod₀
      (fun p hp => le_trans zero_le_one (one_le_corr (three_le_of_mem hp)))
      (fun p hp => corr_le_sq (three_le_of_mem hp))
  have h2 : (∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2)
      ≤ ∏ p ∈ h.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
      (fun p _ => sq_nonneg _)
      (fun p hp _ => one_le_pow₀ (one_le_ratio (Nat.prime_of_mem_primeFactors hp).two_le))
  exact le_trans h1 h2

/-- Replace the factor in a bound of the shape 40000 · factor · Q. -/
private theorem scale_bound {c a b Q : ℝ} (hQ : 0 ≤ Q) (hab : a ≤ b)
    (hc : c ≤ 40000 * a * Q) : c ≤ 40000 * b * Q := by
  have h1 : 40000 * a * Q ≤ 40000 * b * Q := by
    refine mul_le_mul_of_nonneg_right ?_ hQ
    linarith
  linarith

private theorem quotient_nonneg (N : ℕ) : (0 : ℝ) ≤ (N : ℝ) / Real.log N ^ 2 := by
  positivity

/-- The Selberg factor is at most the cube of the number over its totient. -/
private theorem pair_factor_le_cube (h_pf : pair_factor_le_correction)
    (h_c : correction_le_totient_ratio_sq) {h : ℕ} (hh : 0 < h) :
    pair_factor h ≤ totient_ratio h ^ 3 := by
  have h1 := h_pf h hh
  have h2 := h_c h hh
  have h0 := totient_ratio_nonneg h
  have h3 : odd_divisor_correction h * totient_ratio h ≤ totient_ratio h ^ 2 * totient_ratio h :=
    mul_le_mul_of_nonneg_right h2 h0
  have h4 : totient_ratio h ^ 2 * totient_ratio h = totient_ratio h ^ 3 := by ring
  linarith

theorem gap_pair_bound_step (h_gap : selberg_gap_bound) (h_pf : pair_factor_le_correction) :
    gap_pair_bound := by
  intro h N hh hN
  have h1 := h_gap h N hh hN
  rw [mul_div_assoc] at h1 ⊢
  exact scale_bound (quotient_nonneg N) (h_pf h hh) h1

theorem goldbach_pair_bound_step (h_gold : selberg_goldbach_bound)
    (h_pf : pair_factor_le_correction) : goldbach_pair_bound := by
  intro N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have h1 := h_gold N hN
  rw [mul_div_assoc] at h1 ⊢
  exact scale_bound (quotient_nonneg N) (h_pf N hN0) h1

theorem gap_pair_bound_totient_step (h_gap : selberg_gap_bound)
    (h_pf : pair_factor_le_correction) (h_c : correction_le_totient_ratio_sq) :
    gap_pair_bound_totient := by
  intro h N hh hN
  have h1 := h_gap h N hh hN
  rw [mul_div_assoc] at h1 ⊢
  exact scale_bound (quotient_nonneg N) (pair_factor_le_cube h_pf h_c hh) h1

theorem goldbach_pair_bound_totient_step (h_gold : selberg_goldbach_bound)
    (h_pf : pair_factor_le_correction) (h_c : correction_le_totient_ratio_sq) :
    goldbach_pair_bound_totient := by
  intro N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have h1 := h_gold N hN
  rw [mul_div_assoc] at h1 ⊢
  exact scale_bound (quotient_nonneg N) (pair_factor_le_cube h_pf h_c hN0) h1

end RNS.GapPairs

#print axioms RNS.GapPairs.pair_factor_le_correction_holds
#print axioms RNS.GapPairs.correction_le_totient_ratio_sq_holds
#print axioms RNS.GapPairs.gap_pair_bound_step
#print axioms RNS.GapPairs.goldbach_pair_bound_step
#print axioms RNS.GapPairs.gap_pair_bound_totient_step
#print axioms RNS.GapPairs.goldbach_pair_bound_totient_step
