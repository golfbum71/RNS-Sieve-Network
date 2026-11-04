/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Topology.Algebra.Order.Field -- `tendsto_inv_nhdsGT_zero`
import Mathlib.Tactic.Positivity
import RNSNetwork.Nodes.Admissibility.Conclusions
import RNSNetwork.Nodes.SingularSeries.Conclusions
import RNSNetwork.Nodes.HardyLittlewood.Conclusions

/-!
# Proof for HardyLittlewood

Imports claims only. The conclusion is proved as a step from
`SingularSeries.hardy_littlewood_constant_pos` (`h_pos`) and
`Admissibility.zero_two_admissible` (`h_adm`). The open conjecture itself is
not assumed by the step: it is the hypothesis of the conclusion.

Tactic proof: from `twinPrimeConjectureImpliesInfiniteTwinPrimes` in the
`HardyLittlewood` repository (already compiled on this Lean version), with
the positivity and admissibility facts supplied by `h_pos` and `h_adm`.

Idea: the predicted main term tends to infinity (the constant is positive and
the bound over its logarithm squared grows without limit); a count
asymptotically equivalent to it must tend to infinity too; but finitely many
twin primes would cap the count.
-/

namespace RNS.HardyLittlewood

private theorem tendsto_natCast_div_log_sq_atTop :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) / (Real.log N) ^ 2) Filter.atTop Filter.atTop := by
  have hreal : Filter.Tendsto (fun x : ℝ => x / (Real.log x) ^ 2) Filter.atTop
      Filter.atTop := by
    have hz : Filter.Tendsto (fun x : ℝ => Real.log x ^ 2 / x) Filter.atTop (nhds 0) := by
      have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
      simpa using h
    have hpos : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ 2 / x ∈ Set.Ioi (0 : ℝ) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : 0 < Real.log x := Real.log_pos hx
      have hxpos : 0 < x := lt_trans one_pos hx
      exact Set.mem_Ioi.mpr (by positivity)
    have hnW : Filter.Tendsto (fun x : ℝ => Real.log x ^ 2 / x) Filter.atTop
        (nhdsWithin 0 (Set.Ioi 0)) := tendsto_nhdsWithin_iff.mpr ⟨hz, hpos⟩
    have hinv := tendsto_inv_nhdsGT_zero.comp hnW
    have heq : ((fun y : ℝ => y⁻¹) ∘ fun x : ℝ => Real.log x ^ 2 / x)
        = fun x : ℝ => x / Real.log x ^ 2 := by
      funext x
      rw [Function.comp_apply, inv_div]
    rwa [heq] at hinv
  exact hreal.comp tendsto_natCast_atTop_atTop

private theorem main_term_tendsto_atTop
    (h_pos : RNS.SingularSeries.hardy_littlewood_constant_pos)
    (T : Finset Nat) (hT : is_admissible T) (hk2 : T.card = 2) :
    Filter.Tendsto (fun N : ℕ => hardy_littlewood_main_term T N) Filter.atTop
      Filter.atTop := by
  have hconst := h_pos T hT (by omega)
  unfold hardy_littlewood_main_term
  rw [hk2]
  have hmain := tendsto_natCast_div_log_sq_atTop.const_mul_atTop hconst
  simp only [← mul_div_assoc] at hmain
  exact hmain

/-- **Step:** positivity of the constant and admissibility of {0, 2} imply that
the Hardy–Littlewood conjecture for the twin pattern would give infinitely
many twin primes. -/
theorem twin_prime_conjecture_implies_infinite_twin_primes_step
    (h_pos : RNS.SingularSeries.hardy_littlewood_constant_pos)
    (h_adm : RNS.Admissibility.zero_two_admissible) :
    twin_prime_conjecture_implies_infinite_twin_primes := by
  unfold twin_prime_conjecture_implies_infinite_twin_primes
  intro h
  by_contra hfin
  rw [Set.not_infinite] at hfin
  unfold hardy_littlewood_conjecture at h
  have hk2 : ({0, 2} : Finset Nat).card = 2 := by decide
  have hmain_atTop := main_term_tendsto_atTop h_pos ({0, 2} : Finset Nat) h_adm hk2
  have hcount_atTop : Filter.Tendsto
      (fun N : ℕ => (actual_tuple_count ({0, 2} : Finset Nat) N : ℝ))
      Filter.atTop Filter.atTop := h.tendsto_atTop_iff.mpr hmain_atTop
  have hev := Filter.tendsto_atTop.mp hcount_atTop ((hfin.toFinset.card : ℝ) + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨B, hB⟩ := hev
  have hBcount : (hfin.toFinset.card : ℝ) + 1 ≤
      (actual_tuple_count ({0, 2} : Finset Nat) B : ℝ) := hB B le_rfl
  have hbound : actual_tuple_count ({0, 2} : Finset Nat) B ≤ hfin.toFinset.card := by
    unfold actual_tuple_count
    apply Finset.card_le_card
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨_, hn2⟩ := hn
    have h0 : (n + 0).Prime := hn2 0 (by decide)
    have h2 : (n + 2).Prime := hn2 2 (by decide)
    rw [Nat.add_zero] at h0
    exact hfin.mem_toFinset.mpr ⟨h0, h2⟩
  have hfinal : (hfin.toFinset.card : ℝ) + 1 ≤ (hfin.toFinset.card : ℝ) := by
    calc (hfin.toFinset.card : ℝ) + 1
        ≤ (actual_tuple_count ({0, 2} : Finset Nat) B : ℝ) := hBcount
      _ ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast hbound
  linarith

end RNS.HardyLittlewood

#print axioms RNS.HardyLittlewood.twin_prime_conjecture_implies_infinite_twin_primes_step
