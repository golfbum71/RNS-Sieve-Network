/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunTwinBound.Conclusions
import Mathlib.Algebra.BigOperators.Ring.Finset            -- `Finset.mul_sum`, `Nat.cast_prod`
import Mathlib.Algebra.Order.BigOperators.Group.Finset     -- `Finset.sum_le_sum`
import Mathlib.Algebra.Ring.Parity                         -- `Even.neg_one_pow`
import Mathlib.Data.Nat.Prime.Basic                        -- `Nat.Prime.dvd_mul`
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Proofs for BrunTwinBound

Imports claims only, never other nodes' proofs. The bound is a step from
`BrunPureSieve.twin_bonferroni_upper`, `BrunTwinCount.twin_multiples_count`
and `BrunTruncation.truncation_error`, taken as named hypotheses; the arrows
are joined in `RNSSolutions/Assemble.lean`. The link to twin primes rests on
no other node.

Idea. Term by term, plus or minus the count of twin multiples of a set of
wheels is at most plus or minus `N` times the product of their twin shares,
plus the number of twin roots, because the count is within that number of
`N` times the product. Summing, the stopped inclusion–exclusion for the
counts is at most `N` times the stopped sum of products of shares plus the
total of the twin roots. At an even stopping point the stopped sum of
products is at most the full product plus the sum over the sets of one more
wheel.
-/

namespace RNS.BrunTwinBound

open RNS.BrunPureSieve RNS.BrunTwinCount RNS.BrunTruncation

/-- The twin roots over the product is the product of the twin shares. -/
theorem twin_g_prod (D : Finset ℕ) :
    ((twin_rho D : ℕ) : ℝ) / ((D.prod id : ℕ) : ℝ) = ∏ p ∈ D, twin_g p := by
  unfold twin_rho twin_g
  rw [Finset.prod_div_distrib, Nat.cast_prod, Nat.cast_prod]
  have e1 : ∏ x ∈ D, (((if x = 2 then 1 else 2 : ℕ)) : ℝ)
      = ∏ x ∈ D, (if x = 2 then (1 : ℝ) else 2) :=
    Finset.prod_congr rfl (fun p _ => by split_ifs <;> simp)
  rw [e1]
  all_goals rfl

theorem twin_g_mem (p : ℕ) (hp : p.Prime) : 0 ≤ twin_g p ∧ twin_g p ≤ 1 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  unfold twin_g
  constructor
  · split_ifs <;> positivity
  · rw [div_le_one (show (0 : ℝ) < (p : ℝ) by linarith)]
    split_ifs <;> linarith

theorem twin_sifted_bound_step (hbon : twin_bonferroni_upper) (hcount : twin_multiples_count)
    (htr : truncation_error) : twin_sifted_bound := by
  intro W N t hW ht
  have hg : ∀ p ∈ W, 0 ≤ twin_g p ∧ twin_g p ≤ 1 := fun p hp => twin_g_mem p (hW p hp)
  have h1 := hbon W N t hW ht
  have h1' : ((sifted W (fun n => n * (n + 2)) N).card : ℝ)
      ≤ ((truncated_count_fn W (fun n => n * (n + 2)) N t : ℤ) : ℝ) := by
    exact_mod_cast h1
  have hT : ((truncated_count_fn W (fun n => n * (n + 2)) N t : ℤ) : ℝ)
      ≤ (N : ℝ) * trunc_prod W twin_g t
        + ∑ D ∈ W.powerset.filter (fun D => D.card ≤ t), ((twin_rho D : ℕ) : ℝ) := by
    unfold truncated_count_fn trunc_prod
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro D hD
    have hDW : D ⊆ W := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
    have hDp : ∀ p ∈ D, p.Prime := fun p hp => hW p (hDW hp)
    have hc := hcount D N hDp
    rw [← twin_g_prod D]
    rw [abs_le] at hc
    rcases neg_one_pow_eq_or ℝ D.card with h | h <;> rw [h] <;> nlinarith [hc.1, hc.2]
  have hE := (htr W twin_g t hg).2
  rw [Even.neg_one_pow ht, one_mul] at hE
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h3 := mul_le_mul_of_nonneg_left
    (show trunc_prod W twin_g t ≤ ∏ p ∈ W, (1 - twin_g p) + esymm_k W twin_g (t + 1) by linarith)
    hN
  linarith

theorem twin_count_le_sifted_holds : twin_count_le_sifted := by
  intro L N
  unfold twin_prime_count
  have hsub : (Finset.Ioc 0 N).filter (fun n => n.Prime ∧ (n + 2).Prime) ⊆
      Finset.range L ∪ sifted (active_primes L) (fun n => n * (n + 2)) N := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnI, hp, hp2⟩ := hn
    rw [Finset.mem_union]
    by_cases hL : n < L
    · left
      exact Finset.mem_range.mpr hL
    · right
      unfold sifted
      rw [Finset.mem_filter]
      refine ⟨hnI, ?_⟩
      intro q hq hdvd
      unfold active_primes at hq
      rw [Finset.mem_filter, Finset.mem_range] at hq
      obtain ⟨hqL, hqp⟩ := hq
      have hdvd' : q ∣ n * (n + 2) := hdvd
      rcases (Nat.Prime.dvd_mul hqp).mp hdvd' with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hqp hp).mp h
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hqp hp2).mp h
        omega
  calc ((Finset.Ioc 0 N).filter (fun n => n.Prime ∧ (n + 2).Prime)).card
      ≤ (Finset.range L ∪ sifted (active_primes L) (fun n => n * (n + 2)) N).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range L).card + (sifted (active_primes L) (fun n => n * (n + 2)) N).card :=
        Finset.card_union_le _ _
    _ = L + (sifted (active_primes L) (fun n => n * (n + 2)) N).card := by
        rw [Finset.card_range]

end RNS.BrunTwinBound

#print axioms RNS.BrunTwinBound.twin_sifted_bound_step
#print axioms RNS.BrunTwinBound.twin_count_le_sifted_holds
