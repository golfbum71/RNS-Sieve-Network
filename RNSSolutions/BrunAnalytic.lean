/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunAnalytic.Conclusions
import RNSNetwork.Nodes.SurvivorCount.Conclusions
import RNSNetwork.Nodes.ShareBounds.Conclusions
import RNSNetwork.Nodes.BrunTruncation.Conclusions
import RNSNetwork.Nodes.MertensSecond.Conclusions
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset -- `Finset.sum_powerset_insert`
import Mathlib.Algebra.BigOperators.Ring.Finset            -- `Nat.cast_prod`, `Finset.mul_sum`
import Mathlib.Algebra.Order.BigOperators.Ring.Finset      -- `Finset.prod_nonneg`
import Mathlib.Analysis.Complex.ExponentialBounds          -- `Real.exp_one_lt_d9`
import Mathlib.Analysis.SpecialFunctions.Pow.Real          -- `Real.rpow_mul`
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Proofs for BrunAnalytic

Imports claims only, never other nodes' proofs. Both claims are steps; the
arrows are joined in `RNSSolutions/Assemble.lean`.

Idea for the count. Fix `N` from some point on and let `u` be the eighth root
of its logarithm, so the logarithm of `N` is `u⁸`. Take the wheels below `L`,
the first whole number at least `e` to the `u⁶`, and stop at `t`, twice a whole
number a little above `23 u`. The four parts of the bound:

* the positions below `L`: `L` is at most `e` to the `u⁶ + 1`, far below `N`
  over `u¹²`;
* the product: at most twice one over the logarithm of `L`, squared, which is
  at most `2 / u¹²`;
* the truncation error: the total twin share of the wheels is at most twice
  the sum of the prime reciprocals, so at most a constant plus `12 log u`
  (Mertens' second theorem). The power bound turns the error into at most
  `e` to the (`e` times the total share, minus `t + 1`), and `t + 1` is large
  enough to make that at most `1 / u¹²`;
* the twin roots over the sets used: at most (one plus twice the number of
  wheels) to the `t`, whose logarithm is about `46 u` times `u⁶`, far below
  `u⁸`, the logarithm of `N`.

Adding up gives at most `5 N / u¹²`, and `u¹²` is the logarithm of `N` to the
three halves.
-/

namespace RNS.BrunAnalytic

open RNS.BrunPureSieve RNS.BrunTwinCount RNS.BrunTruncation RNS.BrunTwinBound
open RNS.SurvivorCount RNS.ShareBounds RNS.MertensSecond

/-! ### The twin product -/

theorem twin_share_eq_twin_g (L : ℕ) (hsc : twin_survivor_count) :
    ((wheel_survivors L).card : ℝ) / (primorial_modulus L : ℝ)
      = ∏ p ∈ active_primes L, (1 - twin_g p) := by
  rw [hsc L]
  unfold primorial_modulus
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  have hqp : q.Prime := (Finset.mem_filter.mp hq).2
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  have hid : ((id q : ℕ) : ℝ) = (q : ℝ) := rfl
  rw [hid]
  unfold twin_g
  split_ifs with h
  · subst h
    norm_num
  · rw [Nat.cast_sub hqp.two_le, sub_div, div_self hq0]
    norm_num

theorem twin_product_bound_step (hsc : twin_survivor_count)
    (hsb : twin_share_le_two_inv_log_sq) : twin_product_bound := by
  intro L hL
  rw [← twin_share_eq_twin_g L hsc]
  exact hsb L hL

/-! ### Small facts about the twin shares -/

theorem twin_g_bounds (p : ℕ) (hp : p.Prime) : 0 ≤ twin_g p ∧ twin_g p ≤ 2 * (1 / (p : ℝ)) := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  unfold twin_g
  constructor
  · split_ifs <;> positivity
  · split_ifs
    · linarith
    · exact le_of_eq (mul_one_div (2 : ℝ) (p : ℝ)).symm

theorem twin_g_le_one (p : ℕ) (hp : p.Prime) : twin_g p ≤ 1 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  unfold twin_g
  rw [div_le_one (show (0 : ℝ) < (p : ℝ) by linarith)]
  split_ifs <;> linarith

/-! ### The twin roots over the sets used -/

theorem bounded_sets_ite (W : Finset ℕ) (y : ℕ → ℝ) (t : ℕ) :
    ∑ D ∈ W.powerset.filter (fun D => D.card ≤ t), ∏ p ∈ D, y p
      = ∑ D ∈ W.powerset, if D.card ≤ t then ∏ p ∈ D, y p else 0 := by
  rw [Finset.sum_filter]

theorem bounded_sets_zero (W : Finset ℕ) (y : ℕ → ℝ) :
    ∑ D ∈ W.powerset.filter (fun D => D.card ≤ 0), ∏ p ∈ D, y p = 1 := by
  have h : W.powerset.filter (fun D => D.card ≤ 0) = {∅} := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton, Nat.le_zero,
      Finset.card_eq_zero]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨Finset.empty_subset _, rfl⟩
  rw [h, Finset.sum_singleton, Finset.prod_empty]

theorem bounded_sets_insert (s : Finset ℕ) (a : ℕ) (ha : a ∉ s) (y : ℕ → ℝ) (t : ℕ) :
    ∑ D ∈ (insert a s).powerset.filter (fun D => D.card ≤ t + 1), ∏ p ∈ D, y p
      = ∑ D ∈ s.powerset.filter (fun D => D.card ≤ t + 1), ∏ p ∈ D, y p
        + y a * ∑ D ∈ s.powerset.filter (fun D => D.card ≤ t), ∏ p ∈ D, y p := by
  rw [bounded_sets_ite, bounded_sets_ite, bounded_sets_ite, Finset.sum_powerset_insert ha,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  have haD : a ∉ D := fun h => ha (Finset.mem_powerset.mp hD h)
  rw [Finset.card_insert_of_notMem haD, Finset.prod_insert haD]
  by_cases h : D.card ≤ t
  · rw [if_pos (show D.card + 1 ≤ t + 1 by omega), if_pos h]
  · rw [if_neg (show ¬ (D.card + 1 ≤ t + 1) by omega), if_neg h]
    ring

theorem bounded_sets_sum (y : ℕ → ℝ) (W : Finset ℕ) : (∀ p ∈ W, 0 ≤ y p) → ∀ t : ℕ,
    ∑ D ∈ W.powerset.filter (fun D => D.card ≤ t), ∏ p ∈ D, y p ≤ (1 + ∑ p ∈ W, y p) ^ t := by
  induction W using Finset.induction_on with
  | empty =>
    intro _ t
    rw [Finset.sum_empty, add_zero, one_pow, Finset.powerset_empty]
    rw [Finset.sum_filter, Finset.sum_singleton]
    simp
  | insert a s ha ih =>
    intro hy t
    have hys : ∀ p ∈ s, 0 ≤ y p := fun p hp => hy p (Finset.mem_insert_of_mem hp)
    have hya : 0 ≤ y a := hy a (Finset.mem_insert_self a s)
    have hY : 0 ≤ ∑ p ∈ s, y p := Finset.sum_nonneg hys
    cases t with
    | zero =>
      rw [bounded_sets_zero, pow_zero]
    | succ t =>
      rw [bounded_sets_insert s a ha y t, Finset.sum_insert ha]
      have h1 := ih hys (t + 1)
      have h2 := ih hys t
      have hb : 0 ≤ 1 + ∑ p ∈ s, y p := by linarith
      have hpow : (1 + ∑ p ∈ s, y p) ^ t ≤ (1 + (y a + ∑ p ∈ s, y p)) ^ t :=
        pow_le_pow_left₀ hb (by linarith) t
      have h3 := mul_le_mul_of_nonneg_left h2 hya
      have e1 : (1 + (y a + ∑ p ∈ s, y p)) ^ (t + 1)
          = (1 + (y a + ∑ p ∈ s, y p)) ^ t * (1 + (y a + ∑ p ∈ s, y p)) := pow_succ _ _
      have e2 : (1 + ∑ p ∈ s, y p) ^ (t + 1) = (1 + ∑ p ∈ s, y p) ^ t * (1 + ∑ p ∈ s, y p) :=
        pow_succ _ _
      rw [e2] at h1
      rw [e1]
      have h4 := mul_le_mul_of_nonneg_right hpow hb
      have h5 := mul_le_mul_of_nonneg_left hpow hya
      nlinarith [h1, h3, h4, h5]

/-! ### The truncation error as an exponential -/

theorem pow_div_fact_le (S : ℝ) (hS : 0 ≤ S) (n : ℕ) :
    S ^ n / (n.factorial : ℝ) ≤ Real.exp (Real.exp 1 * S - n) := by
  have h := Real.pow_div_factorial_le_exp _ (mul_nonneg (Real.exp_pos 1).le hS) n
  rw [mul_pow] at h
  have he : (0 : ℝ) < Real.exp 1 ^ n := pow_pos (Real.exp_pos 1) n
  have hn : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [Real.exp_sub, hn, le_div_iff₀ he]
  calc S ^ n / (n.factorial : ℝ) * Real.exp 1 ^ n
      = Real.exp 1 ^ n * S ^ n / (n.factorial : ℝ) := by ring
    _ ≤ Real.exp (Real.exp 1 * S) := h

theorem exp_neg_twelve_log (u : ℝ) (hu : 0 < u) :
    Real.exp (-(12 * Real.log u)) = 1 / u ^ 12 := by
  have h : Real.exp (12 * Real.log u) = u ^ 12 := by
    rw [show (12 : ℝ) * Real.log u = Real.log (u ^ 12) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hu 12)]
  rw [Real.exp_neg, h, one_div]

/-! ### The polynomial inequality behind the choice -/

theorem poly_bound (u K₂ : ℝ) (hK : 0 ≤ K₂) (hu : 196 + 4 * K₂ ≤ u) :
    (46 * u + K₂) * (u ^ 6 + 3) + 12 * u ≤ u ^ 8 := by
  have hu1 : 1 ≤ u := by linarith
  have ha : 1 ≤ u ^ 6 := one_le_pow₀ hu1
  have h1 : (46 * u + K₂) * (u ^ 6 + 3) ≤ (46 * u + K₂ * u) * (4 * u ^ 6) := by
    apply mul_le_mul
    · nlinarith
    · linarith
    · linarith
    · nlinarith
  have h2 : 12 * u ≤ 12 * u * u ^ 6 := by nlinarith
  have h3 : (46 * u + K₂ * u) * (4 * u ^ 6) + 12 * u * u ^ 6 = (196 + 4 * K₂) * (u * u ^ 6) := by
    ring
  have h4 : (196 + 4 * K₂) * (u * u ^ 6) ≤ u * (u * u ^ 6) := by
    apply mul_le_mul_of_nonneg_right hu
    exact mul_nonneg (by linarith) (by linarith)
  have h5 : u * (u * u ^ 6) = u ^ 8 := by ring
  linarith

theorem small_power_bound (u K₂ : ℝ) (hK : 0 ≤ K₂) (hu : 196 + 4 * K₂ ≤ u)
    (hlogu : Real.log u ≤ u) : u ^ 6 + 1 + 12 * Real.log u ≤ u ^ 8 := by
  have h1 := poly_bound u K₂ hK hu
  have h2 : 0 ≤ (46 * u + K₂ - 1) * (u ^ 6 + 3) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [h1, h2]

/-! ### The count -/

set_option maxHeartbeats 1000000 in
theorem twin_core (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) ≤ Real.log (Real.log x) + B)
    (hsb : twin_sifted_bound) (hcl : twin_count_le_sifted) (hes : esymm_power_bound)
    (hpb : twin_product_bound)
    (K : ℕ) (hK3 : 3 * (2 + 2 * B) ≤ (K : ℝ))
    (u : ℝ) (hu : 204 + 8 * (K : ℝ) ≤ u) (N : ℕ) (hN : Real.log N = u ^ 8) :
    (twin_prime_count N : ℝ) ≤ 5 * (N * (1 / u ^ 12)) := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hlogu : Real.log u ≤ u := by linarith [Real.log_le_sub_one_of_pos hu0]
  -- `N` is `e` to the `u⁸`
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hN
      have : 0 < u ^ 8 := pow_pos hu0 8
      linarith
    · exact_mod_cast h
  have hNexp : Real.exp (u ^ 8) = N := by rw [← hN, Real.exp_log hNpos]
  have hu12pos : (0 : ℝ) < u ^ 12 := pow_pos hu0 12
  have hu6pos : (0 : ℝ) < u ^ 6 := pow_pos hu0 6
  -- the polynomial inequality
  have hpoly := poly_bound u (2 * K + 2) (by linarith) (by linarith)
  -- the largest wheel: `L` is the first whole number at least `e` to the `u⁶`
  have hlam1 : 1 ≤ u ^ 6 := one_le_pow₀ hu1
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌈Real.exp (u ^ 6)⌉₊ := ⟨_, rfl⟩
  have hL1 : Real.exp (u ^ 6) ≤ (L : ℝ) := by rw [hLdef]; exact Nat.le_ceil _
  have hL2 : (L : ℝ) < Real.exp (u ^ 6) + 1 := by
    rw [hLdef]; exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hexp1 : Real.exp 1 ≤ Real.exp (u ^ 6) := Real.exp_le_exp.mpr hlam1
  have hL2' : (2 : ℝ) ≤ (L : ℝ) := by linarith
  have hL2n : 2 ≤ L := by exact_mod_cast hL2'
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hlogL1 : u ^ 6 ≤ Real.log L := by
    rw [← Real.log_exp (u ^ 6)]
    exact Real.log_le_log (Real.exp_pos _) hL1
  have hLexp : (L : ℝ) ≤ Real.exp (u ^ 6 + 1) := by
    rw [Real.exp_add]
    have h1 := mul_le_mul_of_nonneg_left he2 (Real.exp_pos (u ^ 6)).le
    linarith
  have hlogL2 : Real.log L ≤ u ^ 6 + 1 := by
    calc Real.log L ≤ Real.log (Real.exp (u ^ 6 + 1)) := Real.log_le_log hLpos hLexp
      _ = u ^ 6 + 1 := Real.log_exp _
  -- the wheels
  have hWp : ∀ q ∈ active_primes L, q.Prime := fun q hq => (Finset.mem_filter.mp hq).2
  have hWcard : ((active_primes L).card : ℝ) ≤ (L : ℝ) := by
    have : (active_primes L).card ≤ L :=
      calc (active_primes L).card ≤ (Finset.range L).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = L := Finset.card_range L
    exact_mod_cast this
  -- the total twin share
  have hS0 : 0 ≤ ∑ p ∈ active_primes L, twin_g p :=
    Finset.sum_nonneg (fun p hp => (twin_g_bounds p (hWp p hp)).1)
  have hSle : ∑ p ∈ active_primes L, twin_g p
      ≤ 2 * ∑ p ∈ Finset.Ioc 0 ⌊(L : ℝ)⌋₊ with p.Prime, (1 : ℝ) / p := by
    rw [Nat.floor_natCast, Finset.mul_sum]
    calc ∑ p ∈ active_primes L, twin_g p ≤ ∑ p ∈ active_primes L, 2 * ((1 : ℝ) / p) :=
          Finset.sum_le_sum (fun p hp => (twin_g_bounds p (hWp p hp)).2)
      _ ≤ ∑ p ∈ Finset.Ioc 0 L with p.Prime, 2 * ((1 : ℝ) / p) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            unfold active_primes at hp
            rw [Finset.mem_filter, Finset.mem_range] at hp
            rw [Finset.mem_filter, Finset.mem_Ioc]
            exact ⟨⟨hp.2.pos, hp.1.le⟩, hp.2⟩
          · intro p _ _
            positivity
  have hloglog : Real.log (Real.log L) ≤ Real.log 2 + 6 * Real.log u := by
    have h1 : Real.log (Real.log L) ≤ Real.log (2 * u ^ 6) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hu6pos.ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlog2 : Real.log 2 ≤ 1 := (Real.log_two_lt_d9.trans (by norm_num)).le
  have hSB : ∑ p ∈ active_primes L, twin_g p ≤ 12 * Real.log u + (2 + 2 * B) := by
    have := hB (L : ℝ) hL2'
    linarith
  -- the stopping point
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈23 * u⌉₊ + K := ⟨_, rfl⟩
  have hc1 : 23 * u ≤ (⌈23 * u⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈23 * u⌉₊ : ℝ) < 23 * u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hmR : (m : ℝ) = (⌈23 * u⌉₊ : ℝ) + K := by rw [hmdef]; push_cast; ring
  have ht : Even (2 * m) := even_two_mul m
  have htR : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have ht1R : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
  -- part 1: the truncation error
  have hE1 : esymm_k (active_primes L) twin_g (2 * m + 1) ≤ 1 / u ^ 12 := by
    have h1 := hes (active_primes L) twin_g (2 * m + 1)
      (fun p hp => (twin_g_bounds p (hWp p hp)).1)
    have h2 := pow_div_fact_le (∑ p ∈ active_primes L, twin_g p) hS0 (2 * m + 1)
    have he : Real.exp 1 ≤ 11 / 4 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have h3 : Real.exp 1 * ∑ p ∈ active_primes L, twin_g p
        ≤ 11 / 4 * (12 * Real.log u + (2 + 2 * B)) := by
      calc Real.exp 1 * ∑ p ∈ active_primes L, twin_g p
          ≤ Real.exp 1 * (12 * Real.log u + (2 + 2 * B)) :=
            mul_le_mul_of_nonneg_left hSB (Real.exp_pos 1).le
        _ ≤ 11 / 4 * (12 * Real.log u + (2 + 2 * B)) :=
            mul_le_mul_of_nonneg_right he (by linarith)
    have h4 : Real.exp 1 * ∑ p ∈ active_primes L, twin_g p - ((2 * m + 1 : ℕ) : ℝ)
        ≤ -(12 * Real.log u) := by
      rw [ht1R, hmR]
      linarith
    have h5 : Real.exp (Real.exp 1 * ∑ p ∈ active_primes L, twin_g p - ((2 * m + 1 : ℕ) : ℝ))
        ≤ Real.exp (-(12 * Real.log u)) := Real.exp_le_exp.mpr h4
    rw [exp_neg_twelve_log u hu0] at h5
    linarith
  -- part 2: the product
  have hP : ∏ p ∈ active_primes L, (1 - twin_g p) ≤ 2 * (1 / u ^ 12) := by
    have h1 := hpb L hL2n
    have hlogLpos : 0 < Real.log L := by linarith
    have h2 : 1 / Real.log L ≤ 1 / u ^ 6 :=
      one_div_le_one_div_of_le hu6pos hlogL1
    have h3 : (1 / Real.log L) ^ 2 ≤ (1 / u ^ 6) ^ 2 :=
      pow_le_pow_left₀ (div_pos one_pos hlogLpos).le h2 2
    have h4 : (1 / u ^ 6) ^ 2 = 1 / u ^ 12 := by ring
    linarith
  -- part 3: the twin roots over the sets used
  have hR : ∑ D ∈ (active_primes L).powerset.filter (fun D => D.card ≤ 2 * m),
      ((twin_rho D : ℕ) : ℝ) ≤ (N : ℝ) * (1 / u ^ 12) := by
    have hrho : ∀ D : Finset ℕ, ((twin_rho D : ℕ) : ℝ) = ∏ p ∈ D, (if p = 2 then (1 : ℝ) else 2) := by
      intro D
      unfold twin_rho
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro p _
      split_ifs <;> simp
    simp only [hrho]
    have hy : ∀ p ∈ active_primes L, (0 : ℝ) ≤ (if p = 2 then (1 : ℝ) else 2) := by
      intro p _
      split_ifs <;> norm_num
    have h1 := bounded_sets_sum (fun p => if p = 2 then (1 : ℝ) else 2) (active_primes L) hy (2 * m)
    have h2 : ∑ p ∈ active_primes L, (if p = 2 then (1 : ℝ) else 2)
        ≤ ∑ p ∈ active_primes L, (2 : ℝ) :=
      Finset.sum_le_sum (fun p _ => by split_ifs <;> norm_num)
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : 1 + ∑ p ∈ active_primes L, (if p = 2 then (1 : ℝ) else 2) ≤ 3 * (L : ℝ) := by
      linarith
    have h30 : 0 ≤ 1 + ∑ p ∈ active_primes L, (if p = 2 then (1 : ℝ) else 2) :=
      by linarith [Finset.sum_nonneg hy]
    have h4 : (1 + ∑ p ∈ active_primes L, (if p = 2 then (1 : ℝ) else 2)) ^ (2 * m)
        ≤ (3 * (L : ℝ)) ^ (2 * m) := pow_le_pow_left₀ h30 h3 _
    -- `(3 L)^t · u¹² ≤ N`
    have h3L : (0 : ℝ) < 3 * (L : ℝ) := by linarith
    have hlog3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
    have hlog3L : Real.log (3 * (L : ℝ)) ≤ u ^ 6 + 3 := by
      rw [Real.log_mul (by norm_num) hLpos.ne']
      linarith
    have hlog3L0 : 0 ≤ Real.log (3 * (L : ℝ)) := Real.log_nonneg (by linarith)
    have htle : ((2 * m : ℕ) : ℝ) ≤ 46 * u + (2 * K + 2) := by
      rw [htR, hmR]
      linarith
    have hprod : ((2 * m : ℕ) : ℝ) * Real.log (3 * (L : ℝ)) ≤ (46 * u + (2 * K + 2)) * (u ^ 6 + 3) :=
      mul_le_mul htle hlog3L hlog3L0 (by linarith)
    have h5 : (3 * (L : ℝ)) ^ (2 * m) * u ^ 12 ≤ (N : ℝ) := by
      have e1 : (3 * (L : ℝ)) ^ (2 * m) = Real.exp (((2 * m : ℕ) : ℝ) * Real.log (3 * (L : ℝ))) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos h3L _)]
      have e2 : u ^ 12 = Real.exp (12 * Real.log u) := by
        rw [show (12 : ℝ) * Real.log u = Real.log (u ^ 12) by rw [Real.log_pow]; norm_num,
          Real.exp_log hu12pos]
      rw [e1, e2, ← Real.exp_add, ← hNexp]
      apply Real.exp_le_exp.mpr
      linarith
    have h6 : (3 * (L : ℝ)) ^ (2 * m) ≤ (N : ℝ) * (1 / u ^ 12) := by
      rw [mul_one_div, le_div_iff₀ hu12pos]
      exact h5
    linarith
  -- part 4: the small positions
  have hLN : (L : ℝ) ≤ (N : ℝ) * (1 / u ^ 12) := by
    rw [mul_one_div, le_div_iff₀ hu12pos]
    have e2 : u ^ 12 = Real.exp (12 * Real.log u) := by
      rw [show (12 : ℝ) * Real.log u = Real.log (u ^ 12) by rw [Real.log_pow]; norm_num,
        Real.exp_log hu12pos]
    have hsmall := small_power_bound u (2 * (K : ℝ) + 2) (by linarith) (by linarith) hlogu
    calc (L : ℝ) * u ^ 12 ≤ Real.exp (u ^ 6 + 1) * u ^ 12 :=
          mul_le_mul_of_nonneg_right hLexp hu12pos.le
      _ = Real.exp (u ^ 6 + 1 + 12 * Real.log u) := by rw [e2, ← Real.exp_add]
      _ ≤ Real.exp (u ^ 8) := Real.exp_le_exp.mpr hsmall
      _ = N := hNexp
  -- adding up
  have hmain := hsb (active_primes L) N (2 * m) hWp ht
  have hlink := hcl L N
  have hlink' : (twin_prime_count N : ℝ)
      ≤ (L : ℝ) + ((sifted (active_primes L) (fun n => n * (n + 2)) N).card : ℝ) := by
    exact_mod_cast hlink
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hPE : ∏ p ∈ active_primes L, (1 - twin_g p) + esymm_k (active_primes L) twin_g (2 * m + 1)
      ≤ 3 * (1 / u ^ 12) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hPE hN0
  have e3 : (N : ℝ) * (3 * (1 / u ^ 12)) = 3 * ((N : ℝ) * (1 / u ^ 12)) := by ring
  linarith

theorem twin_prime_count_bound_step (hsb : twin_sifted_bound) (hcl : twin_count_le_sifted)
    (hes : esymm_power_bound) (hpb : twin_product_bound) (hrec : prime_reciprocal_upper) :
    twin_prime_count_bound := by
  obtain ⟨B, hB0, hB⟩ := hrec
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌈3 * (2 + 2 * B)⌉₊ := ⟨_, rfl⟩
  have hK3 : 3 * (2 + 2 * B) ≤ (K : ℝ) := by rw [hKdef]; exact Nat.le_ceil _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  refine ⟨5, Real.exp ((204 + 8 * (K : ℝ)) ^ 8), fun N hN => ?_⟩
  have hU0 : (0 : ℝ) ≤ 204 + 8 * (K : ℝ) := by linarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN
  have hlogN : (204 + 8 * (K : ℝ)) ^ 8 ≤ Real.log N := by
    rw [← Real.log_exp ((204 + 8 * (K : ℝ)) ^ 8)]
    exact Real.log_le_log (Real.exp_pos _) hN
  have hlog0 : 0 ≤ Real.log N := le_trans (by positivity) hlogN
  have hu8 : (Real.log N ^ ((1 : ℝ) / 8)) ^ 8 = Real.log N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog0]
    norm_num
  have hu12 : (Real.log N ^ ((1 : ℝ) / 8)) ^ 12 = Real.log N ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog0]
    norm_num
  have hu0 : 0 ≤ Real.log N ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hlog0 _
  have huU : 204 + 8 * (K : ℝ) ≤ Real.log N ^ ((1 : ℝ) / 8) := by
    by_contra h
    push_neg at h
    have : (Real.log N ^ ((1 : ℝ) / 8)) ^ 8 < (204 + 8 * (K : ℝ)) ^ 8 :=
      pow_lt_pow_left₀ h hu0 (by norm_num)
    linarith
  have h := twin_core B hB0 hB hsb hcl hes hpb K hK3 (Real.log N ^ ((1 : ℝ) / 8)) huU N hu8.symm
  rw [hu12] at h
  calc (twin_prime_count N : ℝ) ≤ 5 * (N * (1 / Real.log N ^ ((3 : ℝ) / 2))) := h
    _ = 5 * N / Real.log N ^ ((3 : ℝ) / 2) := by ring

end RNS.BrunAnalytic

#print axioms RNS.BrunAnalytic.twin_product_bound_step
#print axioms RNS.BrunAnalytic.twin_prime_count_bound_step
