/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.Field.GeomSum           -- `geom_sum_eq`
import Mathlib.NumberTheory.ArithmeticFunction.Misc -- `ArithmeticFunction.sigma`
import Mathlib.NumberTheory.Harmonic.Bounds     -- `log_add_one_le_harmonic`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RNSNetwork.Nodes.SurvivorCount.Conclusions
import RNSNetwork.Nodes.ShareBounds.Conclusions

/-!
# Proofs for ShareBounds

Imports claims only, never other nodes' proofs. Both claims are proved as
steps from `SurvivorCount`'s `general_survivor_count` and
`twin_survivor_count`, taken as named hypotheses; `RNSSolutions/Assemble.lean`
plugs in the finished proofs.

The harmonic step: every number from 1 to `N` divides the product, over the
primes up to `N`, of each prime to the power `N`. So the sum of their
reciprocals is at most the sum of reciprocals of that product's divisors,
which is the sum of its divisors divided by it. That ratio is a product over
the primes (the divisor sum is multiplicative), and each prime's factor is a
finite geometric sum, at most the prime over the prime minus 1.
-/

namespace RNS.ShareBounds

open RNS.SurvivorCount

/-- The active wheels below `limit` are primes below `limit`. -/
private theorem mem_active {limit q : Nat} (hq : q ∈ active_primes limit) :
    q.Prime ∧ q < limit := by
  have h := Finset.mem_filter.mp hq
  exact ⟨h.2, Finset.mem_range.mp h.1⟩

/-- A finite geometric sum in a prime, divided by its top power, is at most
the prime over the prime minus 1. -/
private theorem geom_factor_le (q N : Nat) (hq : 2 ≤ q) :
    (∑ i ∈ Finset.range (N + 1), (q : Real) ^ i) / (q : Real) ^ N ≤ (q : Real) / ((q : Real) - 1) := by
  have hq' : (2 : Real) ≤ q := by exact_mod_cast hq
  have hq1 : (q : Real) ≠ 1 := by linarith
  have hpos : (0 : Real) < (q : Real) - 1 := by linarith
  have hqN : (0 : Real) < (q : Real) ^ N := by positivity
  rw [geom_sum_eq hq1, div_div, div_le_div_iff₀ (by positivity) hpos]
  have e : (q : Real) * (((q : Real) - 1) * (q : Real) ^ N) = (q : Real) ^ (N + 1) * ((q : Real) - 1) := by
    ring
  nlinarith

/-- **The harmonic sum up to `N` is at most the product, over the primes up to
`N`, of the prime over the prime minus 1.** -/
private theorem harmonic_le_prod (N : Nat) :
    ∑ n ∈ Finset.Icc 1 N, (1 / (n : Real))
      ≤ ∏ q ∈ active_primes (N + 1), ((q : Real) / ((q : Real) - 1)) := by
  have hS : ∀ q ∈ active_primes (N + 1), q.Prime := fun q hq => (mem_active hq).1
  have hM0 : (∏ q ∈ active_primes (N + 1), q ^ N) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (hS q hq).ne_zero
  -- every number from 1 to `N` divides the product of the prime powers
  have hsub : Finset.Icc 1 N ⊆ (∏ q ∈ active_primes (N + 1), q ^ N).divisors := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    refine Nat.mem_divisors.mpr ⟨?_, hM0⟩
    rw [Nat.prod_primeFactors_pow_factorization hn0]
    refine (Finset.prod_dvd_prod_of_dvd _ (fun p => p ^ N) fun p hp => ?_).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_)
    · have := Nat.factorization_lt p hn0
      exact pow_dvd_pow p (by omega)
    · obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
      have := Nat.le_of_dvd (by omega) hpn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩
  -- the reciprocal sum over the divisors is the divisor sum over the number
  have hrecip : ∑ d ∈ (∏ q ∈ active_primes (N + 1), q ^ N).divisors, (1 / (d : Real))
      = ((ArithmeticFunction.sigma 1 (∏ q ∈ active_primes (N + 1), q ^ N) : Nat) : Real)
          / ((∏ q ∈ active_primes (N + 1), q ^ N : Nat) : Real) := by
    rw [← Nat.sum_div_divisors, ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdM := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : Real) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    have hM0' : ((∏ q ∈ active_primes (N + 1), q ^ N : Nat) : Real) ≠ 0 := by exact_mod_cast hM0
    rw [Nat.cast_div hdM hd0]
    field_simp
  -- the divisor sum is multiplicative over the prime powers
  have hsigma : ArithmeticFunction.sigma 1 (∏ q ∈ active_primes (N + 1), q ^ N)
      = ∏ q ∈ active_primes (N + 1), ∑ i ∈ Finset.range (N + 1), q ^ i := by
    rw [ArithmeticFunction.IsMultiplicative.map_prod (fun q => q ^ N)
      ArithmeticFunction.isMultiplicative_sigma _
      (fun x hx y hy hxy => ((Nat.coprime_primes (hS x hx) (hS y hy)).mpr hxy).pow N N)]
    refine Finset.prod_congr rfl (fun q hq => ?_)
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow (hS q hq)]
  calc ∑ n ∈ Finset.Icc 1 N, (1 / (n : Real))
      ≤ ∑ d ∈ (∏ q ∈ active_primes (N + 1), q ^ N).divisors, (1 / (d : Real)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
    _ = ∏ q ∈ active_primes (N + 1),
          ((∑ i ∈ Finset.range (N + 1), (q : Real) ^ i) / (q : Real) ^ N) := by
        rw [hrecip, hsigma, Finset.prod_div_distrib]
        push_cast
        rfl
    _ ≤ ∏ q ∈ active_primes (N + 1), ((q : Real) / ((q : Real) - 1)) := by
        refine Finset.prod_le_prod (fun q _ => by positivity) (fun q hq => ?_)
        exact geom_factor_le q N (hS q hq).two_le

/-- The plain share is the product over the wheels of the wheel size minus 1
over the wheel size. -/
private theorem share_eq_prod (hgen : general_survivor_count) (limit : Nat) :
    ((wheel_survivors_gen {0} limit).card : Real) / (primorial_modulus limit : Real)
      = ∏ q ∈ active_primes limit, (((q : Real) - 1) / q) := by
  have hw : ∀ q, w ({0} : Finset Nat) q = 1 := by intro q; simp [w]
  rw [hgen {0} limit, primorial_modulus]
  simp only [hw]
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  rw [Nat.cast_sub (mem_active hq).1.one_le]
  simp

/-- The logarithm of the bound is at most the product of the wheel size over
the wheel size minus 1. -/
private theorem log_le_prod (limit : Nat) (hl : 2 ≤ limit) :
    Real.log limit ≤ ∏ q ∈ active_primes limit, ((q : Real) / ((q : Real) - 1)) := by
  obtain ⟨N, rfl⟩ : ∃ N, limit = N + 1 := ⟨limit - 1, by omega⟩
  have h1 := log_add_one_le_harmonic N
  rw [harmonic_eq_sum_Icc] at h1
  push_cast at h1
  have h2 := harmonic_le_prod N
  simp only [one_div] at h2
  push_cast
  linarith

/-- **The survivor share is at most one over the logarithm**, as a step from
the survivor count. -/
theorem survivor_share_le_inv_log_step (hgen : general_survivor_count) :
    survivor_share_le_inv_log := by
  intro limit hl
  have hlog : 0 < Real.log limit := Real.log_pos (by exact_mod_cast (by omega : 1 < limit))
  have hA := log_le_prod limit hl
  have hprod : (∏ q ∈ active_primes limit, (((q : Real) - 1) / q))
      * ∏ q ∈ active_primes limit, ((q : Real) / ((q : Real) - 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun q hq => ?_)
    have h2 : (2 : Real) ≤ q := by exact_mod_cast (mem_active hq).1.two_le
    have h0 : (q : Real) ≠ 0 := by linarith
    have h1 : (q : Real) - 1 ≠ 0 := by linarith
    field_simp
  rw [share_eq_prod hgen limit]
  have hApos : 0 < ∏ q ∈ active_primes limit, ((q : Real) / ((q : Real) - 1)) := by linarith
  have hs : ∏ q ∈ active_primes limit, (((q : Real) - 1) / q)
      = 1 / ∏ q ∈ active_primes limit, ((q : Real) / ((q : Real) - 1)) := by
    field_simp
    linarith
  rw [hs]
  exact one_div_le_one_div_of_le hlog hA

/-- **The twin share is at most twice the square of that**, as a step from the
two survivor counts. -/
theorem twin_share_le_two_inv_log_sq_step (htwin : twin_survivor_count)
    (hgen : general_survivor_count) : twin_share_le_two_inv_log_sq := by
  intro limit hl
  have hplain := survivor_share_le_inv_log_step hgen limit hl
  rw [share_eq_prod hgen limit] at hplain
  have hplain0 : 0 ≤ ∏ q ∈ active_primes limit, (((q : Real) - 1) / q) := by
    refine Finset.prod_nonneg (fun q hq => ?_)
    have h2 : (2 : Real) ≤ q := by exact_mod_cast (mem_active hq).1.two_le
    exact div_nonneg (by linarith) (by linarith)
  -- the twin share, factor by factor
  have htw : ((wheel_survivors limit).card : Real) / (primorial_modulus limit : Real)
      = ∏ q ∈ active_primes limit, ((if q = 2 then (1 : Real) else (q : Real) - 2) / q) := by
    rw [htwin limit, primorial_modulus, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun q hq => ?_)
    by_cases h : q = 2
    · simp [h]
    · have h3 : 2 ≤ q := (mem_active hq).1.two_le
      rw [if_neg h, if_neg h, Nat.cast_sub h3]
      simp
  have hfac : ∀ q ∈ active_primes limit,
      (if q = 2 then (1 : Real) else (q : Real) - 2) / q
        ≤ (if q = 2 then (2 : Real) else 1) * (((q : Real) - 1) / q) ^ 2 := by
    intro q hq
    by_cases h : q = 2
    · subst h
      norm_num
    · have h3 : (3 : Real) ≤ q := by
        have := (mem_active hq).1.two_le
        exact_mod_cast (show 3 ≤ q by omega)
      rw [if_neg h, if_neg h, one_mul, div_pow, div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith
  have hle := Finset.prod_le_prod (fun q hq => by
      by_cases h : q = 2
      · subst h
        norm_num
      · have h3 : (3 : Real) ≤ q := by
          have := (mem_active hq).1.two_le
          exact_mod_cast (show 3 ≤ q by omega)
        rw [if_neg h]
        exact div_nonneg (by linarith) (by linarith)) hfac
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' (active_primes limit) 2 (fun _ => (2 : Real)),
    Finset.prod_pow] at hle
  have htwo : (if 2 ∈ active_primes limit then (2 : Real) else 1) ≤ 2 := by
    split_ifs <;> norm_num
  have hsq : (∏ q ∈ active_primes limit, (((q : Real) - 1) / q)) ^ 2 ≤ (1 / Real.log limit) ^ 2 :=
    pow_le_pow_left₀ hplain0 hplain 2
  have hsq0 : 0 ≤ (∏ q ∈ active_primes limit, (((q : Real) - 1) / q)) ^ 2 := by positivity
  rw [htw]
  nlinarith

end RNS.ShareBounds
