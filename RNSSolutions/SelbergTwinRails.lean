/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SelbergTwinRails.Conclusions
import RNSNetwork.Nodes.SelbergBound.Conclusions
import RNSNetwork.Nodes.BrunTwinCount.Conclusions
import Mathlib.Data.Nat.Squarefree                  -- `Nat.prod_primeFactors_of_squarefree`
import Mathlib.Algebra.Squarefree.Basic             -- `Finset.squarefree_prod_of_pairwise_isCoprime`
import Mathlib.Algebra.BigOperators.Associated      -- `Prime.dvd_finsetProd_iff`
import Mathlib.Algebra.BigOperators.Ring.Finset     -- `Finset.sum_boole`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proofs for SelbergTwinRails

Built clean by `lake build RNSSolutions` on 2026-11-09; `#print axioms` shows only
the standard three.

Imports claims only. `selberg_twin_columns_bound` is a step from
`SelbergBound.selberg_bound` and `BrunTwinCount.twin_multiples_count`, taken as
named hypotheses.

Idea. The sieve problem: the numbers `m (m + 2)` for `m` from 1 to `N`, each
with weight 1, total mass `N`; the wheels from 5 up to the cut-off; the share
of a divisor `d` of the wheel product is the product over its prime factors of
2 over the prime. The map `m ↦ m (m + 2)` is one-to-one, so the sifted sum is
the number of survivors, and the multiples of `d` are counted by
`BrunTwinCount`, whose error is at most 2 to the number of prime factors.
Selberg's terms are 2/p · (1 − 2/p)⁻¹ = 2/(p − 2) at each prime. Selberg's
bound then gives the claim, with 3 · 2 = 6 per prime factor in the error.
-/

namespace RNS.SelbergTwinRails

open BoundingSieve

/-! ## The wheels from 5 up -/

private theorem mem_twin_wheels {z p : ℕ} :
    p ∈ twin_wheels z ↔ p.Prime ∧ p < z ∧ 5 ≤ p := by
  unfold twin_wheels active_primes
  simp only [Finset.mem_filter, Finset.mem_range]
  tauto

private theorem twin_wheels_prime {z p : ℕ} (hp : p ∈ twin_wheels z) : p.Prime :=
  (mem_twin_wheels.mp hp).1

private theorem twin_wheels_five {z p : ℕ} (hp : p ∈ twin_wheels z) : 5 ≤ p :=
  (mem_twin_wheels.mp hp).2.2

private theorem product_squarefree (z : ℕ) : Squarefree (twin_wheel_product z) := by
  unfold twin_wheel_product
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
    (fun p hp => (twin_wheels_prime hp).prime.squarefree)
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (twin_wheels_prime (Finset.mem_coe.mp ha))
      (twin_wheels_prime (Finset.mem_coe.mp hb))).mpr hab)

private theorem mem_of_prime_dvd {z p : ℕ} (hp : p.Prime) (h : p ∣ twin_wheel_product z) :
    p ∈ twin_wheels z := by
  unfold twin_wheel_product at h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (twin_wheels_prime hq)).mp hpq]

/-! ## The share of a divisor -/

/-- The share of a divisor: the product over its prime factors of 2 over the
prime. -/
private noncomputable def twin_nu : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (2 : ℝ) / p)

private theorem twin_nu_apply {d : ℕ} (hd : d ≠ 0) :
    twin_nu d = ∏ p ∈ d.primeFactors, (2 : ℝ) / p :=
  ArithmeticFunction.prodPrimeFactors_apply hd

private theorem twin_nu_prime {p : ℕ} (hp : p.Prime) : twin_nu p = 2 / p := by
  rw [twin_nu_apply hp.ne_zero, hp.primeFactors, Finset.prod_singleton]

/-! ## The sieve problem -/

/-- The twin columns as a Selberg sieve problem. -/
private noncomputable def twin_sieve (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Finset.Ioc 0 N).image (fun m => m * (m + 2))
  prodPrimes := twin_wheel_product z
  prodPrimes_squarefree := product_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := twin_nu
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => by
    rw [twin_nu_prime hp]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact div_pos two_pos this
  nu_lt_one_of_prime := fun p hp hpd => by
    rw [twin_nu_prime hp]
    have h5 : (5 : ℝ) ≤ p := by exact_mod_cast twin_wheels_five (mem_of_prime_dvd hp hpd)
    rw [div_lt_one (by linarith)]
    linarith
  level := y
  one_le_level := hy

private theorem twin_map_injective : Function.Injective (fun m : ℕ => m * (m + 2)) := by
  intro a b h
  simp only at h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)).ne
  · exact hab
  · exact absurd h (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)).ne'

private theorem card_image_filter (N : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (((Finset.Ioc 0 N).image (fun m => m * (m + 2))).filter q).card =
      ((Finset.Ioc 0 N).filter (fun m => q (m * (m + 2)))).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ twin_map_injective]

private theorem sifted_eq (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    BoundingSieve.siftedSum (s := (twin_sieve N z y hy).toBoundingSieve) =
      (twin_columns_sifted N z : ℝ) := by
  unfold BoundingSieve.siftedSum twin_columns_sifted
  show (∑ d ∈ (Finset.Ioc 0 N).image (fun m => m * (m + 2)),
      if Nat.Coprime (twin_wheel_product z) d then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole, card_image_filter]

private theorem multSum_eq (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) :
    BoundingSieve.multSum (s := (twin_sieve N z y hy).toBoundingSieve) d =
      (((Finset.Ioc 0 N).filter (fun m => d ∣ m * (m + 2))).card : ℝ) := by
  unfold BoundingSieve.multSum
  show (∑ n ∈ (Finset.Ioc 0 N).image (fun m => m * (m + 2)),
      if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole, card_image_filter]

/-- The error of each divisor of the wheel product is at most 2 to the number
of its prime factors (`BrunTwinCount`). -/
private theorem rem_le (N z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (h_tc : RNS.BrunTwinCount.twin_multiples_count)
    {d : ℕ} (hd : d ∣ twin_wheel_product z) :
    |BoundingSieve.rem (s := (twin_sieve N z y hy).toBoundingSieve) d| ≤
      (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (product_squarefree z)
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hD : ∀ p ∈ d.primeFactors, p.Prime ∧ 5 ≤ p := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp,
      twin_wheels_five (mem_of_prime_dvd (Nat.prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hd))⟩
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
  have hprod' : d.primeFactors.prod id = d := hprod
  have hrho : RNS.BrunTwinCount.twin_rho d.primeFactors = 2 ^ d.primeFactors.card := by
    unfold RNS.BrunTwinCount.twin_rho
    rw [Finset.prod_congr rfl (fun p hp => ite_eq_right (by have := (hD p hp).2; omega)),
      Finset.prod_const]
  have hnu : twin_nu d = (2 : ℝ) ^ d.primeFactors.card / d := by
    rw [twin_nu_apply hd0, Finset.prod_div_distrib, Finset.prod_const]
    congr 1
    rw [← Nat.cast_prod, hprod]
  have key := h_tc d.primeFactors N (fun p hp => (hD p hp).1)
  rw [hprod', hrho] at key
  unfold BoundingSieve.rem
  rw [multSum_eq]
  show |(_ : ℝ) - twin_nu d * N| ≤ _
  rw [hnu, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  push_cast at key ⊢
  calc _ = |(((Finset.Ioc 0 N).filter (fun m => d ∣ m * (m + 2))).card : ℝ) -
        (N : ℝ) * 2 ^ d.primeFactors.card / d| := by congr 1; ring
    _ ≤ _ := key

/-- Selberg's terms for the twin columns are 2 over (the prime − 2) at each
prime, so the node's bounding sum is the twin sum. -/
private theorem bounding_eq (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    RNS.SelbergBound.bounding_sum (twin_sieve N z y hy) = twin_selberg_sum z y := by
  unfold RNS.SelbergBound.bounding_sum twin_selberg_sum
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hld : l ∣ twin_wheel_product z := Nat.dvd_of_mem_divisors hl
  have hl0 : l ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hl)
  have hg : (twin_sieve N z y hy).toBoundingSieve.selbergTerms l =
      ∏ p ∈ l.primeFactors, (2 : ℝ) / ((p : ℝ) - 2) := by
    rw [BoundingSieve.selbergTerms_apply]
    show twin_nu l * ∏ p ∈ l.primeFactors, (1 - twin_nu p)⁻¹ = _
    rw [twin_nu_apply hl0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpP := Nat.prime_of_mem_primeFactors hp
    have h5 : (5 : ℝ) ≤ p := by
      exact_mod_cast twin_wheels_five
        (mem_of_prime_dvd hpP ((Nat.dvd_of_mem_primeFactors hp).trans hld))
    rw [twin_nu_prime hpP]
    have h1 : (p : ℝ) ≠ 0 := by linarith
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    have h3 : (1 : ℝ) - 2 / p ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      rw [eq_div_iff h1] at h
      linarith
    field_simp
  rw [hg]
  rfl

/-- **Step:** Selberg's bound and the twin multiples count give Selberg's bound
for the twin columns. -/
theorem selberg_twin_columns_bound_step
    (h_sb : RNS.SelbergBound.selberg_bound)
    (h_tc : RNS.BrunTwinCount.twin_multiples_count) :
    selberg_twin_columns_bound := by
  intro N z y hy
  have h := h_sb (twin_sieve N z y hy)
  rw [sifted_eq, bounding_eq] at h
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum (fun d hd => ?_)))
  show (if (d : ℝ) ≤ y then (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
      |BoundingSieve.rem (s := (twin_sieve N z y hy).toBoundingSieve) d| else 0) ≤
    if (d : ℝ) ≤ y then (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0
  split_ifs with hdy
  · have hr := rem_le N z y hy h_tc (Nat.dvd_of_mem_divisors hd)
    calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
          |BoundingSieve.rem (s := (twin_sieve N z y hy).toBoundingSieve) d|
        ≤ (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
          (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d := by
          rw [← mul_pow]; norm_num
  · exact le_rfl

end RNS.SelbergTwinRails

#print axioms RNS.SelbergTwinRails.selberg_twin_columns_bound_step
