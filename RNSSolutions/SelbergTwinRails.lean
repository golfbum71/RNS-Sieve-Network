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
import Mathlib.NumberTheory.Divisors                 -- `Nat.mem_divisors`
import Mathlib.Tactic.Push                          -- `push Not`
import Mathlib.NumberTheory.Harmonic.Bounds         -- `log_add_one_le_harmonic`
import Mathlib.Analysis.SpecialFunctions.Pow.Real   -- `Real.sqrt`, `Real.log`, `Nat.floor`

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

/-! ## The twin sum grows like log² of the level

The route (after Ford, Theorem 4.4). Write the twin sum as a sum over sets `T`
of wheels with product at most `M`, each set weighing the product of
2/(p − 2). Adding one wheel `q` splits the sum: the sets without `q`, plus
2/(q − 2) times the sets without `q` up to `M / q`. Against it set the smooth
sum: over the numbers `n` up to `M` built from the wheels, 2 to the number of
prime factors of `n` over `n`. The smooth sum splits the same way, with 2/q in
place of 2/(q − 2) and the smooth sum itself in the second part; since
(2/q)(1 + 2/(q − 2)) = 2/(q − 2), induction on the wheels shows the twin sum
is at least the smooth sum. The number of ways to write `n` as `a b` is at most
2 to the number of prime factors of `n`, so the smooth sum is at least the
square of the sum of 1/a over the `a` up to √M prime to 6, and the numbers
6k + 1 alone make that at least (1/6) log of the count.
-/

/-- Selberg's term for a set of wheels: the product of 2 over (the wheel − 2). -/
private noncomputable def setTerm (T : Finset ℕ) : ℝ := ∏ p ∈ T, (2 : ℝ) / ((p : ℝ) - 2)

/-- The twin sum over sets of wheels from `S` with product at most `M`. -/
private noncomputable def setSum (S : Finset ℕ) (M : ℕ) : ℝ :=
  ∑ T ∈ S.powerset, if ∏ p ∈ T, p ≤ M then setTerm T else 0

private theorem setTerm_nonneg {T : Finset ℕ} (hT : ∀ p ∈ T, 5 ≤ p) : 0 ≤ setTerm T := by
  unfold setTerm
  refine Finset.prod_nonneg (fun p hp => div_nonneg (by norm_num) ?_)
  have : (5 : ℝ) ≤ p := by exact_mod_cast hT p hp
  linarith

private theorem setSum_nonneg {S : Finset ℕ} (hS : ∀ p ∈ S, 5 ≤ p) (M : ℕ) :
    0 ≤ setSum S M := by
  unfold setSum
  refine Finset.sum_nonneg (fun T hT => ?_)
  split_ifs
  · exact setTerm_nonneg (fun p hp => hS p (Finset.mem_powerset.mp hT hp))
  · exact le_rfl

private theorem setSum_mono {S : Finset ℕ} (hS : ∀ p ∈ S, 5 ≤ p) {M M' : ℕ} (h : M ≤ M') :
    setSum S M ≤ setSum S M' := by
  unfold setSum
  refine Finset.sum_le_sum (fun T hT => ?_)
  by_cases h1 : ∏ p ∈ T, p ≤ M
  · rw [ite_eq_left h1, ite_eq_left (h1.trans h)]
  · rw [ite_eq_right h1]
    split_ifs
    · exact setTerm_nonneg (fun p hp => hS p (Finset.mem_powerset.mp hT hp))
    · exact le_rfl

private theorem setSum_insert {S : Finset ℕ} {q : ℕ} (hq : q ∉ S) (hq0 : 0 < q) (M : ℕ) :
    setSum (insert q S) M = setSum S M + 2 / ((q : ℝ) - 2) * setSum S (M / q) := by
  unfold setSum
  rw [Finset.sum_powerset_insert hq]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  have hqT : q ∉ T := fun h => hq (Finset.mem_powerset.mp hT h)
  have hiff : q * ∏ p ∈ T, p ≤ M ↔ ∏ p ∈ T, p ≤ M / q := by
    rw [Nat.le_div_iff_mul_le hq0, Nat.mul_comm (∏ p ∈ T, p) q]
  rw [Finset.prod_insert hqT]
  by_cases h : ∏ p ∈ T, p ≤ M / q
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    unfold setTerm
    rw [Finset.prod_insert hqT]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h, mul_zero]

/-- The smooth term: 2 to the number of prime factors of `n` over `n`, when
every prime factor of `n` lies in `S`. -/
private noncomputable def smoothTerm (S : Finset ℕ) (n : ℕ) : ℝ :=
  if n.primeFactors ⊆ S then (2 : ℝ) ^ ArithmeticFunction.cardFactors n / n else 0

/-- The smooth sum over the numbers from 1 to `M`. -/
private noncomputable def smoothSum (S : Finset ℕ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, smoothTerm S n

private theorem smoothTerm_nonneg (S : Finset ℕ) (n : ℕ) : 0 ≤ smoothTerm S n := by
  unfold smoothTerm
  split_ifs
  · positivity
  · exact le_rfl

private theorem smoothTerm_mul {S : Finset ℕ} {q m : ℕ} (hq : q.Prime) (hqS : q ∈ S)
    (hm0 : m ≠ 0) : smoothTerm S (q * m) = 2 / (q : ℝ) * smoothTerm S m := by
  have hcond : (q * m).primeFactors ⊆ S ↔ m.primeFactors ⊆ S := by
    rw [Nat.primeFactors_mul hq.ne_zero hm0, hq.primeFactors, Finset.union_subset_iff,
      Finset.singleton_subset_iff]
    exact ⟨fun h => h.2, fun h => ⟨hqS, h⟩⟩
  have hΩ : ArithmeticFunction.cardFactors (q * m) = ArithmeticFunction.cardFactors m + 1 := by
    rw [ArithmeticFunction.cardFactors_mul hq.ne_zero hm0,
      ArithmeticFunction.cardFactors_apply_prime hq, Nat.add_comm]
  unfold smoothTerm
  by_cases h : m.primeFactors ⊆ S
  · rw [ite_eq_left (hcond.mpr h), ite_eq_left h, hΩ, pow_succ]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    push_cast
    field_simp
  · rw [ite_eq_right (fun h' => h (hcond.mp h')), ite_eq_right h, mul_zero]

/-- The smooth sum splits at a new wheel `q`: the numbers prime to `q`, plus
2/q times the smooth sum up to `M / q`. -/
private theorem smoothSum_insert_le {S : Finset ℕ} {q : ℕ} (hq : q ∉ S) (hqP : q.Prime)
    (M : ℕ) : smoothSum (insert q S) M ≤
      smoothSum S M + 2 / (q : ℝ) * smoothSum (insert q S) (M / q) := by
  have hq0 : 0 < q := hqP.pos
  unfold smoothSum
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun n => q ∣ n), add_comm]
  refine add_le_add ?_ ?_
  · calc ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ q ∣ n), smoothTerm (insert q S) n
        = ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ q ∣ n), smoothTerm S n := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          have hqn : ¬ q ∣ n := (Finset.mem_filter.mp hn).2
          have hnq : q ∉ n.primeFactors := fun h => hqn (Nat.dvd_of_mem_primeFactors h)
          have hiff : n.primeFactors ⊆ insert q S ↔ n.primeFactors ⊆ S := by
            constructor
            · intro h p hp
              rcases Finset.mem_insert.mp (h hp) with rfl | h'
              · exact absurd hp hnq
              · exact h'
            · intro h
              exact h.trans (Finset.subset_insert _ _)
          unfold smoothTerm
          by_cases h : n.primeFactors ⊆ S
          · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
          · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]
      _ ≤ ∑ n ∈ Finset.Icc 1 M, smoothTerm S n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun n _ _ => smoothTerm_nonneg S n)
  · have hsub : (Finset.Icc 1 M).filter (fun n => q ∣ n) ⊆
        (Finset.Icc 1 (M / q)).image (fun m => q * m) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩ := hn
      rw [Finset.mem_image]
      refine ⟨m, ?_, rfl⟩
      rw [Finset.mem_Icc]
      constructor
      · rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, Nat.mul_zero] at h1
          omega
        · exact h
      · rw [Nat.le_div_iff_mul_le hq0, Nat.mul_comm]
        exact h2
    rw [Finset.mul_sum]
    calc ∑ n ∈ (Finset.Icc 1 M).filter (fun n => q ∣ n), smoothTerm (insert q S) n
        ≤ ∑ n ∈ (Finset.Icc 1 (M / q)).image (fun m => q * m), smoothTerm (insert q S) n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => smoothTerm_nonneg _ n)
      _ = ∑ m ∈ Finset.Icc 1 (M / q), smoothTerm (insert q S) (q * m) := by
          rw [Finset.sum_image]
          intro a _ b _ h
          exact Nat.eq_of_mul_eq_mul_left hq0 h
      _ = ∑ m ∈ Finset.Icc 1 (M / q), 2 / (q : ℝ) * smoothTerm (insert q S) m := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          have hm0 : m ≠ 0 := by
            have := (Finset.mem_Icc.mp hm).1
            omega
          exact smoothTerm_mul hqP (Finset.mem_insert_self q S) hm0

/-- **The twin sum is at least the smooth sum**, for any set of wheels from 5 up. -/
private theorem smoothSum_le_setSum (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime ∧ 5 ≤ p) → ∀ M, smoothSum S M ≤ setSum S M := by
  refine Finset.induction_on S ?_ ?_
  · intro _ M
    have h1 : smoothSum ∅ M ≤ ∑ n ∈ Finset.Icc 1 M, (if n = 1 then (1 : ℝ) else 0) := by
      unfold smoothSum
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      unfold smoothTerm
      split_ifs with h h'
      · rw [h', ArithmeticFunction.cardFactors_one]
        norm_num
      · exfalso
        have := Finset.subset_empty.mp h
        rw [Nat.primeFactors_eq_empty] at this
        omega
      · positivity
      · exact le_rfl
    refine h1.trans (le_of_eq ?_)
    rw [Finset.sum_ite_eq']
    unfold setSum setTerm
    by_cases hM : 1 ≤ M
    · simp [hM]
    · simp [hM]
  · intro q S hq ih hS' M
    have hSS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p := fun p hp => hS' p (Finset.mem_insert_of_mem hp)
    have hS5 : ∀ p ∈ S, 5 ≤ p := fun p hp => (hSS p hp).2
    have hqP := hS' q (Finset.mem_insert_self q S)
    have hS5' : ∀ p ∈ insert q S, 5 ≤ p := fun p hp => (hS' p hp).2
    have ihS := ih hSS
    have hq0 : 0 < q := hqP.1.pos
    have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast hqP.2
    have hg0 : 0 ≤ 2 / ((q : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
    induction M using Nat.strong_induction_on with
    | _ M ihM =>
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM
        have : smoothSum (insert q S) 0 = 0 := by simp [smoothSum]
        rw [this]
        exact setSum_nonneg hS5' 0
      · have hlt : M / q < M := Nat.div_lt_self hM hqP.1.one_lt
        calc smoothSum (insert q S) M
            ≤ smoothSum S M + 2 / (q : ℝ) * smoothSum (insert q S) (M / q) :=
              smoothSum_insert_le hq hqP.1 M
          _ ≤ setSum S M + 2 / (q : ℝ) * setSum (insert q S) (M / q) :=
              add_le_add (ihS M) (mul_le_mul_of_nonneg_left (ihM _ hlt) (by positivity))
          _ = setSum S M + 2 / (q : ℝ) *
                (setSum S (M / q) + 2 / ((q : ℝ) - 2) * setSum S (M / q / q)) := by
              rw [setSum_insert hq hq0]
          _ ≤ setSum S M + 2 / (q : ℝ) *
                (setSum S (M / q) + 2 / ((q : ℝ) - 2) * setSum S (M / q)) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left
                (add_le_add le_rfl (mul_le_mul_of_nonneg_left
                  (setSum_mono hS5 (Nat.div_le_self _ _)) hg0)) (by positivity))
          _ = setSum S M + 2 / ((q : ℝ) - 2) * setSum S (M / q) := by
              have h1 : (q : ℝ) ≠ 0 := by linarith
              have h2 : (q : ℝ) - 2 ≠ 0 := by linarith
              field_simp
              ring
          _ = setSum (insert q S) M := (setSum_insert hq hq0 M).symm

/-- A number has at most 2 to the number of its prime factors divisors. -/
private theorem card_divisors_le_two_pow (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ≤ 2 ^ ArithmeticFunction.cardFactors n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      simp
    · have hp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [Nat.mul_zero] at hm
        exact hn hm
      have hmlt : m < n := by
        have h2 := hp.two_le
        rw [hm]
        nlinarith [Nat.pos_of_ne_zero hm0]
      have hdiv : n.divisors.card ≤ 2 * m.divisors.card := by
        have hsub : n.divisors ⊆ m.divisors ∪ m.divisors.image (fun e => n.minFac * e) := by
          intro d hd
          rw [Nat.mem_divisors] at hd
          rw [Finset.mem_union, Finset.mem_image]
          have hdm : d ∣ n.minFac * m := hm ▸ hd.1
          by_cases hpd : n.minFac ∣ d
          · right
            obtain ⟨e, rfl⟩ := hpd
            refine ⟨e, ?_, rfl⟩
            rw [Nat.mem_divisors]
            exact ⟨(mul_dvd_mul_iff_left hp.ne_zero).mp hdm, hm0⟩
          · left
            rw [Nat.mem_divisors]
            have hc : Nat.Coprime d n.minFac := ((hp.coprime_iff_not_dvd).mpr hpd).symm
            exact ⟨hc.dvd_of_dvd_mul_left hdm, hm0⟩
        calc n.divisors.card
            ≤ (m.divisors ∪ m.divisors.image (fun e => n.minFac * e)).card :=
              Finset.card_le_card hsub
          _ ≤ m.divisors.card + (m.divisors.image (fun e => n.minFac * e)).card :=
              Finset.card_union_le _ _
          _ ≤ m.divisors.card + m.divisors.card := Nat.add_le_add_left Finset.card_image_le _
          _ = 2 * m.divisors.card := by omega
      have hΩ : ArithmeticFunction.cardFactors n = ArithmeticFunction.cardFactors m + 1 := by
        rw [hm, ArithmeticFunction.cardFactors_mul hp.ne_zero hm0,
          ArithmeticFunction.cardFactors_apply_prime hp, Nat.add_comm]
      rw [hΩ, pow_succ]
      have := ih m hmlt hm0
      omega

/-- The numbers up to `K` prime to 6. -/
private def primeToSix (K : ℕ) : Finset ℕ := (Finset.Icc 1 K).filter (fun a => Nat.Coprime 6 a)

/-- A number up to `M` prime to 6 is built from the wheels from 5 up to `z`,
when `M < z`. -/
private theorem primeFactors_sub_wheels {z M n : ℕ} (hMz : M < z) (hn : n ∈ primeToSix M) :
    n.primeFactors ⊆ twin_wheels z := by
  unfold primeToSix at hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnM⟩, hcop⟩ := hn
  intro p hp
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have hle : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hsmall : ∀ d, d ∣ 6 → d ∣ n → d ≤ 1 := by
    intro d h6 hdn
    have := Nat.dvd_gcd h6 hdn
    rw [hcop.gcd_eq_one] at this
    exact Nat.le_of_dvd one_pos this
  have h2 : p ≠ 2 := by
    rintro rfl
    have := hsmall 2 (by norm_num) hpn
    omega
  have h3 : p ≠ 3 := by
    rintro rfl
    have := hsmall 3 (by norm_num) hpn
    omega
  have h4 : p ≠ 4 := by
    rintro rfl
    have := hpP.eq_one_or_self_of_dvd 2 (by norm_num)
    omega
  have h5 : 5 ≤ p := by
    have := hpP.two_le
    omega
  exact mem_twin_wheels.mpr ⟨hpP, by omega, h5⟩

/-- **The smooth sum is at least the square of the sum of 1/a over the `a` up
to `K` prime to 6**, when `K²` is at most `M` and `M` is below the cut-off. -/
private theorem sq_le_smoothSum {z M K : ℕ} (hMz : M < z) (hKM : K * K ≤ M) :
    (∑ a ∈ primeToSix K, (1 : ℝ) / a) ^ 2 ≤ smoothSum (twin_wheels z) M := by
  have hmaps : ∀ x ∈ primeToSix K ×ˢ primeToSix K, x.1 * x.2 ∈ primeToSix M := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨ha, hb⟩ := hx
    unfold primeToSix at ha hb ⊢
    rw [Finset.mem_filter, Finset.mem_Icc] at ha hb ⊢
    refine ⟨⟨?_, ?_⟩, Nat.Coprime.mul_right ha.2 hb.2⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact (Nat.mul_le_mul ha.1.2 hb.1.2).trans hKM
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product',
    ← Finset.sum_fiberwise_of_maps_to hmaps]
  have hsub : primeToSix M ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => smoothTerm_nonneg _ n))
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn1 : 1 ≤ n := by
    have := hsub hn
    exact (Finset.mem_Icc.mp this).1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  set fib := (primeToSix K ×ˢ primeToSix K).filter (fun x => x.1 * x.2 = n) with hfib
  have hval : ∀ x ∈ fib, (1 : ℝ) / x.1 * (1 / x.2) = 1 / n := by
    intro x hx
    have := (Finset.mem_filter.mp hx).2
    rw [← this]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hcard : fib.card ≤ n.divisors.card := by
    refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
    · intro x hx
      have hx' := Finset.mem_filter.mp hx
      rw [Finset.mem_coe, Nat.mem_divisors]
      exact ⟨⟨x.2, hx'.2.symm⟩, by omega⟩
    · intro x hx x' hx' h
      have hx1 := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      have hx2 := Finset.mem_filter.mp (Finset.mem_coe.mp hx')
      have h1 : x.1 = x'.1 := h
      have hpos : 0 < x.1 := by
        have := (Finset.mem_product.mp hx1.1).1
        unfold primeToSix at this
        exact (Finset.mem_Icc.mp (Finset.mem_filter.mp this).1).1
      have h2 : x.2 = x'.2 := by
        have : x.1 * x.2 = x.1 * x'.2 := by rw [hx1.2, h1, hx2.2]
        exact Nat.eq_of_mul_eq_mul_left hpos this
      exact Prod.ext h1 h2
  have hτ := card_divisors_le_two_pow n (by omega)
  unfold smoothTerm
  rw [ite_eq_left (primeFactors_sub_wheels hMz hn)]
  have : (fib.card : ℝ) ≤ (2 : ℝ) ^ ArithmeticFunction.cardFactors n := by
    exact_mod_cast hcard.trans hτ
  rw [div_eq_mul_one_div ((2 : ℝ) ^ _) (n : ℝ)]
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **The numbers 6k + 1 alone**: the sum of 1/a over the `a` up to `K` prime to
6 is at least (1/6) log((K + 6)/6). -/
private theorem log_le_sum_primeToSix (K : ℕ) :
    Real.log (((K : ℝ) + 6) / 6) / 6 ≤ ∑ a ∈ primeToSix K, (1 : ℝ) / a := by
  set J := (K + 5) / 6 with hJ
  have hKJ : K ≤ 6 * J := by omega
  have hsub : (Finset.range J).image (fun k => 6 * k + 1) ⊆ primeToSix K := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    rw [Finset.mem_range] at hk
    unfold primeToSix
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have : (k + 1) * 6 ≤ K + 5 := (Nat.le_div_iff_mul_le (by norm_num)).mp hk
      omega
    · show Nat.gcd 6 (6 * k + 1) = 1
      rw [Nat.gcd_rec, show (6 * k + 1) % 6 = 1 by omega, Nat.gcd_one_left]
  have h1 : ∑ k ∈ Finset.range J, (1 : ℝ) / ((6 * k + 1 : ℕ) : ℝ) ≤
      ∑ a ∈ primeToSix K, (1 : ℝ) / a := by
    rw [← Finset.sum_image (f := fun a : ℕ => (1 : ℝ) / a) (g := fun k => 6 * k + 1)]
    · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
    · intro a _ b _ h
      simp only at h
      omega
  have h2 : ∑ k ∈ Finset.range J, (1 : ℝ) / ((k : ℝ) + 1) / 6 ≤
      ∑ k ∈ Finset.range J, (1 : ℝ) / ((6 * k + 1 : ℕ) : ℝ) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    push_cast
    rw [div_div]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have h3 : Real.log ((J : ℝ) + 1) ≤ ∑ k ∈ Finset.range J, (1 : ℝ) / ((k : ℝ) + 1) := by
    have := log_add_one_le_harmonic J
    unfold harmonic at this
    push_cast at this
    simpa [one_div] using this
  have h4 : Real.log (((K : ℝ) + 6) / 6) ≤ Real.log ((J : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    have : (K : ℝ) ≤ 6 * J := by exact_mod_cast hKJ
    linarith
  rw [← Finset.sum_div] at h2
  linarith

/-- The twin sum as a sum over sets of wheels: each divisor of the wheel
product is the product of its prime factors, and these are a set of wheels. -/
private theorem twin_selberg_sum_eq (z : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    twin_selberg_sum z y = setSum (twin_wheels z) ⌊Real.sqrt y⌋₊ := by
  have hpf : ∀ T ⊆ twin_wheels z, (∏ p ∈ T, p).primeFactors = T := by
    intro T hT
    have hTP : ∀ p ∈ T, p.Prime := fun p hp => twin_wheels_prime (hT hp)
    have h0 : ∏ p ∈ T, p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hTP p hp).ne_zero)
    ext p
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp hdvd
      rwa [(Nat.prime_dvd_prime_iff_eq hp (hTP q hq)).mp hpq]
    · intro hp
      exact ⟨hTP p hp, Finset.dvd_prod_of_mem _ hp, h0⟩
  have hP0 : twin_wheel_product z ≠ 0 := by
    unfold twin_wheel_product
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (twin_wheels_prime hp).ne_zero)
  unfold twin_selberg_sum setSum
  refine Finset.sum_nbij' (fun l => l.primeFactors) (fun T => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [Nat.mem_divisors] at hl
    rw [Finset.mem_powerset]
    intro p hp
    exact mem_of_prime_dvd (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hl.1)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Nat.mem_divisors]
    refine ⟨?_, hP0⟩
    unfold twin_wheel_product
    exact Finset.prod_dvd_prod_of_subset T (twin_wheels z) (fun p => p) hT
  · intro l hl
    rw [Nat.mem_divisors] at hl
    exact Nat.prod_primeFactors_of_squarefree
      (Squarefree.squarefree_of_dvd hl.1 (product_squarefree z))
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact hpf T hT
  · intro l hl
    rw [Nat.mem_divisors] at hl
    have hsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1 (product_squarefree z)
    rw [Nat.prod_primeFactors_of_squarefree hsq]
    have hiff : (l : ℝ) ^ 2 ≤ y ↔ l ≤ ⌊Real.sqrt y⌋₊ := by
      rw [Nat.le_floor_iff (Real.sqrt_nonneg y)]
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      have hs := Real.sq_sqrt hy
      have hs0 := Real.sqrt_nonneg y
      constructor
      · intro h
        by_contra h'
        push Not at h'
        nlinarith
      · intro h
        nlinarith
    by_cases h : (l : ℝ) ^ 2 ≤ y
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
      rfl
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]

/-- **The twin sum grows like log² of the level** (after Ford, Theorem 4.4). -/
theorem twin_selberg_sum_lower_holds : twin_selberg_sum_lower := by
  intro z y hy hyz
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  set M := ⌊Real.sqrt y⌋₊ with hMdef
  set K := Nat.sqrt M with hKdef
  have hz0 : (0 : ℝ) < z := by
    by_contra h
    push Not at h
    have : (z : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg z)
    rw [this] at hyz
    linarith
  have hMz : M < z := by
    have h1 : (M : ℝ) ≤ Real.sqrt y := Nat.floor_le (Real.sqrt_nonneg y)
    have h2 : Real.sqrt y < z := (Real.sqrt_lt' hz0).mpr hyz
    exact_mod_cast h1.trans_lt h2
  have hKM : K * K ≤ M := Nat.sqrt_le M
  -- the chain of lower bounds
  have hsum := twin_selberg_sum_eq z y hy0.le
  have hset := smoothSum_le_setSum (twin_wheels z)
    (fun p hp => ⟨twin_wheels_prime hp, twin_wheels_five hp⟩) M
  have hsmooth := sq_le_smoothSum hMz hKM
  have hlog := log_le_sum_primeToSix K
  -- the size of `K`: `y` is below (K + 1)⁴
  have hM1 : Real.sqrt y < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK1 : (M : ℝ) + 1 ≤ ((K : ℝ) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt M
    have h' : M + 1 ≤ (K + 1) * (K + 1) := this
    have h'' : ((M + 1 : ℕ) : ℝ) ≤ ((K + 1) * (K + 1) : ℕ) := by exact_mod_cast h'
    push_cast at h''
    nlinarith
  have hyK : y < ((K : ℝ) + 1) ^ 4 := by
    have hs := Real.sq_sqrt hy0.le
    have hs0 := Real.sqrt_nonneg y
    have h3 : y < ((M : ℝ) + 1) ^ 2 := by nlinarith
    have h4 : ((M : ℝ) + 1) ^ 2 ≤ (((K : ℝ) + 1) ^ 2) ^ 2 := by
      have : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
      nlinarith
    calc y < ((M : ℝ) + 1) ^ 2 := h3
      _ ≤ (((K : ℝ) + 1) ^ 2) ^ 2 := h4
      _ = ((K : ℝ) + 1) ^ 4 := by ring
  have hlogy : Real.log y < 4 * Real.log ((K : ℝ) + 1) := by
    have := Real.log_lt_log hy0 hyK
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hlog6 : 4 * Real.log 6 ≤ Real.log y := by
    have := Real.log_le_log (by norm_num) hy
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hKlog : Real.log ((K : ℝ) + 1) - Real.log 6 ≤ Real.log (((K : ℝ) + 6) / 6) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    have : Real.log ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) + 6) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  set L := ∑ a ∈ primeToSix K, (1 : ℝ) / a
  have hL : (Real.log y - 4 * Real.log 6) / 24 ≤ L := by linarith
  have hL0 : 0 ≤ (Real.log y - 4 * Real.log 6) / 24 := by linarith
  have hsq : ((Real.log y - 4 * Real.log 6) / 24) * ((Real.log y - 4 * Real.log 6) / 24) ≤
      L * L := mul_self_le_mul_self hL0 hL
  rw [hsum]
  calc (Real.log y - 4 * Real.log 6) ^ 2 / 576
      = ((Real.log y - 4 * Real.log 6) / 24) * ((Real.log y - 4 * Real.log 6) / 24) := by ring
    _ ≤ L * L := hsq
    _ = L ^ 2 := by ring
    _ ≤ smoothSum (twin_wheels z) M := hsmooth
    _ ≤ setSum (twin_wheels z) M := hset

end RNS.SelbergTwinRails

#print axioms RNS.SelbergTwinRails.selberg_twin_columns_bound_step
#print axioms RNS.SelbergTwinRails.twin_selberg_sum_lower_holds
