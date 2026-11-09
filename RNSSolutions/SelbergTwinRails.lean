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
`twin_selberg_sum_lower` is proved outright (Mathlib only).
`selberg_twin_bound` is a step from `selberg_twin_columns_bound` and
`twin_selberg_sum_lower`, taken as named hypotheses.

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

/-! ## At most a constant times N / log² N twin primes

Take `t` the eighth root of `N` rounded down, the level t² and the cut-off
t² + 1. Twin primes from the cut-off up survive the twin columns, so they
number at most the cut-off plus the survivors. The survivors are at most `N`
over the twin sum plus the error; the twin sum is at least log² N / 36864 once
`N` is at least 5184⁸, and each error term 6 to the number of prime factors of
`d` is at most d² (every wheel is at least 5, and 6 ≤ 5²), so the error is at
most t⁶. Since log N ≤ 8 t, t⁶ is at most 64 N / log² N.
-/

private theorem twin_count_le (N z : ℕ) :
    RNS.BrunTwinBound.twin_prime_count N ≤ z + twin_columns_sifted N z := by
  unfold RNS.BrunTwinBound.twin_prime_count twin_columns_sifted
  have hsub : (Finset.Ioc 0 N).filter (fun n => n.Prime ∧ (n + 2).Prime) ⊆
      Finset.range z ∪ (Finset.Ioc 0 N).filter
        (fun m => Nat.Coprime (twin_wheel_product z) (m * (m + 2))) := by
    intro n hn
    obtain ⟨hnN, hp, hp2⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_filter]
    by_cases hnz : n < z
    · exact Or.inl hnz
    · right
      refine ⟨hnN, Nat.Coprime.mul_right ?_ ?_⟩
      · refine ((hp.coprime_iff_not_dvd).mpr (fun h => hnz ?_)).symm
        exact (mem_twin_wheels.mp (mem_of_prime_dvd hp h)).2.1
      · refine ((hp2.coprime_iff_not_dvd).mpr (fun h => hnz ?_)).symm
        have := (mem_twin_wheels.mp (mem_of_prime_dvd hp2 h)).2.1
        omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_range]

/-- 6 to the number of prime factors of a divisor of the wheel product is at
most its square. -/
private theorem six_pow_le_sq {z d : ℕ} (hd : d ∣ twin_wheel_product z) :
    (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d ≤ (d : ℝ) ^ 2 := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (product_squarefree z)
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
  conv_rhs => rw [← hprod]
  push_cast
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, ← Finset.prod_const,
    ← Finset.prod_pow]
  gcongr with p hp
  have h5 : (5 : ℝ) ≤ p := by
    exact_mod_cast twin_wheels_five (mem_of_prime_dvd (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hd))
  nlinarith

/-- The error at level t² is at most t⁶. -/
private theorem error_le (z t : ℕ) :
    (∑ d ∈ Nat.divisors (twin_wheel_product z),
      if (d : ℝ) ≤ (t : ℝ) ^ 2 then (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0)
      ≤ (t : ℝ) ^ 6 := by
  calc _ ≤ ∑ d ∈ Nat.divisors (twin_wheel_product z),
        if d ∈ Finset.Icc 1 (t ^ 2) then (t : ℝ) ^ 4 else 0 := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd' := Nat.mem_divisors.mp hd
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        by_cases h : (d : ℝ) ≤ (t : ℝ) ^ 2
        · have hdt : d ≤ t ^ 2 := by exact_mod_cast h
          rw [ite_eq_left h, ite_eq_left (Finset.mem_Icc.mpr ⟨hd1, hdt⟩)]
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          calc (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d ≤ (d : ℝ) ^ 2 :=
                six_pow_le_sq hd'.1
            _ ≤ ((t : ℝ) ^ 2) ^ 2 := by nlinarith
            _ = (t : ℝ) ^ 4 := by ring
        · rw [ite_eq_right h]
          split_ifs
          · positivity
          · exact le_rfl
    _ = ∑ d ∈ Nat.divisors (twin_wheel_product z) ∩ Finset.Icc 1 (t ^ 2), (t : ℝ) ^ 4 :=
        Finset.sum_ite_mem _ _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (t ^ 2), (t : ℝ) ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun _ _ _ => by positivity)
    _ = (t : ℝ) ^ 6 := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        push_cast
        ring

/-- The eighth root of `N`, rounded down. -/
private theorem eighth_root (N : ℕ) : ∃ t : ℕ, t ^ 8 ≤ N ∧ N < (t + 1) ^ 8 := by
  obtain ⟨a, h3, h3'⟩ : ∃ a, a * a ≤ N ∧ N < (a + 1) * (a + 1) :=
    ⟨Nat.sqrt N, Nat.sqrt_le N, Nat.lt_succ_sqrt N⟩
  obtain ⟨b, h2, h2'⟩ : ∃ b, b * b ≤ a ∧ a < (b + 1) * (b + 1) :=
    ⟨Nat.sqrt a, Nat.sqrt_le a, Nat.lt_succ_sqrt a⟩
  obtain ⟨t, h1, h1'⟩ : ∃ t, t * t ≤ b ∧ b < (t + 1) * (t + 1) :=
    ⟨Nat.sqrt b, Nat.sqrt_le b, Nat.lt_succ_sqrt b⟩
  refine ⟨t, ?_, ?_⟩
  · have h4 : (t * t) * (t * t) ≤ a := (Nat.mul_le_mul h1 h1).trans h2
    calc t ^ 8 = ((t * t) * (t * t)) * ((t * t) * (t * t)) := by ring
      _ ≤ a * a := Nat.mul_le_mul h4 h4
      _ ≤ N := h3
  · have h1'' : b + 1 ≤ (t + 1) * (t + 1) := h1'
    have h2'' : a + 1 ≤ (b + 1) * (b + 1) := h2'
    have h4 : a + 1 ≤ ((t + 1) * (t + 1)) * ((t + 1) * (t + 1)) :=
      h2''.trans (Nat.mul_le_mul h1'' h1'')
    calc N < (a + 1) * (a + 1) := h3'
      _ ≤ (((t + 1) * (t + 1)) * ((t + 1) * (t + 1))) *
            (((t + 1) * (t + 1)) * ((t + 1) * (t + 1))) := Nat.mul_le_mul h4 h4
      _ = (t + 1) ^ 8 := by ring

/-- **Step:** the bound for the twin columns and the lower bound for the twin
sum give Selberg's bound for twin primes. -/
theorem selberg_twin_bound_step
    (h_cols : selberg_twin_columns_bound) (h_low : twin_selberg_sum_lower) :
    selberg_twin_bound := by
  intro N hN
  obtain ⟨t, hlo, hhi⟩ := eighth_root N
  have hN8 : (5184 : ℕ) ^ 8 ≤ N := by exact_mod_cast hN
  have ht5184 : 5184 ≤ t := by
    by_contra h
    have h' : t + 1 ≤ 5184 := by omega
    have : (t + 1) ^ 8 ≤ 5184 ^ 8 := Nat.pow_le_pow_left h' 8
    exact absurd (lt_of_lt_of_le hhi this) (not_lt.mpr hN8)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0 : ℝ) < t := by linarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hloR : (t : ℝ) ^ 8 ≤ N := by exact_mod_cast hlo
  have hhiR : (N : ℝ) < ((t : ℝ) + 1) ^ 8 := by exact_mod_cast hhi
  -- logarithms
  have hLt : Real.log N < 8 * Real.log ((t : ℝ) + 1) := by
    have := Real.log_lt_log hNpos hhiR
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hL5184 : 8 * Real.log 5184 ≤ Real.log N := by
    have := Real.log_le_log (by positivity) hN
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlog5184 : Real.log 5184 = 2 * Real.log 2 + 4 * Real.log 6 := by
    rw [show (5184 : ℝ) = 2 ^ 2 * 6 ^ 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hLpos : 0 < Real.log N := by linarith
  have hlogt1 : Real.log ((t : ℝ) + 1) ≤ Real.log 2 + Real.log t := by
    rw [← Real.log_mul (by norm_num) ht0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hlogt1' : Real.log ((t : ℝ) + 1) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (t : ℝ) + 1 by positivity)
    linarith
  have hlt2 : Real.log ((t : ℝ) ^ 2) = 2 * Real.log t := by
    rw [Real.log_pow]
    push_cast
    ring
  -- the level t² and the cut-off t² + 1
  have hy1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (t : ℝ) * t := mul_le_mul ht1 ht1 zero_le_one ht0.le
      _ = (t : ℝ) ^ 2 := by ring
  have hy6 : (6 : ℝ) ^ 4 ≤ (t : ℝ) ^ 2 := by
    have h5 : (5184 : ℝ) ≤ t := by exact_mod_cast ht5184
    calc (6 : ℝ) ^ 4 ≤ 5184 * 5184 := by norm_num
      _ ≤ (t : ℝ) * t := mul_le_mul h5 h5 (by norm_num) ht0.le
      _ = (t : ℝ) ^ 2 := by ring
  have hyz : (t : ℝ) ^ 2 < ((t ^ 2 + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    calc (t : ℝ) ^ 2 < (t : ℝ) ^ 2 + 1 := by linarith
      _ = ((t : ℝ) ^ 2 + 1) * 1 := by ring
      _ ≤ ((t : ℝ) ^ 2 + 1) * ((t : ℝ) ^ 2 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ((t : ℝ) ^ 2 + 1) ^ 2 := by ring
  have hG := h_low (t ^ 2 + 1) ((t : ℝ) ^ 2) hy6 hyz
  have hsieve := h_cols N (t ^ 2 + 1) ((t : ℝ) ^ 2) hy1
  have hE := error_le (t ^ 2 + 1) t
  have hcount : (RNS.BrunTwinBound.twin_prime_count N : ℝ) ≤
      (t : ℝ) ^ 2 + 1 + (twin_columns_sifted N (t ^ 2 + 1) : ℝ) := by
    have := twin_count_le N (t ^ 2 + 1)
    exact_mod_cast this
  -- the twin sum is at least log² N / 36864
  have hu : Real.log N / 8 ≤ Real.log ((t : ℝ) ^ 2) - 4 * Real.log 6 := by linarith
  have hu0 : 0 ≤ Real.log N / 8 := by linarith
  have hsq := mul_self_le_mul_self hu0 hu
  have hGlow : Real.log N ^ 2 / 36864 ≤ twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) := by
    calc Real.log N ^ 2 / 36864 = (Real.log N / 8) * (Real.log N / 8) / 576 := by ring
      _ ≤ (Real.log ((t : ℝ) ^ 2) - 4 * Real.log 6) *
            (Real.log ((t : ℝ) ^ 2) - 4 * Real.log 6) / 576 := by linarith [hsq]
      _ = (Real.log ((t : ℝ) ^ 2) - 4 * Real.log 6) ^ 2 / 576 := by ring
      _ ≤ _ := hG
  have hGpos : 0 < Real.log N ^ 2 / 36864 := by positivity
  set Q := (N : ℝ) / Real.log N ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hdivG : (N : ℝ) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) ≤ 36864 * Q := by
    calc (N : ℝ) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2)
        ≤ (N : ℝ) / (Real.log N ^ 2 / 36864) :=
          div_le_div_of_nonneg_left hNpos.le hGpos hGlow
      _ = 36864 * Q := by
          rw [hQ]
          field_simp
  -- the error and the cut-off are at most a constant times N / log² N
  have hLle : Real.log N ≤ 8 * t := by linarith
  have hL2 : Real.log N ^ 2 ≤ 64 * (t : ℝ) ^ 2 := by
    calc Real.log N ^ 2 = Real.log N * Real.log N := by ring
      _ ≤ (8 * t) * (8 * t) := mul_self_le_mul_self hLpos.le hLle
      _ = 64 * (t : ℝ) ^ 2 := by ring
  have ht6 : (t : ℝ) ^ 6 ≤ 64 * Q := by
    rw [hQ, mul_div_assoc', le_div_iff₀ (by positivity)]
    have h1 : (t : ℝ) ^ 6 * Real.log N ^ 2 ≤ (t : ℝ) ^ 6 * (64 * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    calc (t : ℝ) ^ 6 * Real.log N ^ 2 ≤ (t : ℝ) ^ 6 * (64 * (t : ℝ) ^ 2) := h1
      _ = 64 * (t : ℝ) ^ 8 := by ring
      _ ≤ 64 * N := by linarith
  have hz : (t : ℝ) ^ 2 + 1 ≤ 2 * (t : ℝ) ^ 6 := by
    have h4 : (1 : ℝ) ≤ (t : ℝ) ^ 4 := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (t : ℝ) ^ 2 * (t : ℝ) ^ 2 := mul_le_mul hy1 hy1 zero_le_one (by positivity)
        _ = (t : ℝ) ^ 4 := by ring
    have h26 : (t : ℝ) ^ 2 ≤ (t : ℝ) ^ 6 := by
      calc (t : ℝ) ^ 2 = (t : ℝ) ^ 2 * 1 := by ring
        _ ≤ (t : ℝ) ^ 2 * (t : ℝ) ^ 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (t : ℝ) ^ 6 := by ring
    linarith
  rw [mul_div_assoc, ← hQ]
  linarith

/-! ## Prime pairs at any gap, and Goldbach pairs

The same sieve on `m (m + c)` for a shift `c`, with the wheels dividing `c`
left out (there a wheel blocks only one position of its cycle). Leaving them
out costs at most the product, over those wheels, of 1 + 2/(p − 2) =
p/(p − 2): splitting the sets of wheels by the left-out part shows the full
twin sum is at most that product times the sum without them. Goldbach pairs
of `N` are the shift `c = (Q − 1) N`, with `Q` the product of the wheels not
dividing `N`: then `m + c` and `N − m` have the same wheels as factors.
-/

/-- The parameters of the twin bound: `t` the eighth root of `N` rounded down,
the level t², the cut-off t² + 1. -/
private theorem twin_parameters (h_low : twin_selberg_sum_lower) (N : ℕ)
    (hN : (5184 : ℝ) ^ 8 ≤ N) :
    ∃ t : ℕ, 5184 ≤ t ∧ t ^ 8 ≤ N ∧ 0 < Real.log N ∧ (1 : ℝ) ≤ (t : ℝ) ^ 2 ∧
      Real.log N ^ 2 / 36864 ≤ twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) ∧
      (t : ℝ) ^ 6 ≤ 64 * ((N : ℝ) / Real.log N ^ 2) ∧
      (t : ℝ) ^ 2 + 1 ≤ 2 * (t : ℝ) ^ 6 := by
  obtain ⟨t, hlo, hhi⟩ := eighth_root N
  have hN8 : (5184 : ℕ) ^ 8 ≤ N := by exact_mod_cast hN
  have ht5184 : 5184 ≤ t := by
    by_contra h
    have h' : t + 1 ≤ 5184 := by omega
    have : (t + 1) ^ 8 ≤ 5184 ^ 8 := Nat.pow_le_pow_left h' 8
    exact absurd (lt_of_lt_of_le hhi this) (not_lt.mpr hN8)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0 : ℝ) < t := by linarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hloR : (t : ℝ) ^ 8 ≤ N := by exact_mod_cast hlo
  have hhiR : (N : ℝ) < ((t : ℝ) + 1) ^ 8 := by exact_mod_cast hhi
  -- logarithms
  have hLt : Real.log N < 8 * Real.log ((t : ℝ) + 1) := by
    have := Real.log_lt_log hNpos hhiR
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hL5184 : 8 * Real.log 5184 ≤ Real.log N := by
    have := Real.log_le_log (by positivity) hN
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlog5184 : Real.log 5184 = 2 * Real.log 2 + 4 * Real.log 6 := by
    rw [show (5184 : ℝ) = 2 ^ 2 * 6 ^ 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hLpos : 0 < Real.log N := by linarith
  have hlogt1 : Real.log ((t : ℝ) + 1) ≤ Real.log 2 + Real.log t := by
    rw [← Real.log_mul (by norm_num) ht0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hlogt1' : Real.log ((t : ℝ) + 1) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (t : ℝ) + 1 by positivity)
    linarith
  have hlt2 : Real.log ((t : ℝ) ^ 2) = 2 * Real.log t := by
    rw [Real.log_pow]
    push_cast
    ring
  -- the level t² and the cut-off t² + 1
  have hy1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (t : ℝ) * t := mul_le_mul ht1 ht1 zero_le_one ht0.le
      _ = (t : ℝ) ^ 2 := by ring
  have hy6 : (6 : ℝ) ^ 4 ≤ (t : ℝ) ^ 2 := by
    have h5 : (5184 : ℝ) ≤ t := by exact_mod_cast ht5184
    calc (6 : ℝ) ^ 4 ≤ 5184 * 5184 := by norm_num
      _ ≤ (t : ℝ) * t := mul_le_mul h5 h5 (by norm_num) ht0.le
      _ = (t : ℝ) ^ 2 := by ring
  have hyz : (t : ℝ) ^ 2 < ((t ^ 2 + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    calc (t : ℝ) ^ 2 < (t : ℝ) ^ 2 + 1 := by linarith
      _ = ((t : ℝ) ^ 2 + 1) * 1 := by ring
      _ ≤ ((t : ℝ) ^ 2 + 1) * ((t : ℝ) ^ 2 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ((t : ℝ) ^ 2 + 1) ^ 2 := by ring
  have hG := h_low (t ^ 2 + 1) ((t : ℝ) ^ 2) hy6 hyz
  have hu : Real.log N / 8 ≤ Real.log ((t : ℝ) ^ 2) - 4 * Real.log 6 := by linarith
  have hu0 : 0 ≤ Real.log N / 8 := by linarith
  have hsq := mul_self_le_mul_self hu0 hu
  have hGlow : Real.log N ^ 2 / 36864 ≤ twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) := by
    calc Real.log N ^ 2 / 36864 = (Real.log N / 8) * (Real.log N / 8) / 576 := by ring
      _ ≤ (Real.log ((t : ℝ) ^ 2) - 4 * Real.log 6) *
            (Real.log ((t : ℝ) ^ 2) - 4 * Real.log 6) / 576 := by linarith [hsq]
      _ = (Real.log ((t : ℝ) ^ 2) - 4 * Real.log 6) ^ 2 / 576 := by ring
      _ ≤ _ := hG
  set Q := (N : ℝ) / Real.log N ^ 2 with hQ
  have hLle : Real.log N ≤ 8 * t := by linarith
  have hL2 : Real.log N ^ 2 ≤ 64 * (t : ℝ) ^ 2 := by
    calc Real.log N ^ 2 = Real.log N * Real.log N := by ring
      _ ≤ (8 * t) * (8 * t) := mul_self_le_mul_self hLpos.le hLle
      _ = 64 * (t : ℝ) ^ 2 := by ring
  have ht6 : (t : ℝ) ^ 6 ≤ 64 * Q := by
    rw [hQ, mul_div_assoc', le_div_iff₀ (by positivity)]
    have h1 : (t : ℝ) ^ 6 * Real.log N ^ 2 ≤ (t : ℝ) ^ 6 * (64 * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    calc (t : ℝ) ^ 6 * Real.log N ^ 2 ≤ (t : ℝ) ^ 6 * (64 * (t : ℝ) ^ 2) := h1
      _ = 64 * (t : ℝ) ^ 8 := by ring
      _ ≤ 64 * N := by linarith
  have hz : (t : ℝ) ^ 2 + 1 ≤ 2 * (t : ℝ) ^ 6 := by
    have h4 : (1 : ℝ) ≤ (t : ℝ) ^ 4 := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (t : ℝ) ^ 2 * (t : ℝ) ^ 2 := mul_le_mul hy1 hy1 zero_le_one (by positivity)
        _ = (t : ℝ) ^ 4 := by ring
    have h26 : (t : ℝ) ^ 2 ≤ (t : ℝ) ^ 6 := by
      calc (t : ℝ) ^ 2 = (t : ℝ) ^ 2 * 1 := by ring
        _ ≤ (t : ℝ) ^ 2 * (t : ℝ) ^ 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (t : ℝ) ^ 6 := by ring
    linarith
  exact ⟨t, ht5184, hlo, hLpos, hy1, hGlow, ht6, hz⟩

/-- The wheels from 5 up to `z` that do not divide `c`. -/
private def shiftWheels (c z : ℕ) : Finset ℕ := (twin_wheels z).filter (fun p => ¬ p ∣ c)

/-- The wheels from 5 up to `z` that divide `c`. -/
private def badWheels (c z : ℕ) : Finset ℕ := (twin_wheels z).filter (fun p => p ∣ c)

private theorem shiftWheels_mem {c z p : ℕ} (hp : p ∈ shiftWheels c z) :
    p ∈ twin_wheels z ∧ ¬ p ∣ c := Finset.mem_filter.mp hp

private theorem shiftWheels_prime {c z p : ℕ} (hp : p ∈ shiftWheels c z) : p.Prime :=
  twin_wheels_prime (shiftWheels_mem hp).1

private theorem prod_squarefree_of_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
    (fun p hp => (hS p hp).prime.squarefree)
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (hS a (Finset.mem_coe.mp ha)) (hS b (Finset.mem_coe.mp hb))).mpr hab)

private theorem mem_of_prime_dvd_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {p : ℕ}
    (hp : p.Prime) (h : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hpq]

/-- The shifted columns as a Selberg sieve problem. -/
private noncomputable def shift_sieve (c X z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Finset.Ioc 0 X).image (fun m => m * (m + c))
  prodPrimes := ∏ p ∈ shiftWheels c z, p
  prodPrimes_squarefree := prod_squarefree_of_primes _ (fun p hp => shiftWheels_prime hp)
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := twin_nu
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => by
    rw [twin_nu_prime hp]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact div_pos two_pos this
  nu_lt_one_of_prime := fun p hp hpd => by
    rw [twin_nu_prime hp]
    have h5 : (5 : ℝ) ≤ p := by
      exact_mod_cast twin_wheels_five (shiftWheels_mem
        (mem_of_prime_dvd_prod (fun q hq => shiftWheels_prime hq) hp hpd)).1
    rw [div_lt_one (by linarith)]
    linarith
  level := y
  one_le_level := hy

private theorem shift_map_injective (c : ℕ) : Function.Injective (fun m : ℕ => m * (m + c)) := by
  intro a b h
  simp only at h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)).ne
  · exact hab
  · exact absurd h (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)).ne'

private theorem shift_card_image_filter (c X : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (((Finset.Ioc 0 X).image (fun m => m * (m + c))).filter q).card =
      ((Finset.Ioc 0 X).filter (fun m => q (m * (m + c)))).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (shift_map_injective c)]

private theorem shift_sifted_eq (c X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    BoundingSieve.siftedSum (s := (shift_sieve c X z y hy).toBoundingSieve) =
      (((Finset.Ioc 0 X).filter
        (fun m => Nat.Coprime (∏ p ∈ shiftWheels c z, p) (m * (m + c)))).card : ℝ) := by
  unfold BoundingSieve.siftedSum
  show (∑ d ∈ (Finset.Ioc 0 X).image (fun m => m * (m + c)),
      if Nat.Coprime (∏ p ∈ shiftWheels c z, p) d then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole, shift_card_image_filter]

private theorem shift_multSum_eq (c X z : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) :
    BoundingSieve.multSum (s := (shift_sieve c X z y hy).toBoundingSieve) d =
      (((Finset.Ioc 0 X).filter (fun m => d ∣ m * (m + c))).card : ℝ) := by
  unfold BoundingSieve.multSum
  show (∑ n ∈ (Finset.Ioc 0 X).image (fun m => m * (m + c)),
      if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole, shift_card_image_filter]

private theorem shift_rem_le (c X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (h_sc : RNS.BrunTwinCount.shift_multiples_count)
    {d : ℕ} (hd : d ∣ ∏ p ∈ shiftWheels c z, p) :
    |BoundingSieve.rem (s := (shift_sieve c X z y hy).toBoundingSieve) d| ≤
      (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (prod_squarefree_of_primes _ (fun p hp => shiftWheels_prime hp))
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hD : ∀ p ∈ d.primeFactors, p.Prime ∧ ¬ p ∣ c := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp,
      (shiftWheels_mem (mem_of_prime_dvd_prod (fun q hq => shiftWheels_prime hq)
        (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hd))).2⟩
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
  have hprod' : d.primeFactors.prod id = d := hprod
  have hrho : RNS.BrunTwinCount.shift_rho c d.primeFactors = 2 ^ d.primeFactors.card := by
    unfold RNS.BrunTwinCount.shift_rho
    rw [Finset.prod_congr rfl (fun p hp => ite_eq_right (hD p hp).2), Finset.prod_const]
  have hnu : twin_nu d = (2 : ℝ) ^ d.primeFactors.card / d := by
    rw [twin_nu_apply hd0, Finset.prod_div_distrib, Finset.prod_const]
    congr 1
    rw [← Nat.cast_prod, hprod]
  have key := h_sc d.primeFactors c X (fun p hp => (hD p hp).1)
  rw [hprod', hrho] at key
  unfold BoundingSieve.rem
  rw [shift_multSum_eq]
  show |(_ : ℝ) - twin_nu d * X| ≤ _
  rw [hnu, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  push_cast at key ⊢
  calc _ = |(((Finset.Ioc 0 X).filter (fun m => d ∣ m * (m + c))).card : ℝ) -
        (X : ℝ) * 2 ^ d.primeFactors.card / d| := by congr 1; ring
    _ ≤ _ := key

private theorem shift_bounding_eq (c X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    RNS.SelbergBound.bounding_sum (shift_sieve c X z y hy) =
      ∑ l ∈ Nat.divisors (∏ p ∈ shiftWheels c z, p),
        if (l : ℝ) ^ 2 ≤ y then ∏ p ∈ l.primeFactors, (2 : ℝ) / ((p : ℝ) - 2) else 0 := by
  unfold RNS.SelbergBound.bounding_sum
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hld : l ∣ ∏ p ∈ shiftWheels c z, p := Nat.dvd_of_mem_divisors hl
  have hl0 : l ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hl)
  have hg : (shift_sieve c X z y hy).toBoundingSieve.selbergTerms l =
      ∏ p ∈ l.primeFactors, (2 : ℝ) / ((p : ℝ) - 2) := by
    rw [BoundingSieve.selbergTerms_apply]
    show twin_nu l * ∏ p ∈ l.primeFactors, (1 - twin_nu p)⁻¹ = _
    rw [twin_nu_apply hl0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpP := Nat.prime_of_mem_primeFactors hp
    have h5 : (5 : ℝ) ≤ p := by
      exact_mod_cast twin_wheels_five (shiftWheels_mem (mem_of_prime_dvd_prod
        (fun q hq => shiftWheels_prime hq) hpP ((Nat.dvd_of_mem_primeFactors hp).trans hld))).1
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

/-- A divisor sum over a set of wheels from 5 up, as a sum over sets of wheels. -/
private theorem divisor_sum_eq_setSum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (y : ℝ)
    (hy : 0 ≤ y) :
    (∑ l ∈ Nat.divisors (∏ p ∈ S, p),
      if (l : ℝ) ^ 2 ≤ y then ∏ p ∈ l.primeFactors, (2 : ℝ) / ((p : ℝ) - 2) else 0) =
      setSum S ⌊Real.sqrt y⌋₊ := by
  have hpf : ∀ T ⊆ S, (∏ p ∈ T, p).primeFactors = T := by
    intro T hT
    have hTP : ∀ p ∈ T, p.Prime := fun p hp => hS p (hT hp)
    have h0 : ∏ p ∈ T, p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hTP p hp).ne_zero)
    ext p
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp hdvd
      rwa [(Nat.prime_dvd_prime_iff_eq hp (hTP q hq)).mp hpq]
    · intro hp
      exact ⟨hTP p hp, Finset.dvd_prod_of_mem _ hp, h0⟩
  have hP0 : ∏ p ∈ S, p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  have hsqS := prod_squarefree_of_primes S hS
  unfold setSum
  refine Finset.sum_nbij' (fun l => l.primeFactors) (fun T => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [Nat.mem_divisors] at hl
    rw [Finset.mem_powerset]
    intro p hp
    exact mem_of_prime_dvd_prod hS (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hl.1)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Nat.mem_divisors]
    exact ⟨Finset.prod_dvd_prod_of_subset T S (fun p => p) hT, hP0⟩
  · intro l hl
    rw [Nat.mem_divisors] at hl
    exact Nat.prod_primeFactors_of_squarefree (Squarefree.squarefree_of_dvd hl.1 hsqS)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact hpf T hT
  · intro l hl
    rw [Nat.mem_divisors] at hl
    have hsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1 hsqS
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

/-- Leaving out the wheels `A` costs at most the product of 1 + 2/(p − 2). -/
private theorem setSum_union_le (B : Finset ℕ) (hB : ∀ p ∈ B, 5 ≤ p) (A : Finset ℕ) :
    (∀ p ∈ A, p.Prime ∧ 5 ≤ p) → Disjoint A B → ∀ M,
      setSum (A ∪ B) M ≤ (∏ p ∈ A, (1 + 2 / ((p : ℝ) - 2))) * setSum B M := by
  refine Finset.induction_on A ?_ ?_
  · intro _ _ M
    rw [Finset.empty_union, Finset.prod_empty, one_mul]
  · intro q A hq ih hA hdisj M
    have hqB : q ∉ B := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self q A)
    have hdisj' : Disjoint A B := Finset.disjoint_of_subset_left (Finset.subset_insert q A) hdisj
    have hA' : ∀ p ∈ A, p.Prime ∧ 5 ≤ p := fun p hp => hA p (Finset.mem_insert_of_mem hp)
    have hqP := hA q (Finset.mem_insert_self q A)
    have hqAB : q ∉ A ∪ B := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact hq h
      · exact hqB h
    have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast hqP.2
    have hg0 : 0 ≤ 2 / ((q : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
    have hP0 : 0 ≤ ∏ p ∈ A, (1 + 2 / ((p : ℝ) - 2)) := by
      refine Finset.prod_nonneg (fun p hp => ?_)
      have h5 : (5 : ℝ) ≤ p := by exact_mod_cast (hA' p hp).2
      have : 0 ≤ 2 / ((p : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
      linarith
    rw [Finset.insert_union, setSum_insert hqAB hqP.1.pos, Finset.prod_insert hq]
    calc setSum (A ∪ B) M + 2 / ((q : ℝ) - 2) * setSum (A ∪ B) (M / q)
        ≤ (∏ p ∈ A, (1 + 2 / ((p : ℝ) - 2))) * setSum B M +
            2 / ((q : ℝ) - 2) * ((∏ p ∈ A, (1 + 2 / ((p : ℝ) - 2))) * setSum B (M / q)) :=
          add_le_add (ih hA' hdisj' M) (mul_le_mul_of_nonneg_left (ih hA' hdisj' (M / q)) hg0)
      _ ≤ (∏ p ∈ A, (1 + 2 / ((p : ℝ) - 2))) * setSum B M +
            2 / ((q : ℝ) - 2) * ((∏ p ∈ A, (1 + 2 / ((p : ℝ) - 2))) * setSum B M) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (setSum_mono hB (Nat.div_le_self _ _)) hP0) hg0)
      _ = (1 + 2 / ((q : ℝ) - 2)) * (∏ p ∈ A, (1 + 2 / ((p : ℝ) - 2))) * setSum B M := by ring

/-- The factor for the left-out wheels is positive. -/
private theorem bad_factor_pos (c z : ℕ) : 0 < ∏ p ∈ badWheels c z, (1 + 2 / ((p : ℝ) - 2)) := by
  refine Finset.prod_pos (fun p hp => ?_)
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast twin_wheels_five (Finset.mem_filter.mp hp).1
  have : 0 ≤ 2 / ((p : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
  linarith

/-- **The shifted sieve.** The survivors of `m (m + c)` among 1 to `X` number at
most the left-out factor times `X` over the twin sum, plus the error. -/
private theorem shift_core (h_sb : RNS.SelbergBound.selberg_bound)
    (h_sc : RNS.BrunTwinCount.shift_multiples_count) (c X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (hG : 0 < twin_selberg_sum z y) :
    (((Finset.Ioc 0 X).filter
        (fun m => Nat.Coprime (∏ p ∈ shiftWheels c z, p) (m * (m + c)))).card : ℝ) ≤
      (∏ p ∈ badWheels c z, (1 + 2 / ((p : ℝ) - 2))) * X / twin_selberg_sum z y +
        ∑ d ∈ Nat.divisors (∏ p ∈ shiftWheels c z, p),
          if (d : ℝ) ≤ y then (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0 := by
  have hW : ∀ p ∈ shiftWheels c z, p.Prime := fun p hp => shiftWheels_prime hp
  have h := h_sb (shift_sieve c X z y hy)
  rw [shift_sifted_eq, shift_bounding_eq, divisor_sum_eq_setSum _ hW y (by linarith)] at h
  set F := ∏ p ∈ badWheels c z, (1 + 2 / ((p : ℝ) - 2)) with hF
  have hFpos : 0 < F := bad_factor_pos c z
  have hsplit : twin_selberg_sum z y ≤ F * setSum (shiftWheels c z) ⌊Real.sqrt y⌋₊ := by
    rw [twin_selberg_sum_eq z y (by linarith)]
    have hu : twin_wheels z = badWheels c z ∪ shiftWheels c z := by
      ext p
      unfold badWheels shiftWheels
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hpc : p ∣ c <;> tauto
    rw [hu]
    refine setSum_union_le _ (fun p hp => twin_wheels_five (shiftWheels_mem hp).1) _ ?_ ?_ _
    · intro p hp
      have := (Finset.mem_filter.mp hp).1
      exact ⟨twin_wheels_prime this, twin_wheels_five this⟩
    · exact Finset.disjoint_left.mpr (fun p h1 h2 =>
        (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2)
  have hGW : 0 < setSum (shiftWheels c z) ⌊Real.sqrt y⌋₊ := by
    by_contra hneg
    push Not at hneg
    have : F * setSum (shiftWheels c z) ⌊Real.sqrt y⌋₊ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hFpos.le hneg
    linarith
  have hmain : (X : ℝ) / setSum (shiftWheels c z) ⌊Real.sqrt y⌋₊ ≤ F * X / twin_selberg_sum z y := by
    calc (X : ℝ) / setSum (shiftWheels c z) ⌊Real.sqrt y⌋₊
        = F * X / (F * setSum (shiftWheels c z) ⌊Real.sqrt y⌋₊) := by
          field_simp
      _ ≤ F * X / twin_selberg_sum z y :=
          div_le_div_of_nonneg_left (by positivity) hG hsplit
  refine h.trans (add_le_add hmain (Finset.sum_le_sum (fun d hd => ?_)))
  show (if (d : ℝ) ≤ y then (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
      |BoundingSieve.rem (s := (shift_sieve c X z y hy).toBoundingSieve) d| else 0) ≤
    if (d : ℝ) ≤ y then (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0
  split_ifs with hdy
  · have hr := shift_rem_le c X z y hy h_sc (Nat.dvd_of_mem_divisors hd)
    calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
          |BoundingSieve.rem (s := (shift_sieve c X z y hy).toBoundingSieve) d|
        ≤ (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
          (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d := by
          rw [← mul_pow]; norm_num
  · exact le_rfl

/-- The error over any set of wheels from 5 up, at level t², is at most t⁶. -/
private theorem error_le_of (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) (t : ℕ) :
    (∑ d ∈ Nat.divisors (∏ p ∈ S, p),
      if (d : ℝ) ≤ (t : ℝ) ^ 2 then (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0)
      ≤ (t : ℝ) ^ 6 := by
  have hsix : ∀ d ∈ Nat.divisors (∏ p ∈ S, p),
      (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d ≤ (d : ℝ) ^ 2 := by
    intro d hd
    have hdd := (Nat.mem_divisors.mp hd).1
    have hsq : Squarefree d := Squarefree.squarefree_of_dvd hdd
      (prod_squarefree_of_primes S (fun p hp => (hS p hp).1))
    have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
    conv_rhs => rw [← hprod]
    push_cast
    rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, ← Finset.prod_const,
      ← Finset.prod_pow]
    gcongr with p hp
    have h5 : (5 : ℝ) ≤ p := by
      exact_mod_cast (hS p (mem_of_prime_dvd_prod (fun q hq => (hS q hq).1)
        (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hdd))).2
    nlinarith
  calc _ ≤ ∑ d ∈ Nat.divisors (∏ p ∈ S, p),
        if d ∈ Finset.Icc 1 (t ^ 2) then (t : ℝ) ^ 4 else 0 := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        by_cases h : (d : ℝ) ≤ (t : ℝ) ^ 2
        · have hdt : d ≤ t ^ 2 := by exact_mod_cast h
          rw [ite_eq_left h, ite_eq_left (Finset.mem_Icc.mpr ⟨hd1, hdt⟩)]
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          calc (6 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d ≤ (d : ℝ) ^ 2 := hsix d hd
            _ ≤ ((t : ℝ) ^ 2) ^ 2 := by nlinarith
            _ = (t : ℝ) ^ 4 := by ring
        · rw [ite_eq_right h]
          split_ifs
          · positivity
          · exact le_rfl
    _ = ∑ d ∈ Nat.divisors (∏ p ∈ S, p) ∩ Finset.Icc 1 (t ^ 2), (t : ℝ) ^ 4 :=
        Finset.sum_ite_mem _ _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (t ^ 2), (t : ℝ) ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun _ _ _ => by positivity)
    _ = (t : ℝ) ^ 6 := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        push_cast
        ring

private theorem one_le_prod_of (s : Finset ℕ) (f : ℕ → ℝ) :
    (∀ p ∈ s, 1 ≤ f p) → 1 ≤ ∏ p ∈ s, f p := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty]
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    exact one_le_mul_of_one_le_of_one_le (h a (Finset.mem_insert_self a s))
      (ih (fun p hp => h p (Finset.mem_insert_of_mem hp)))

private theorem one_le_frac {p : ℕ} (hp : 5 ≤ p) : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 2) := by
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  rw [le_div_iff₀ (by linarith)]
  linarith

private theorem one_le_pair_factor (h : ℕ) : 1 ≤ pair_factor h :=
  one_le_prod_of _ _ (fun _ hp => one_le_frac (Finset.mem_filter.mp hp).2)

/-- The left-out factor is at most `pair_factor`. -/
private theorem bad_le_pair_factor (h z : ℕ) (hh : h ≠ 0) :
    ∏ p ∈ badWheels h z, (1 + 2 / ((p : ℝ) - 2)) ≤ pair_factor h := by
  have hsub : badWheels h z ⊆ h.primeFactors.filter (fun p => 5 ≤ p) := by
    intro p hp
    obtain ⟨hw, hph⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨twin_wheels_prime hw, hph, hh⟩, twin_wheels_five hw⟩
  have heq : ∏ p ∈ badWheels h z, (1 + 2 / ((p : ℝ) - 2)) =
      ∏ p ∈ badWheels h z, (p : ℝ) / ((p : ℝ) - 2) := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have h5 : (5 : ℝ) ≤ p := by exact_mod_cast twin_wheels_five (Finset.mem_filter.mp hp).1
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [heq]
  unfold pair_factor
  rw [← Finset.prod_sdiff hsub]
  have h1 : 1 ≤ ∏ p ∈ h.primeFactors.filter (fun p => 5 ≤ p) \ badWheels h z,
      (p : ℝ) / ((p : ℝ) - 2) :=
    one_le_prod_of _ _ (fun p hp => one_le_frac (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2)
  have h0 : 0 ≤ ∏ p ∈ badWheels h z, (p : ℝ) / ((p : ℝ) - 2) :=
    Finset.prod_nonneg (fun p hp => (zero_le_one.trans (one_le_frac
      (twin_wheels_five (Finset.mem_filter.mp hp).1))))
  nlinarith

/-- Prime pairs at gap `h` from the cut-off up survive the shifted sieve. -/
private theorem gap_count_le (h N z : ℕ) :
    gap_pair_count h N ≤ z + ((Finset.Ioc 0 N).filter
      (fun m => Nat.Coprime (∏ p ∈ shiftWheels h z, p) (m * (m + h)))).card := by
  unfold gap_pair_count
  have hW : ∀ p ∈ shiftWheels h z, p.Prime := fun p hp => shiftWheels_prime hp
  have hsub : (Finset.Ioc 0 N).filter (fun n => n.Prime ∧ (n + h).Prime) ⊆
      Finset.range z ∪ (Finset.Ioc 0 N).filter
        (fun m => Nat.Coprime (∏ p ∈ shiftWheels h z, p) (m * (m + h))) := by
    intro n hn
    obtain ⟨hnN, hp, hp2⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_filter]
    by_cases hnz : n < z
    · exact Or.inl hnz
    · right
      refine ⟨hnN, Nat.Coprime.mul_right ?_ ?_⟩
      · refine ((hp.coprime_iff_not_dvd).mpr (fun hd => hnz ?_)).symm
        exact (mem_twin_wheels.mp (shiftWheels_mem (mem_of_prime_dvd_prod hW hp hd)).1).2.1
      · refine ((hp2.coprime_iff_not_dvd).mpr (fun hd => hnz ?_)).symm
        have := (mem_twin_wheels.mp (shiftWheels_mem (mem_of_prime_dvd_prod hW hp2 hd)).1).2.1
        omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_range]

/-- **Step:** Selberg's bound, the multiples count at any shift and the lower
bound for the twin sum give Selberg's bound at any gap. -/
theorem selberg_gap_bound_step (h_sb : RNS.SelbergBound.selberg_bound)
    (h_sc : RNS.BrunTwinCount.shift_multiples_count) (h_low : twin_selberg_sum_lower) :
    selberg_gap_bound := by
  intro h N hh hN
  obtain ⟨t, _, _, hLpos, hy1, hGlow, ht6, hz⟩ := twin_parameters h_low N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  set Q := (N : ℝ) / Real.log N ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hGpos : 0 < twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) :=
    lt_of_lt_of_le (by positivity) hGlow
  have hcore := shift_core h_sb h_sc h N (t ^ 2 + 1) ((t : ℝ) ^ 2) hy1 hGpos
  have hE := error_le_of (shiftWheels h (t ^ 2 + 1))
    (fun p hp => ⟨shiftWheels_prime hp, twin_wheels_five (shiftWheels_mem hp).1⟩) t
  have hcount : (gap_pair_count h N : ℝ) ≤ (t : ℝ) ^ 2 + 1 + (((Finset.Ioc 0 N).filter
      (fun m => Nat.Coprime (∏ p ∈ shiftWheels h (t ^ 2 + 1), p) (m * (m + h)))).card : ℝ) := by
    have := gap_count_le h N (t ^ 2 + 1)
    exact_mod_cast this
  have hdivG : (N : ℝ) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) ≤ 36864 * Q := by
    have hpos : 0 < Real.log N ^ 2 / 36864 := by positivity
    calc (N : ℝ) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2)
        ≤ (N : ℝ) / (Real.log N ^ 2 / 36864) := div_le_div_of_nonneg_left hNpos.le hpos hGlow
      _ = 36864 * Q := by rw [hQ]; field_simp
  have hF := bad_le_pair_factor h (t ^ 2 + 1) (by omega)
  have hF1 := one_le_pair_factor h
  have hmain : (∏ p ∈ badWheels h (t ^ 2 + 1), (1 + 2 / ((p : ℝ) - 2))) * N /
      twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) ≤ 36864 * (pair_factor h * Q) := by
    rw [mul_div_assoc]
    calc (∏ p ∈ badWheels h (t ^ 2 + 1), (1 + 2 / ((p : ℝ) - 2))) *
          ((N : ℝ) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2))
        ≤ pair_factor h * (36864 * Q) :=
          mul_le_mul hF hdivG (div_nonneg hNpos.le hGpos.le) (by linarith)
      _ = 36864 * (pair_factor h * Q) := by ring
  have hPQ : Q ≤ pair_factor h * Q := le_mul_of_one_le_left hQ0 hF1
  rw [show 40000 * pair_factor h * (N : ℝ) / Real.log N ^ 2 = 40000 * (pair_factor h * Q) by
    rw [hQ]; ring]
  linarith

/-- Goldbach pairs: each pair is counted from its smaller member, at most twice. -/
private theorem goldbach_half (N : ℕ) :
    goldbach_count N ≤
      2 * ((Finset.Ioc 0 (N / 2)).filter (fun m => m.Prime ∧ (N - m).Prime)).card := by
  unfold goldbach_count
  have h1 : ((Finset.Ioo 0 N).filter (fun n => n.Prime ∧ (N - n).Prime)).filter
      (fun n => n ≤ N / 2) ⊆ (Finset.Ioc 0 (N / 2)).filter (fun m => m.Prime ∧ (N - m).Prime) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioo] at hn
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hn.1.1.1, hn.2⟩, hn.1.2⟩
  have h2 : (((Finset.Ioo 0 N).filter (fun n => n.Prime ∧ (N - n).Prime)).filter
      (fun n => ¬ n ≤ N / 2)).card ≤
      ((Finset.Ioc 0 (N / 2)).filter (fun m => m.Prime ∧ (N - m).Prime)).card := by
    refine Finset.card_le_card_of_injOn (fun n => N - n) ?_ ?_
    · intro n hn
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioo] at hn
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
      dsimp only
      obtain ⟨⟨⟨h0, hN⟩, hp, hq⟩, hhalf⟩ := hn
      refine ⟨⟨by omega, by omega⟩, hq, ?_⟩
      rw [Nat.sub_sub_self hN.le]
      exact hp
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioo] at ha hb
      have : N - a = N - b := hab
      omega
  have h3 := Finset.card_le_card h1
  have hsplit : (Finset.Ioo 0 N).filter (fun n => n.Prime ∧ (N - n).Prime) ⊆
      ((Finset.Ioo 0 N).filter (fun n => n.Prime ∧ (N - n).Prime)).filter (fun n => n ≤ N / 2) ∪
      ((Finset.Ioo 0 N).filter (fun n => n.Prime ∧ (N - n).Prime)).filter
        (fun n => ¬ n ≤ N / 2) := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h : x ≤ N / 2
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have h4 := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  omega

/-- **Step:** Selberg's bound, the multiples count at any shift and the lower
bound for the twin sum give Selberg's bound for Goldbach pairs. -/
theorem selberg_goldbach_bound_step (h_sb : RNS.SelbergBound.selberg_bound)
    (h_sc : RNS.BrunTwinCount.shift_multiples_count) (h_low : twin_selberg_sum_lower) :
    selberg_goldbach_bound := by
  intro N hN
  obtain ⟨t, ht5184, hlo, hLpos, hy1, hGlow, ht6, hz⟩ := twin_parameters h_low N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hNpos
  -- the cut-off is at most N / 2
  have hzN : 2 * (t ^ 2 + 1) ≤ N := by
    have h6 : 2 ^ 6 ≤ t ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have h1 : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h48 : 4 * t ^ 2 ≤ t ^ 8 := by
      calc 4 * t ^ 2 ≤ t ^ 6 * t ^ 2 := Nat.mul_le_mul_right _ (by norm_num at h6 ⊢; omega)
        _ = t ^ 8 := by ring
    omega
  -- the shift
  obtain ⟨Qp, hQp⟩ : ∃ Qp, Qp = ∏ p ∈ shiftWheels N (t ^ 2 + 1), p := ⟨_, rfl⟩
  have hQp1 : 1 ≤ Qp := by
    rw [hQp]
    exact Finset.prod_pos (fun p hp => (shiftWheels_prime hp).pos)
  obtain ⟨c, hc⟩ : ∃ c, c = (Qp - 1) * N := ⟨_, rfl⟩
  have hiff : ∀ p ∈ twin_wheels (t ^ 2 + 1), p ∣ c ↔ p ∣ N := by
    intro p hp
    have hpP := twin_wheels_prime hp
    constructor
    · intro hpc
      rw [hc] at hpc
      rcases (Nat.Prime.dvd_mul hpP).mp hpc with h1 | h1
      · by_contra hpN
        have hmem : p ∈ shiftWheels N (t ^ 2 + 1) := Finset.mem_filter.mpr ⟨hp, hpN⟩
        have hpQ : p ∣ Qp := by
          rw [hQp]
          exact Finset.dvd_prod_of_mem (fun q => q) hmem
        have h2 : p ∣ Qp - 1 + 1 := by
          rw [show Qp - 1 + 1 = Qp by omega]
          exact hpQ
        have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
        exact hpP.one_lt.ne' (Nat.dvd_one.mp h3)
      · exact h1
    · intro hpN
      rw [hc]
      exact Dvd.dvd.mul_left hpN _
  have hWc : shiftWheels c (t ^ 2 + 1) = shiftWheels N (t ^ 2 + 1) := by
    unfold shiftWheels
    exact Finset.filter_congr (fun p hp => not_congr (hiff p hp))
  have hBc : badWheels c (t ^ 2 + 1) = badWheels N (t ^ 2 + 1) := by
    unfold badWheels
    exact Finset.filter_congr (fun p hp => hiff p hp)
  -- Goldbach pairs from the cut-off up survive the shifted sieve
  have hW : ∀ p ∈ shiftWheels N (t ^ 2 + 1), p.Prime := fun p hp => shiftWheels_prime hp
  have hsurv : ((Finset.Ioc 0 (N / 2)).filter (fun m => m.Prime ∧ (N - m).Prime)).card ≤
      (t ^ 2 + 1) + ((Finset.Ioc 0 (N / 2)).filter
        (fun m => Nat.Coprime (∏ p ∈ shiftWheels N (t ^ 2 + 1), p) (m * (m + c)))).card := by
    have hsub : (Finset.Ioc 0 (N / 2)).filter (fun m => m.Prime ∧ (N - m).Prime) ⊆
        Finset.range (t ^ 2 + 1) ∪ (Finset.Ioc 0 (N / 2)).filter
          (fun m => Nat.Coprime (∏ p ∈ shiftWheels N (t ^ 2 + 1), p) (m * (m + c))) := by
      intro n hn
      obtain ⟨hnN, hp, hq⟩ := Finset.mem_filter.mp hn
      have hnN' := Finset.mem_Ioc.mp hnN
      rw [Finset.mem_union, Finset.mem_range, Finset.mem_filter]
      by_cases hnz : n < t ^ 2 + 1
      · exact Or.inl hnz
      · right
        refine ⟨hnN, Nat.Coprime.mul_right ?_ ?_⟩
        · refine ((hp.coprime_iff_not_dvd).mpr (fun hd => hnz ?_)).symm
          exact (mem_twin_wheels.mp (shiftWheels_mem (mem_of_prime_dvd_prod hW hp hd)).1).2.1
        · refine Nat.Coprime.prod_left (fun p hp' => ?_)
          have hpP := shiftWheels_prime hp'
          refine (hpP.coprime_iff_not_dvd).mpr (fun hpd => ?_)
          have hpQ : p ∣ Qp := by
            rw [hQp]
            exact Finset.dvd_prod_of_mem (fun q => q) hp'
          have hid : n + c + (N - n) = Qp * N := by
            obtain ⟨k, hk⟩ : ∃ k, Qp = k + 1 := ⟨Qp - 1, by omega⟩
            rw [hc, hk, Nat.add_sub_cancel]
            have hnle : n ≤ N := by omega
            calc n + k * N + (N - n) = k * N + (n + (N - n)) := by ring
              _ = k * N + N := by rw [Nat.add_sub_of_le hnle]
              _ = (k + 1) * N := by ring
          have h1 : p ∣ n + c + (N - n) := by
            rw [hid]
            exact Dvd.dvd.mul_right hpQ N
          have h2 : p ∣ N - n := (Nat.dvd_add_right hpd).mp h1
          have h3 : p = N - n := (Nat.prime_dvd_prime_iff_eq hpP hq).mp h2
          have h4 := (mem_twin_wheels.mp (shiftWheels_mem hp').1).2.1
          omega
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_range]
  set Q := (N : ℝ) / Real.log N ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hGpos : 0 < twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) :=
    lt_of_lt_of_le (by positivity) hGlow
  have hcore := shift_core h_sb h_sc c (N / 2) (t ^ 2 + 1) ((t : ℝ) ^ 2) hy1 hGpos
  rw [hWc, hBc] at hcore
  have hE := error_le_of (shiftWheels N (t ^ 2 + 1))
    (fun p hp => ⟨shiftWheels_prime hp, twin_wheels_five (shiftWheels_mem hp).1⟩) t
  have hcount : (goldbach_count N : ℝ) ≤ 2 * ((t : ℝ) ^ 2 + 1 + (((Finset.Ioc 0 (N / 2)).filter
      (fun m => Nat.Coprime (∏ p ∈ shiftWheels N (t ^ 2 + 1), p) (m * (m + c)))).card : ℝ)) := by
    have := (goldbach_half N).trans (Nat.mul_le_mul_left 2 hsurv)
    exact_mod_cast this
  have hX : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
  have hdivG : ((N / 2 : ℕ) : ℝ) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) ≤ 18432 * Q := by
    have hpos : 0 < Real.log N ^ 2 / 36864 := by positivity
    calc ((N / 2 : ℕ) : ℝ) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2)
        ≤ ((N : ℝ) / 2) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hX hGpos.le
      _ ≤ ((N : ℝ) / 2) / (Real.log N ^ 2 / 36864) :=
          div_le_div_of_nonneg_left (by positivity) hpos hGlow
      _ = 18432 * Q := by rw [hQ]; field_simp; ring
  have hF := bad_le_pair_factor N (t ^ 2 + 1) hN0
  have hF1 := one_le_pair_factor N
  have hmain : (∏ p ∈ badWheels N (t ^ 2 + 1), (1 + 2 / ((p : ℝ) - 2))) * ((N / 2 : ℕ) : ℝ) /
      twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2) ≤ 18432 * (pair_factor N * Q) := by
    rw [mul_div_assoc]
    calc (∏ p ∈ badWheels N (t ^ 2 + 1), (1 + 2 / ((p : ℝ) - 2))) *
          (((N / 2 : ℕ) : ℝ) / twin_selberg_sum (t ^ 2 + 1) ((t : ℝ) ^ 2))
        ≤ pair_factor N * (18432 * Q) :=
          mul_le_mul hF hdivG (div_nonneg (Nat.cast_nonneg _) hGpos.le) (by linarith)
      _ = 18432 * (pair_factor N * Q) := by ring
  have hPQ : Q ≤ pair_factor N * Q := le_mul_of_one_le_left hQ0 hF1
  rw [show 40000 * pair_factor N * (N : ℝ) / Real.log N ^ 2 = 40000 * (pair_factor N * Q) by
    rw [hQ]; ring]
  linarith

end RNS.SelbergTwinRails

#print axioms RNS.SelbergTwinRails.selberg_twin_columns_bound_step
#print axioms RNS.SelbergTwinRails.twin_selberg_sum_lower_holds
#print axioms RNS.SelbergTwinRails.selberg_twin_bound_step
#print axioms RNS.SelbergTwinRails.selberg_gap_bound_step
#print axioms RNS.SelbergTwinRails.selberg_goldbach_bound_step
