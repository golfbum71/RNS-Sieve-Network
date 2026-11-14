/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib
import RNSNetwork.Nodes.Schnirelmann.Conclusions

/-!
# Proofs for Schnirelmann

Draft (2026-11-14): not yet built.

Imports claims only.

* `goldbach_first_moment`: a pair of primes up to `N` is a Goldbach pair of
  its sum, which is at most `2 * N` (Mathlib only).
* `pair_factor_second_moment`: the square of the factor is a product, over
  the wheels from 5 up dividing the number, of one plus a small term; multiply
  out, count the multiples of each product of wheels, and bound the resulting
  product over all wheels by the exponential of a convergent sum (Mathlib
  only).
* `goldbach_second_moment`: a step from `SelbergTwinRails.selberg_goldbach_bound`
  and `pair_factor_second_moment`.
* `prime_pair_sums_density`: a step from the two moments, by Cauchy–Schwarz
  and Mathlib's Chebyshev lower bound for the number of primes.
* `schnirelmann_inequality`: by counting, one number at a time, behind the
  last member of the first set (Mathlib only).
* `schnirelmann_basis`: a step from `schnirelmann_inequality`.
* `schnirelmann_bounded_sum`: a step from `prime_pair_sums_density` and
  `schnirelmann_basis`.
-/

open scoped Pointwise

namespace RNS.Schnirelmann

open RNS.SelbergTwinRails

/-! ## The first moment -/

theorem goldbach_first_moment_holds : goldbach_first_moment := by
  intro N
  have hT : ∑ n ∈ Finset.range (2 * N + 1), goldbach_count n
      = ((Finset.range (2 * N + 1)).sigma
          (fun n => (Finset.Ioo 0 n).filter (fun k => k.Prime ∧ (n - k).Prime))).card :=
    (Finset.card_sigma _ _).symm
  have hP : Nat.primeCounting N ^ 2 = ((Nat.primesLE N) ×ˢ (Nat.primesLE N)).card := by
    rw [Finset.card_product, Nat.primesLE_card_eq_primeCounting, sq]
  rw [hT, hP]
  refine Finset.card_le_card_of_injOn (fun x => (⟨x.1 + x.2, x.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
    obtain ⟨h1le, h1p⟩ := Nat.mem_primesLE.mp h1
    obtain ⟨h2le, h2p⟩ := Nat.mem_primesLE.mp h2
    have hpos2 := h2p.pos
    have hlt : x.1 + x.2 < 2 * N + 1 := by omega
    have hlt2 : x.1 < x.1 + x.2 := by omega
    have hpr : (x.1 + x.2 - x.1).Prime := by
      rw [Nat.add_sub_cancel_left]
      exact h2p
    exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hlt,
      Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨h1p.pos, hlt2⟩, h1p, hpr⟩⟩)
  · intro x _ y _ hxy
    simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
    obtain ⟨e1, e2⟩ := hxy
    exact Prod.ext e2 (by omega)

/-! ## The Selberg factor on average -/

/-- The extra term of one wheel in the square of the factor. -/
private noncomputable def gf (p : ℕ) : ℝ := ((p : ℝ) / ((p : ℝ) - 2)) ^ 2 - 1

private theorem gf_nonneg {p : ℕ} (hp : 5 ≤ p) : 0 ≤ gf p := by
  have hx : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : 1 ≤ (p : ℝ) / ((p : ℝ) - 2) := by
    rw [one_le_div₀ (by linarith)]
    linarith
  have h2 : 1 ≤ ((p : ℝ) / ((p : ℝ) - 2)) ^ 2 := one_le_pow₀ h1
  unfold gf
  linarith

private theorem gf_div_le {p : ℕ} (hp : 5 ≤ p) : gf p / p ≤ 9 * (1 / (p : ℝ) ^ 2) := by
  have hx : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hx0 : (0 : ℝ) < p := by linarith
  have hx2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h1 : ((p : ℝ) / ((p : ℝ) - 2)) ^ 2 ≤ ((p : ℝ) + 9) / p := by
    rw [div_pow, div_le_div_iff₀ (pow_pos hx2 2) hx0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx)]
  have h2 : ((p : ℝ) + 9) / p = 1 + 9 / p := by
    rw [add_div, div_self hx0.ne']
  have h3 : gf p ≤ 9 / p := by
    unfold gf
    linarith
  calc gf p / p ≤ 9 / (p : ℝ) / p := div_le_div_of_nonneg_right h3 hx0.le
    _ = 9 * (1 / (p : ℝ) ^ 2) := by
      rw [div_div, ← sq]
      ring

theorem pair_factor_second_moment_holds : pair_factor_second_moment := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine ⟨Real.exp (9 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2), Real.exp_pos _, fun N => ?_⟩
  obtain ⟨W, hW⟩ : ∃ W : Finset ℕ,
      W = (Finset.range (N + 1)).filter (fun p => p.Prime ∧ 5 ≤ p) := ⟨_, rfl⟩
  have hWmem : ∀ p, p ∈ W ↔ p < N + 1 ∧ p.Prime ∧ 5 ≤ p := by
    intro p
    rw [hW, Finset.mem_filter, Finset.mem_range]
  have hG0 : ∀ D ∈ W.powerset, 0 ≤ ∏ p ∈ D, gf p := fun D hD =>
    Finset.prod_nonneg
      (fun p hp => gf_nonneg ((hWmem p).mp (Finset.mem_powerset.mp hD hp)).2.2)
  -- one number: its squared factor, multiplied out over sets of wheels
  have ha : ∀ n ∈ Finset.Ioc 0 N, pair_factor n ^ 2
      ≤ ∑ D ∈ W.powerset, if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, gf p else 0 := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hsub : n.primeFactors.filter (fun p => 5 ≤ p) ⊆ W := by
      intro p hp
      obtain ⟨hp1, hp5⟩ := Finset.mem_filter.mp hp
      have hple := Nat.le_of_mem_primeFactors hp1
      exact (hWmem p).mpr ⟨by omega, Nat.prime_of_mem_primeFactors hp1, hp5⟩
    have e1 : pair_factor n ^ 2
        = ∑ D ∈ (n.primeFactors.filter (fun p => 5 ≤ p)).powerset, ∏ p ∈ D, gf p := by
      unfold pair_factor
      rw [← Finset.prod_pow, ← Finset.prod_one_add]
      refine Finset.prod_congr rfl (fun p _ => ?_)
      unfold gf
      ring
    have e2 : ∀ D ∈ (n.primeFactors.filter (fun p => 5 ≤ p)).powerset,
        ∏ p ∈ D, gf p = if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, gf p else 0 := by
      intro D hD
      have hDs := Finset.mem_powerset.mp hD
      have hdvd : (∏ p ∈ D, p) ∣ n :=
        Finset.prod_primes_dvd n
          (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (hDs hp)).1).prime)
          (fun p hp => Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp (hDs hp)).1)
      exact (ite_eq_left hdvd).symm
    rw [e1, Finset.sum_congr rfl e2]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.powerset_mono.mpr hsub)
      (fun D hD _ => ?_)
    split_ifs
    · exact hG0 D hD
    · exact le_refl 0
  -- all numbers up to N: count the multiples of each product of wheels
  have hb : ∑ n ∈ Finset.Ioc 0 N, pair_factor n ^ 2
      ≤ ∑ D ∈ W.powerset, (∏ p ∈ D, gf p) * ((N : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)) := by
    calc ∑ n ∈ Finset.Ioc 0 N, pair_factor n ^ 2
        ≤ ∑ n ∈ Finset.Ioc 0 N, ∑ D ∈ W.powerset,
            if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, gf p else 0 := Finset.sum_le_sum ha
      _ = ∑ D ∈ W.powerset, ∑ n ∈ Finset.Ioc 0 N,
            if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, gf p else 0 := Finset.sum_comm
      _ ≤ ∑ D ∈ W.powerset, (∏ p ∈ D, gf p) * ((N : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum (fun D hD => ?_)
          have hcount : ∑ n ∈ Finset.Ioc 0 N, (if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, gf p else 0)
              = ((N / ∏ p ∈ D, p : ℕ) : ℝ) * ∏ p ∈ D, gf p := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
              Nat.Ioc_filter_dvd_card_eq_div]
          rw [hcount, mul_comm ((N / ∏ p ∈ D, p : ℕ) : ℝ) (∏ p ∈ D, gf p)]
          exact mul_le_mul_of_nonneg_left Nat.cast_div_le (hG0 D hD)
  -- the sum over sets of wheels is a product over the wheels
  have hd : ∑ D ∈ W.powerset, (∏ p ∈ D, gf p) * ((N : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ))
      = N * ∏ p ∈ W, (1 + gf p / p) := by
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    rw [Finset.prod_div_distrib, Nat.cast_prod]
    ring
  -- the product is bounded
  have he : ∏ p ∈ W, (1 + gf p / p) ≤ Real.exp (9 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) := by
    calc ∏ p ∈ W, (1 + gf p / p) ≤ ∏ p ∈ W, Real.exp (gf p / p) := by
          refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
          · exact add_nonneg zero_le_one
              (div_nonneg (gf_nonneg ((hWmem p).mp hp).2.2) (Nat.cast_nonneg p))
          · linarith [Real.add_one_le_exp (gf p / p)]
      _ = Real.exp (∑ p ∈ W, gf p / p) := (Real.exp_sum W _).symm
      _ ≤ Real.exp (9 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          have hW2 : ∑ p ∈ W, 1 / (p : ℝ) ^ 2 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
            hsum.sum_le_tsum W (fun n _ => by
              show (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2
              positivity)
          calc ∑ p ∈ W, gf p / p ≤ ∑ p ∈ W, 9 * (1 / (p : ℝ) ^ 2) :=
                Finset.sum_le_sum (fun p hp => gf_div_le ((hWmem p).mp hp).2.2)
            _ = 9 * ∑ p ∈ W, 1 / (p : ℝ) ^ 2 := by rw [Finset.mul_sum]
            _ ≤ 9 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hW2 (by norm_num)
  calc ∑ n ∈ Finset.Ioc 0 N, pair_factor n ^ 2
      ≤ ∑ D ∈ W.powerset, (∏ p ∈ D, gf p) * ((N : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)) := hb
    _ = N * ∏ p ∈ W, (1 + gf p / p) := hd
    _ ≤ N * Real.exp (9 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)
    _ = Real.exp (9 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) * N := mul_comm _ _

/-! ## The second moment -/

/-- For `2 ≤ a ≤ b`: `e^a b² ≤ e^b a²` (a number over its squared logarithm
grows from `e²` on). -/
private theorem exp_sq_mono {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    Real.exp a * b ^ 2 ≤ Real.exp b * a ^ 2 := by
  have h1 : (b - a) / 2 + 1 ≤ Real.exp ((b - a) / 2) := Real.add_one_le_exp _
  have he : b ≤ a * Real.exp ((b - a) / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ a),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a - 2) (by linarith : (0 : ℝ) ≤ (b - a) / 2)]
  have hE : Real.exp ((b - a) / 2) ^ 2 = Real.exp (b - a) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsq : b ^ 2 ≤ (a * Real.exp ((b - a) / 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) he 2
  have hba : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp a * b ^ 2 ≤ Real.exp a * (a * Real.exp ((b - a) / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos a).le
    _ = Real.exp a * Real.exp (b - a) * a ^ 2 := by
        rw [mul_pow, hE]
        ring
    _ = Real.exp b * a ^ 2 := by rw [hba]

private theorem goldbach_count_le (n : ℕ) : goldbach_count n ≤ n := by
  unfold goldbach_count
  calc ((Finset.Ioo 0 n).filter (fun k => k.Prime ∧ (n - k).Prime)).card
      ≤ (Finset.Ioo 0 n).card := Finset.card_filter_le _ _
    _ = n - 0 - 1 := Nat.card_Ioo 0 n
    _ ≤ n := by omega

/-- Step: the second moment from Selberg's bound for Goldbach pairs and the
factor on average. -/
theorem goldbach_second_moment_step (hsel : RNS.SelbergTwinRails.selberg_goldbach_bound)
    (h2 : pair_factor_second_moment) : goldbach_second_moment := by
  obtain ⟨C2, hC2, hmom⟩ := h2
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 5184 ^ 8 := ⟨_, rfl⟩
  refine ⟨1 + 1600000000 * C2, by linarith, 16 * K ^ 3, fun N hN => ?_⟩
  have hKr : (K : ℝ) = (5184 : ℝ) ^ 8 := by
    rw [hK]
    norm_num
  have hK9 : (9 : ℝ) ≤ K := by
    rw [hKr]
    norm_num
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  have hK3 : K ≤ K ^ 3 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 3 := Nat.pow_le_pow_right hK1 (by norm_num)
  have hKN : K ≤ N + 1 := by omega
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNr : (16 : ℝ) * (K : ℝ) ^ 3 ≤ N := by exact_mod_cast hN
  -- log⁴ N ≤ 16 N²
  have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hlog : Real.log N = 2 * Real.log (Real.sqrt N) := by
    rw [Real.log_sqrt hNpos.le]
    ring
  have hl1 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 := Real.log_le_sub_one_of_pos hspos
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hL2 : Real.log N ≤ 2 * Real.sqrt N := by linarith
  have hL4 : Real.log N ^ 4 ≤ 16 * (N : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ hL0 hL2 4
    have e : (2 * Real.sqrt N) ^ 4 = 16 * (Real.sqrt N ^ 2) ^ 2 := by ring
    rw [e, hs2] at h
    exact h
  -- e² ≤ K
  have hexp2 : Real.exp 2 ≤ K := by
    have he1 := Real.exp_one_lt_d9
    have hpos := Real.exp_pos 1
    have h2e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * Real.exp 1 :=
      mul_le_mul_of_nonneg_right he1.le hpos.le
    rw [h2e]
    linarith
  -- the numbers below K
  have hA : ∑ n ∈ Finset.range K, (goldbach_count n : ℝ) ^ 2 ≤ (K : ℝ) ^ 3 := by
    calc ∑ n ∈ Finset.range K, (goldbach_count n : ℝ) ^ 2
        ≤ ∑ _n ∈ Finset.range K, (K : ℝ) ^ 2 := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hle : goldbach_count n ≤ K :=
            (goldbach_count_le n).trans (Finset.mem_range.mp hn).le
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) 2
      _ = (K : ℝ) * (K : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (K : ℝ) ^ 3 := by ring
  -- the numbers from K on
  have hB : ∀ n ∈ Finset.Ico K (N + 1),
      (goldbach_count n : ℝ) ^ 2 * Real.log N ^ 4
        ≤ 1600000000 * (N : ℝ) ^ 2 * pair_factor n ^ 2 := by
    intro n hn
    obtain ⟨hKn, hnN⟩ := Finset.mem_Ico.mp hn
    have hKn' : (K : ℝ) ≤ n := by exact_mod_cast hKn
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast (Nat.lt_succ_iff.mp hnN)
    have hnpos : (0 : ℝ) < n := by linarith
    have hs := hsel n (by rw [← hKr]; exact hKn')
    have hlog2 : 2 ≤ Real.log n := (Real.le_log_iff_exp_le hnpos).mpr (hexp2.trans hKn')
    have hm := exp_sq_mono hlog2 (Real.log_le_log hnpos hnN')
    rw [Real.exp_log hnpos, Real.exp_log hNpos] at hm
    have hlogsq : 0 < Real.log n ^ 2 := pow_pos (by linarith) 2
    have hs' : (goldbach_count n : ℝ) * Real.log n ^ 2 ≤ 40000 * pair_factor n * n :=
      (le_div_iff₀ hlogsq).mp hs
    have h3 : (goldbach_count n : ℝ) * Real.log N ^ 2 * n
        ≤ 40000 * pair_factor n * N * n := by
      calc (goldbach_count n : ℝ) * Real.log N ^ 2 * n
          = (goldbach_count n : ℝ) * (n * Real.log N ^ 2) := by ring
        _ ≤ (goldbach_count n : ℝ) * (N * Real.log n ^ 2) :=
            mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
        _ = N * ((goldbach_count n : ℝ) * Real.log n ^ 2) := by ring
        _ ≤ N * (40000 * pair_factor n * n) := mul_le_mul_of_nonneg_left hs' hNpos.le
        _ = 40000 * pair_factor n * N * n := by ring
    have h4 : (goldbach_count n : ℝ) * Real.log N ^ 2 ≤ 40000 * pair_factor n * N :=
      le_of_mul_le_mul_right h3 hnpos
    have h0 : 0 ≤ (goldbach_count n : ℝ) * Real.log N ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have h5 := pow_le_pow_left₀ h0 h4 2
    calc (goldbach_count n : ℝ) ^ 2 * Real.log N ^ 4
        = ((goldbach_count n : ℝ) * Real.log N ^ 2) ^ 2 := by ring
      _ ≤ (40000 * pair_factor n * N) ^ 2 := h5
      _ = 1600000000 * (N : ℝ) ^ 2 * pair_factor n ^ 2 := by ring
  have hsubset : Finset.Ico K (N + 1) ⊆ Finset.Ioc 0 N := by
    intro n hn
    obtain ⟨hKn, hnN⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hBsum : (∑ n ∈ Finset.Ico K (N + 1), (goldbach_count n : ℝ) ^ 2) * Real.log N ^ 4
      ≤ 1600000000 * (N : ℝ) ^ 2 * (C2 * N) := by
    rw [Finset.sum_mul]
    calc ∑ n ∈ Finset.Ico K (N + 1), (goldbach_count n : ℝ) ^ 2 * Real.log N ^ 4
        ≤ ∑ n ∈ Finset.Ico K (N + 1), 1600000000 * (N : ℝ) ^ 2 * pair_factor n ^ 2 :=
          Finset.sum_le_sum hB
      _ = 1600000000 * (N : ℝ) ^ 2 * ∑ n ∈ Finset.Ico K (N + 1), pair_factor n ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ 1600000000 * (N : ℝ) ^ 2 * ∑ n ∈ Finset.Ioc 0 N, pair_factor n ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => sq_nonneg _))
            (by positivity)
      _ ≤ 1600000000 * (N : ℝ) ^ 2 * (C2 * N) :=
          mul_le_mul_of_nonneg_left (hmom N) (by positivity)
  have hAsum : (∑ n ∈ Finset.range K, (goldbach_count n : ℝ) ^ 2) * Real.log N ^ 4
      ≤ (N : ℝ) ^ 3 := by
    calc (∑ n ∈ Finset.range K, (goldbach_count n : ℝ) ^ 2) * Real.log N ^ 4
        ≤ (K : ℝ) ^ 3 * (16 * (N : ℝ) ^ 2) :=
          mul_le_mul hA hL4 (by positivity) (by positivity)
      _ = 16 * (K : ℝ) ^ 3 * (N : ℝ) ^ 2 := by ring
      _ ≤ N * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hNr (by positivity)
      _ = (N : ℝ) ^ 3 := by ring
  have hsplit := Finset.sum_range_add_sum_Ico (fun n => (goldbach_count n : ℝ) ^ 2) hKN
  calc (∑ n ∈ Finset.range (N + 1), (goldbach_count n : ℝ) ^ 2) * Real.log N ^ 4
      = (∑ n ∈ Finset.range K, (goldbach_count n : ℝ) ^ 2) * Real.log N ^ 4
        + (∑ n ∈ Finset.Ico K (N + 1), (goldbach_count n : ℝ) ^ 2) * Real.log N ^ 4 := by
        rw [← hsplit, add_mul]
    _ ≤ (N : ℝ) ^ 3 + 1600000000 * (N : ℝ) ^ 2 * (C2 * N) := add_le_add hAsum hBsum
    _ = (1 + 1600000000 * C2) * (N : ℝ) ^ 3 := by ring

/-! ## A positive share -/

private theorem share_arith {N P L S1 S2 t C : ℝ} (hN : 0 < N) (hP : N / 6 ≤ P * L)
    (hS1 : P ^ 2 ≤ S1) (hcs : S1 ^ 2 ≤ S2 * t) (hmom : S2 * L ^ 4 ≤ C * N ^ 3)
    (ht : 0 ≤ t) : N / 1296 ≤ C * t := by
  have hN6 : 0 ≤ N / 6 := div_nonneg hN.le (by norm_num)
  have e1 : (N / 6) ^ 2 ≤ S1 * L ^ 2 := by
    calc (N / 6) ^ 2 ≤ (P * L) ^ 2 := pow_le_pow_left₀ hN6 hP 2
      _ = P ^ 2 * L ^ 2 := by ring
      _ ≤ S1 * L ^ 2 := mul_le_mul_of_nonneg_right hS1 (sq_nonneg L)
  have e2 : ((N / 6) ^ 2) ^ 2 ≤ (S1 * L ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) e1 2
  have hL4 : 0 ≤ L ^ 4 := by positivity
  have e3 : (S1 * L ^ 2) ^ 2 ≤ C * N ^ 3 * t := by
    calc (S1 * L ^ 2) ^ 2 = S1 ^ 2 * L ^ 4 := by ring
      _ ≤ S2 * t * L ^ 4 := mul_le_mul_of_nonneg_right hcs hL4
      _ = S2 * L ^ 4 * t := by ring
      _ ≤ C * N ^ 3 * t := mul_le_mul_of_nonneg_right hmom ht
  have e4 : N ^ 3 * (N / 1296) ≤ N ^ 3 * (C * t) := by
    have i1 : ((N / 6) ^ 2) ^ 2 = N ^ 3 * (N / 1296) := by ring
    have i2 : C * N ^ 3 * t = N ^ 3 * (C * t) := by ring
    linarith
  exact le_of_mul_le_mul_left e4 (pow_pos hN 3)

/-- Step: positive density of the sums of two primes, from the two moments. -/
theorem prime_pair_sums_density_step (h1 : goldbach_first_moment)
    (h3 : goldbach_second_moment) : prime_pair_sums_density := by
  classical
  obtain ⟨C, hC, N₀, hmom⟩ := h3
  have hlarge : ∀ N : ℕ, N₀ ≤ N → 8 ≤ N →
      (N : ℝ) / 1296
        ≤ C * (((Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums)).card : ℝ) := by
    intro N hN₀ hN8
    have hNpos : (0 : ℝ) < N := by
      have : (8 : ℝ) ≤ N := by exact_mod_cast hN8
      linarith
    -- a number with a Goldbach pair is in the set
    have hmemT : ∀ n ∈ Finset.range (N + 1), goldbach_count n ≠ 0 →
        n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums) := by
      intro n hn hne
      have hnN := Finset.mem_range.mp hn
      unfold goldbach_count at hne
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      obtain ⟨hkI, hkp, hnk⟩ := Finset.mem_filter.mp hk
      have hkI' := Finset.mem_Ioo.mp hkI
      have hpps : n ∈ prime_pair_sums :=
        Or.inr (Or.inr ⟨k, n - k, hkp, hnk, by omega⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hpps⟩
    -- Cauchy–Schwarz
    have hfg : ∀ n ∈ Finset.range (N + 1),
        (goldbach_count n : ℝ)
            * (if n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums)
                then (1 : ℝ) else 0)
          = (goldbach_count n : ℝ) := by
      intro n hn
      by_cases h0 : goldbach_count n = 0
      · rw [h0, Nat.cast_zero, zero_mul]
      · rw [ite_eq_left (hmemT n hn h0), mul_one]
    have hg2 : ∀ n ∈ Finset.range (N + 1),
        (if n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums)
            then (1 : ℝ) else 0) ^ 2
          = (if n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums)
              then (1 : ℝ) else 0) := by
      intro n _
      split_ifs <;> norm_num
    have hgsum : ∑ n ∈ Finset.range (N + 1),
          (if n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums)
            then (1 : ℝ) else 0)
        ≤ (((Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums)).card : ℝ) := by
      rw [← Finset.natCast_card_filter]
      exact_mod_cast Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + 1))
      (fun n => (goldbach_count n : ℝ))
      (fun n => if n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums)
        then (1 : ℝ) else 0)
    beta_reduce at hcs
    rw [Finset.sum_congr rfl hfg, Finset.sum_congr rfl hg2] at hcs
    have hS2nn : 0 ≤ ∑ n ∈ Finset.range (N + 1), (goldbach_count n : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun n _ => sq_nonneg _)
    have hcs' : (∑ n ∈ Finset.range (N + 1), (goldbach_count n : ℝ)) ^ 2
        ≤ (∑ n ∈ Finset.range (N + 1), (goldbach_count n : ℝ) ^ 2)
          * (((Finset.Ioc 0 N).filter (fun n => n ∈ prime_pair_sums)).card : ℝ) :=
      hcs.trans (mul_le_mul_of_nonneg_left hgsum hS2nn)
    -- the first moment and Chebyshev
    have h4 : 4 ≤ N / 2 := by omega
    have hnat : Nat.primeCounting (N / 2) ^ 2
        ≤ ∑ n ∈ Finset.range (N + 1), goldbach_count n :=
      (h1 (N / 2)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
          (fun _ _ _ => Nat.zero_le _))
    have hS1 : (Nat.primeCounting (N / 2) : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.range (N + 1), (goldbach_count n : ℝ) := by
      exact_mod_cast hnat
    have hM1 : (1 : ℝ) < ((N / 2 : ℕ) : ℝ) := by
      have : (4 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h4
      linarith
    have hMN : ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N 2
    have hM3 : (N : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) := by
      have : N ≤ 3 * (N / 2) := by omega
      exact_mod_cast this
    have hlogM : 0 < Real.log ((N / 2 : ℕ) : ℝ) := Real.log_pos hM1
    have hc := Chebyshev.pi_ge_of_four_le h4
    have hc' : ((N / 2 : ℕ) : ℝ) * Real.log 2
        ≤ (Nat.primeCounting (N / 2) : ℝ) * Real.log ((N / 2 : ℕ) : ℝ) :=
      (div_le_iff₀ hlogM).mp hc
    have hmono : Real.log ((N / 2 : ℕ) : ℝ) ≤ Real.log N :=
      Real.log_le_log (by linarith) hMN
    have h5 : (Nat.primeCounting (N / 2) : ℝ) * Real.log ((N / 2 : ℕ) : ℝ)
        ≤ (Nat.primeCounting (N / 2) : ℝ) * Real.log N :=
      mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h6 : ((N / 2 : ℕ) : ℝ) * (1 / 2) ≤ ((N / 2 : ℕ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
    have hP : (N : ℝ) / 6 ≤ (Nat.primeCounting (N / 2) : ℝ) * Real.log N := by linarith
    exact share_arith hNpos hP hS1 hcs' (hmom N hN₀) (Nat.cast_nonneg _)
  -- the density
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = max N₀ 8 := ⟨_, rfl⟩
  have hM0 : N₀ ≤ M := by rw [hM]; exact le_max_left _ _
  have hM8 : 8 ≤ M := by rw [hM]; exact le_max_right _ _
  have hMpos : (0 : ℝ) < M := by
    have : (8 : ℝ) ≤ M := by exact_mod_cast hM8
    linarith
  have hCpos : (0 : ℝ) < 1296 * C := mul_pos (by norm_num) hC
  have hδ : min (1 / (1296 * C)) (1 / (M : ℝ)) ≤ schnirelmannDensity prime_pair_sums := by
    rw [le_schnirelmannDensity_iff]
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases hnM : M ≤ n
    · have hl := hlarge n (hM0.trans hnM) (hM8.trans hnM)
      have hl' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1296)).mp hl
      refine (min_le_left _ _).trans ?_
      rw [le_div_iff₀ hn', div_mul_eq_mul_div, div_le_iff₀ hCpos]
      linarith
    · have hnlt : n ≤ M := (not_le.mp hnM).le
      have h1mem : 1 ∈ (Finset.Ioc 0 n).filter (fun a => a ∈ prime_pair_sums) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.one_pos, hn⟩, Or.inr (Or.inl rfl)⟩
      have hcard : 0 < ((Finset.Ioc 0 n).filter (fun a => a ∈ prime_pair_sums)).card :=
        Finset.card_pos.mpr ⟨1, h1mem⟩
      have ht : (1 : ℝ) ≤ (((Finset.Ioc 0 n).filter (fun a => a ∈ prime_pair_sums)).card : ℝ) := by
        exact_mod_cast hcard
      refine (min_le_right _ _).trans ?_
      calc 1 / (M : ℝ) ≤ 1 / (n : ℝ) :=
            one_div_le_one_div_of_le hn' (by exact_mod_cast hnlt)
        _ ≤ (((Finset.Ioc 0 n).filter (fun a => a ∈ prime_pair_sums)).card : ℝ) / n :=
            div_le_div_of_nonneg_right ht hn'.le
  exact lt_of_lt_of_le (lt_min (one_div_pos.mpr hCpos) (one_div_pos.mpr hMpos)) hδ

/-! ## Schnirelmann's inequality -/

/-- The number of members of `X` from 1 to `n`, as a sum of ones. -/
private noncomputable def cnt (X : Set ℕ) [DecidablePred (· ∈ X)] (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 n, if k ∈ X then (1 : ℝ) else 0

private theorem cnt_eq (X : Set ℕ) [DecidablePred (· ∈ X)] (n : ℕ) :
    (((Finset.Ioc 0 n).filter (fun a => a ∈ X)).card : ℝ) = cnt X n :=
  Finset.natCast_card_filter _ _

private theorem cnt_succ (X : Set ℕ) [DecidablePred (· ∈ X)] (n : ℕ) :
    cnt X (n + 1) = cnt X n + if n + 1 ∈ X then (1 : ℝ) else 0 :=
  Finset.sum_Ioc_succ_top (Nat.zero_le n) _

private theorem cnt_zero (X : Set ℕ) [DecidablePred (· ∈ X)] : cnt X 0 = 0 := by
  unfold cnt
  rw [Finset.Ioc_self, Finset.sum_empty]

private theorem density_le_cnt (X : Set ℕ) [DecidablePred (· ∈ X)] (n : ℕ) :
    schnirelmannDensity X * n ≤ cnt X n := by
  rw [← cnt_eq]
  exact schnirelmannDensity_mul_le_card_filter

/-- Behind the last member `a` of `A` up to `n`, every member of `B` up to
`n - a` gives a member of the sumset. -/
private theorem gap_invariant {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] (hA : 0 ∈ A) (hB : 0 ∈ B) (n : ℕ) :
    ∃ a : ℕ, a ≤ n ∧ a ∈ A ∧
      cnt A n + schnirelmannDensity B * ((a : ℝ) - cnt A n) + cnt B (n - a)
        ≤ cnt (A + B) n := by
  induction n with
  | zero =>
    refine ⟨0, le_refl 0, hA, ?_⟩
    rw [Nat.sub_zero, cnt_zero A, cnt_zero B, cnt_zero (A + B), Nat.cast_zero]
    norm_num
  | succ n ih =>
    obtain ⟨a, han, haA, hinv⟩ := ih
    have hβ := density_le_cnt B (n - a)
    rw [Nat.cast_sub han] at hβ
    by_cases hmem : n + 1 ∈ A
    · refine ⟨n + 1, le_refl _, hmem, ?_⟩
      have hC : n + 1 ∈ A + B := Set.mem_add.mpr ⟨n + 1, hmem, 0, hB, add_zero _⟩
      rw [cnt_succ A, cnt_succ (A + B), ite_eq_left hmem, ite_eq_left hC, Nat.sub_self,
        cnt_zero B]
      push_cast
      nlinarith
    · refine ⟨a, Nat.le_succ_of_le han, haA, ?_⟩
      have hsub : n + 1 - a = n - a + 1 := by omega
      rw [cnt_succ A, cnt_succ (A + B), ite_eq_right hmem, hsub, cnt_succ B, add_zero]
      by_cases hb : n - a + 1 ∈ B
      · have hC : n + 1 ∈ A + B :=
          Set.mem_add.mpr ⟨a, haA, n - a + 1, hb, by omega⟩
        rw [ite_eq_left hb, ite_eq_left hC]
        linarith
      · rw [ite_eq_right hb]
        by_cases hC : n + 1 ∈ A + B
        · rw [ite_eq_left hC]
          linarith
        · rw [ite_eq_right hC]
          linarith

private theorem schn_ineq_aux {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] (hA : 0 ∈ A) (hB : 0 ∈ B) :
    schnirelmannDensity A + schnirelmannDensity B
        - schnirelmannDensity A * schnirelmannDensity B
      ≤ schnirelmannDensity (A + B) := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn', cnt_eq (A + B) n]
  obtain ⟨a, han, _, hinv⟩ := gap_invariant hA hB n
  have hβ := density_le_cnt B (n - a)
  rw [Nat.cast_sub han] at hβ
  have hα := density_le_cnt A n
  have hβ1 : schnirelmannDensity B ≤ 1 := schnirelmannDensity_le_one
  nlinarith [mul_le_mul_of_nonneg_left hα (sub_nonneg.mpr hβ1)]

theorem schnirelmann_inequality_holds : schnirelmann_inequality := by
  intro A B hA hB
  exact schn_ineq_aux hA hB

/-! ## The basis theorem -/

private theorem fold_zero (A : Set ℕ) : fold_sum A 0 = {0} := rfl

private theorem fold_succ (A : Set ℕ) (h : ℕ) : fold_sum A (h + 1) = fold_sum A h + A := rfl

private theorem zero_mem_fold (A : Set ℕ) (hA : 0 ∈ A) (h : ℕ) : 0 ∈ fold_sum A h := by
  induction h with
  | zero =>
    rw [fold_zero]
    exact Set.mem_singleton 0
  | succ h ih =>
    rw [fold_succ]
    exact Set.mem_add.mpr ⟨0, ih, 0, hA, add_zero 0⟩

private theorem fold_add (A : Set ℕ) (h k : ℕ) :
    ∀ x y : ℕ, x ∈ fold_sum A h → y ∈ fold_sum A k → x + y ∈ fold_sum A (h + k) := by
  induction k with
  | zero =>
    intro x y hx hy
    rw [fold_zero, Set.mem_singleton_iff] at hy
    rw [hy, add_zero, add_zero]
    exact hx
  | succ k ih =>
    intro x y hx hy
    rw [fold_succ] at hy
    obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp hy
    have hxu := ih x u hx hu
    rw [← huv, ← add_assoc h k 1, fold_succ, ← add_assoc x u v]
    exact Set.mem_add.mpr ⟨x + u, hxu, v, hv, rfl⟩

/-- Step: the basis theorem from Schnirelmann's inequality. -/
theorem schnirelmann_basis_step (h5 : schnirelmann_inequality) : schnirelmann_basis := by
  classical
  intro A hA hpos
  have hα1 : schnirelmannDensity A ≤ 1 := schnirelmannDensity_le_one
  have hstep : ∀ h : ℕ,
      1 - schnirelmannDensity (fold_sum A h) ≤ (1 - schnirelmannDensity A) ^ h := by
    intro h
    induction h with
    | zero =>
      have h0 : 0 ≤ schnirelmannDensity (fold_sum A 0) := schnirelmannDensity_nonneg
      rw [pow_zero]
      linarith
    | succ h ih =>
      have key := h5 (fold_sum A h) A (zero_mem_fold A hA h) hA
      rw [← fold_succ] at key
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hα1)]
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith : 1 - schnirelmannDensity A < 1)
  have hhalf := hstep h
  have huniv := add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
    (zero_mem_fold A hA h) (zero_mem_fold A hA h) (by linarith)
  refine ⟨h + h, Set.eq_univ_iff_forall.mpr (fun n => ?_)⟩
  have hn : n ∈ fold_sum A h + fold_sum A h := by
    rw [huniv]
    exact Set.mem_univ n
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_add.mp hn
  rw [← hxy]
  exact fold_add A h h x y hx hy

/-! ## Schnirelmann's theorem -/

/-- A number from 2 on is a sum of 2s, with one 3 when it is odd. -/
private theorem small_primes (j : ℕ) (hj : 2 ≤ j) :
    ∃ l : List ℕ, l.length ≤ j ∧ (∀ p ∈ l, p.Prime) ∧ l.sum = j := by
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨m, hm⟩ := he
    refine ⟨List.replicate m 2, ?_, ?_, ?_⟩
    · rw [List.length_replicate]
      omega
    · intro p hp
      rw [List.eq_of_mem_replicate hp]
      exact Nat.prime_two
    · rw [List.sum_replicate, smul_eq_mul]
      omega
  · obtain ⟨m, hm⟩ := ho
    refine ⟨3 :: List.replicate (m - 1) 2, ?_, ?_, ?_⟩
    · rw [List.length_cons, List.length_replicate]
      omega
    · intro p hp
      rcases List.mem_cons.mp hp with h | h
      · rw [h]
        exact Nat.prime_three
      · rw [List.eq_of_mem_replicate h]
        exact Nat.prime_two
    · rw [List.sum_cons, List.sum_replicate, smul_eq_mul]
      omega

/-- A sum of `h` members of the set is a sum of at most `2 * h` primes plus at
most `h` ones. -/
private theorem fold_primes (h : ℕ) : ∀ m : ℕ, m ∈ fold_sum prime_pair_sums h →
    ∃ l : List ℕ, l.length ≤ 2 * h ∧ (∀ p ∈ l, p.Prime) ∧ ∃ k : ℕ, k ≤ h ∧ l.sum + k = m := by
  induction h with
  | zero =>
    intro m hm
    rw [fold_zero, Set.mem_singleton_iff] at hm
    refine ⟨[], ?_, ?_, 0, le_refl 0, ?_⟩
    · simp
    · intro p hp
      simp at hp
    · simp [hm]
  | succ h ih =>
    intro m hm
    rw [fold_succ] at hm
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_add.mp hm
    obtain ⟨l, hl, hp, k, hk, hsum⟩ := ih x hx
    rcases hy with h0 | h1 | ⟨a, b, ha, hb, hab⟩
    · exact ⟨l, by omega, hp, k, by omega, by omega⟩
    · exact ⟨l, by omega, hp, k + 1, by omega, by omega⟩
    · refine ⟨a :: b :: l, ?_, ?_, k, by omega, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro p hpm
        rcases List.mem_cons.mp hpm with e | e
        · rw [e]
          exact ha
        · rcases List.mem_cons.mp e with e' | e'
          · rw [e']
            exact hb
          · exact hp p e'
      · simp only [List.sum_cons]
        omega

/-- Step: Schnirelmann's theorem from the positive density of the sums of two
primes and the basis theorem. -/
theorem schnirelmann_bounded_sum_step (h4 : prime_pair_sums_density)
    (h6 : schnirelmann_basis) : schnirelmann_bounded_sum := by
  obtain ⟨h, hh⟩ := h6 prime_pair_sums (Or.inl rfl) h4
  refine ⟨2 * h + (h + 2), fun n hn => ?_⟩
  have hmem : n - 2 ∈ fold_sum prime_pair_sums h := by
    rw [hh]
    exact Set.mem_univ _
  obtain ⟨l, hl, hp, k, hk, hsum⟩ := fold_primes h (n - 2) hmem
  obtain ⟨l', hl', hp', hsum'⟩ := small_primes (k + 2) (by omega)
  refine ⟨l ++ l', ?_, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · intro p hpm
    rcases List.mem_append.mp hpm with e | e
    · exact hp p e
    · exact hp' p e
  · rw [List.sum_append]
    omega

#print axioms goldbach_first_moment_holds
#print axioms pair_factor_second_moment_holds
#print axioms goldbach_second_moment_step
#print axioms prime_pair_sums_density_step
#print axioms schnirelmann_inequality_holds
#print axioms schnirelmann_basis_step
#print axioms schnirelmann_bounded_sum_step

end RNS.Schnirelmann
