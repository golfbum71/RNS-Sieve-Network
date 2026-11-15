/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GapPairs.Conclusions
import RNSNetwork.Nodes.PatternUpperBound.Conclusions   -- `pattern_count_le`, `bad_factor`
import Mathlib.Algebra.BigOperators.Intervals              -- `Finset.prod_Icc_succ_top`
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset   -- `Finset.prod_le_prod_of_subset_of_one_le₀`
import Mathlib.Algebra.BigOperators.Ring.Finset                  -- `Nat.cast_prod`
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proofs for GapPairs

Built clean on GitHub (standard axioms only, 2026-11-14).

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

/-! ## Ford's first-power form (added 2026-11-15)

`gap_pair_bound_ford` is a step from `PatternUpperBound.pattern_count_le` and
`BadWheels.blocked_le_card` / `blocked_eq_card_iff`: the pair at gap `h` is the
pattern of the forms `n` and `n + h`; a wheel above 2 dividing its bad product
blocks fewer than two positions, so it divides `h` (otherwise 0 and the wheel
minus the remainder of `h` are two blocked positions) and blocks exactly one.
Its factor is then (wheel − 1)/(wheel − 2), the gap's own correction.

`correction_le_two_totient_ratio` is proved outright: (p − 1)/(p − 2) is
p/(p − 1) times (p − 1)²/(p(p − 2)), and the product of the last factor over
all numbers from 3 to `M` telescopes to 2(M − 1)/M, below 2.
-/

namespace RNS.GapPairs

open RNS.SelbergTwinRails RNS.GapConstant RNS.BadWheels RNS.PatternUpperBound

/-- The pair at gap `h`: the forms `n` and `n + h`. -/
def gap_forms (h : ℕ) : Finset (ℕ × ℕ) := {(1, 0), (1, h)}

theorem gap_forms_card {h : ℕ} (hh : 0 < h) : (gap_forms h).card = 2 := by
  apply Finset.card_pair
  intro he
  have := congrArg Prod.snd he
  simp at this
  omega

theorem gap_forms_primitive (h : ℕ) : primitive_forms (gap_forms h) := by
  intro ℓ hℓ
  unfold gap_forms at hℓ
  rcases Finset.mem_insert.mp hℓ with rfl | hℓ'
  · exact ⟨le_rfl, Nat.coprime_one_left 0⟩
  · rw [Finset.mem_singleton] at hℓ'
    subst hℓ'
    exact ⟨le_rfl, Nat.coprime_one_left h⟩

theorem gap_mem_blocked {L : Finset (ℕ × ℕ)} {q r : ℕ} :
    r ∈ blocked L q ↔ r < q ∧ ∃ ℓ ∈ L, (ℓ.1 * r + ℓ.2) % q = 0 := by
  unfold blocked
  rw [Finset.mem_filter, Finset.mem_range]

theorem gap_two_le_blocked {L : Finset (ℕ × ℕ)} {q r s : ℕ} (hr : r ∈ blocked L q)
    (hs : s ∈ blocked L q) (hne : r ≠ s) : 2 ≤ (blocked L q).card := by
  have hsub : ({r, s} : Finset ℕ) ⊆ blocked L q := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hr
    · rw [Finset.mem_singleton] at hx'
      rw [hx']
      exact hs
  calc 2 = ({r, s} : Finset ℕ).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem gap_count_eq (h N : ℕ) : gap_pair_count h N = pattern_count (gap_forms h) N := by
  unfold gap_pair_count pattern_count
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro n _
  simp [gap_forms]

/-- A bad wheel of the pair at gap `h` divides `h` and blocks one position. -/
theorem gap_bad_wheel (h_le : blocked_le_card) (h_eq : blocked_eq_card_iff) {h : ℕ}
    (hh : 0 < h) {q : ℕ}
    (hq : q ∈ (bad_product (gap_forms h)).natAbs.primeFactors.filter
      (fun q => (gap_forms h).card < q)) :
    q ∈ h.primeFactors.filter (fun p => p ≠ 2) ∧ blocked_count (gap_forms h) q = 1 := by
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqP, hqd, _⟩ := Nat.mem_primeFactors.mp hq1
  rw [gap_forms_card hh] at hq2
  have hcop : ∀ ℓ ∈ gap_forms h, Nat.Coprime ℓ.1 ℓ.2 :=
    fun ℓ hℓ => (gap_forms_primitive h ℓ hℓ).2
  have hdvd : (q : ℤ) ∣ bad_product (gap_forms h) := Int.natCast_dvd.mpr hqd
  have hne : (blocked (gap_forms h) q).card ≠ (gap_forms h).card :=
    fun e => ((h_eq _ q hqP hcop).mp e) hdvd
  have hle := h_le (gap_forms h) q hqP hcop
  rw [gap_forms_card hh] at hne hle
  have h0 : 0 ∈ blocked (gap_forms h) q :=
    gap_mem_blocked.mpr ⟨hqP.pos, (1, 0), by simp [gap_forms], by simp⟩
  have h1 : 1 ≤ (blocked (gap_forms h) q).card := Finset.card_pos.mpr ⟨0, h0⟩
  have hqh : q ∣ h := by
    by_contra hnd
    have hm0 : h % q ≠ 0 := fun e => hnd (Nat.dvd_of_mod_eq_zero e)
    have hml : h % q < q := Nat.mod_lt h hqP.pos
    have hd := Nat.mod_add_div h q
    obtain ⟨a, ha⟩ : ∃ a, a = h / q := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = h % q := ⟨_, rfl⟩
    rw [← ha, ← hb] at hd
    rw [← hb] at hm0 hml
    have hr : q - b ∈ blocked (gap_forms h) q := by
      refine gap_mem_blocked.mpr ⟨by omega, (1, h), by simp [gap_forms], ?_⟩
      show (1 * (q - b) + h) % q = 0
      have e : 1 * (q - b) + h = q * a + q := by omega
      rw [e, Nat.add_mod_right, Nat.mul_mod_right]
    have h2 := gap_two_le_blocked h0 hr (by omega)
    omega
  refine ⟨Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hqP, hqh, hh.ne'⟩, by omega⟩, ?_⟩
  unfold blocked_count
  omega

theorem gap_bad_factor_le (h_le : blocked_le_card) (h_eq : blocked_eq_card_iff) {h : ℕ}
    (hh : 0 < h) : bad_factor (gap_forms h) ≤ odd_divisor_correction h := by
  unfold bad_factor odd_divisor_correction
  calc ∏ q ∈ (bad_product (gap_forms h)).natAbs.primeFactors.filter
          (fun q => (gap_forms h).card < q),
        ((q : ℝ) - blocked_count (gap_forms h) q) / ((q : ℝ) - (gap_forms h).card)
      = ∏ q ∈ (bad_product (gap_forms h)).natAbs.primeFactors.filter
          (fun q => (gap_forms h).card < q), ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
        refine Finset.prod_congr rfl (fun q hq => ?_)
        rw [(gap_bad_wheel h_le h_eq hh hq).2, gap_forms_card hh]
        first | (push_cast; ring) | push_cast | norm_num
    _ ≤ ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        apply Finset.prod_le_prod_of_subset_of_one_le₀
        · intro q hq
          exact (gap_bad_wheel h_le h_eq hh hq).1
        · intro q hq
          have := one_le_corr (three_le_of_mem (gap_bad_wheel h_le h_eq hh hq).1)
          linarith
        · intro p hp _
          exact one_le_corr (three_le_of_mem hp)

theorem bad_factor_nonneg_gap (h_le : blocked_le_card) {h : ℕ} (hh : 0 < h) :
    0 ≤ bad_factor (gap_forms h) := by
  unfold bad_factor
  refine Finset.prod_nonneg (fun q hq => ?_)
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
  have hqP := Nat.prime_of_mem_primeFactors hq1
  have hle := h_le (gap_forms h) q hqP (fun ℓ hℓ => (gap_forms_primitive h ℓ hℓ).2)
  have h1 : ((gap_forms h).card : ℝ) < q := by exact_mod_cast hq2
  have h2 : (blocked_count (gap_forms h) q : ℝ) ≤ (gap_forms h).card := by
    unfold blocked_count
    exact_mod_cast hle
  exact div_nonneg (by linarith) (by linarith)

theorem gap_pair_bound_ford_step (h_count : pattern_count_le) (h_le : blocked_le_card)
    (h_eq : blocked_eq_card_iff) : gap_pair_bound_ford := by
  obtain ⟨C, N₀, hC⟩ := h_count 2 (by norm_num)
  refine ⟨max C 0, N₀, fun h N hh hN => ?_⟩
  have hb := hC (gap_forms h) (gap_forms_primitive h) (gap_forms_card hh) N hN
  have hbad := gap_bad_factor_le h_le h_eq hh
  have hbad0 := bad_factor_nonneg_gap h_le hh
  have hQ := quotient_nonneg N
  rw [gap_count_eq]
  have e1 : C * bad_factor (gap_forms h) * N / Real.log N ^ 2 =
      C * bad_factor (gap_forms h) * ((N : ℝ) / Real.log N ^ 2) := by ring
  have e2 : max C 0 * odd_divisor_correction h * N / Real.log N ^ 2 =
      max C 0 * odd_divisor_correction h * ((N : ℝ) / Real.log N ^ 2) := by ring
  rw [e1] at hb
  rw [e2]
  have s1 : C * bad_factor (gap_forms h) ≤ max C 0 * bad_factor (gap_forms h) :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) hbad0
  have s2 : max C 0 * bad_factor (gap_forms h) ≤ max C 0 * odd_divisor_correction h :=
    mul_le_mul_of_nonneg_left hbad (le_max_right C 0)
  calc (pattern_count (gap_forms h) N : ℝ)
      ≤ C * bad_factor (gap_forms h) * ((N : ℝ) / Real.log N ^ 2) := hb
    _ ≤ max C 0 * odd_divisor_correction h * ((N : ℝ) / Real.log N ^ 2) :=
        mul_le_mul_of_nonneg_right (s1.trans s2) hQ

/-- The telescoping factor (n − 1)² / (n (n − 2)). -/
noncomputable def tele (n : ℕ) : ℝ := ((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))

theorem tele_prod (M : ℕ) (hM : 2 ≤ M) :
    ∏ n ∈ Finset.Icc 3 M, tele n = 2 * ((M : ℝ) - 1) / M := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty]
    norm_num
  | succ M hM ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    unfold tele
    have h2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    have hM1 : (M : ℝ) - 1 ≠ 0 := by linarith
    have hM2 : (M : ℝ) + 1 ≠ 0 := by linarith
    push_cast
    have hM3 : (M : ℝ) + 1 - 2 ≠ 0 := by linarith
    first | (field_simp; ring) | field_simp

theorem tele_one_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ tele n := by
  unfold tele
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

theorem corr_eq_ratio_mul_tele {p : ℕ} (hp : 3 ≤ p) :
    ((p : ℝ) - 1) / ((p : ℝ) - 2) = (p : ℝ) / ((p : ℝ) - 1) * tele p := by
  unfold tele
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  first | (field_simp; ring) | field_simp

theorem correction_le_two_totient_ratio_holds : correction_le_two_totient_ratio := by
  intro h hh
  unfold odd_divisor_correction
  have hsplit : ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) - 1) / ((p : ℝ) - 2) =
      (∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), (p : ℝ) / ((p : ℝ) - 1)) *
        ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), tele p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun p hp => corr_eq_ratio_mul_tele (three_le_of_mem hp))
  have hA : ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), (p : ℝ) / ((p : ℝ) - 1) ≤
      totient_ratio h := by
    rw [totient_ratio_eq hh]
    apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
    · intro p hp
      have := one_le_ratio (by have := three_le_of_mem hp; omega : 2 ≤ p)
      linarith
    · intro p hp _
      exact one_le_ratio (Nat.prime_of_mem_primeFactors hp).two_le
  have hA0 : 0 ≤ ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_nonneg (fun p hp => by
      have := one_le_ratio (by have := three_le_of_mem hp; omega : 2 ≤ p)
      linarith)
  have hB : ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), tele p ≤ 2 := by
    rcases Nat.lt_or_ge h 2 with h2 | h2
    · have : h.primeFactors.filter (fun p => p ≠ 2) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have h3 := three_le_of_mem hp
        have hle := Nat.le_of_mem_primeFactors (Finset.mem_filter.mp hp).1
        omega
      rw [this, Finset.prod_empty]
      norm_num
    · have hsub : h.primeFactors.filter (fun p => p ≠ 2) ⊆ Finset.Icc 3 h := by
        intro p hp
        exact Finset.mem_Icc.mpr ⟨three_le_of_mem hp,
          Nat.le_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩
      have h1 : ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), tele p ≤
          ∏ n ∈ Finset.Icc 3 h, tele n := by
        apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
        · intro p hp
          have := tele_one_le (three_le_of_mem hp)
          linarith
        · intro n hn _
          exact tele_one_le (Finset.mem_Icc.mp hn).1
      rw [tele_prod h h2] at h1
      have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
      have : 2 * ((h : ℝ) - 1) / h ≤ 2 := by
        rw [div_le_iff₀ hh0]
        linarith
      linarith
  have hB0 : 0 ≤ ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), tele p :=
    Finset.prod_nonneg (fun p hp => by
      have := tele_one_le (three_le_of_mem hp)
      linarith)
  rw [hsplit]
  calc (∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), (p : ℝ) / ((p : ℝ) - 1)) *
        ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), tele p
      ≤ totient_ratio h * 2 := mul_le_mul hA hB hB0 (totient_ratio_nonneg h)
    _ = 2 * totient_ratio h := by ring

theorem gap_pair_bound_ford_totient_step (h_ford : gap_pair_bound_ford)
    (h_c : correction_le_two_totient_ratio) : gap_pair_bound_ford_totient := by
  obtain ⟨C, N₀, hC⟩ := h_ford
  refine ⟨2 * max C 0, N₀, fun h N hh hN => ?_⟩
  have hb := hC h N hh hN
  have hQ := quotient_nonneg N
  have hcorr := h_c h hh
  have hcorr0 : 0 ≤ odd_divisor_correction h := by
    unfold odd_divisor_correction
    exact Finset.prod_nonneg (fun p hp => by
      have := one_le_corr (three_le_of_mem hp)
      linarith)
  have e1 : C * odd_divisor_correction h * N / Real.log N ^ 2 =
      C * odd_divisor_correction h * ((N : ℝ) / Real.log N ^ 2) := by ring
  have e2 : 2 * max C 0 * totient_ratio h * N / Real.log N ^ 2 =
      2 * max C 0 * totient_ratio h * ((N : ℝ) / Real.log N ^ 2) := by ring
  rw [e1] at hb
  rw [e2]
  have s1 : C * odd_divisor_correction h ≤ max C 0 * odd_divisor_correction h :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) hcorr0
  have s2 : max C 0 * odd_divisor_correction h ≤ max C 0 * (2 * totient_ratio h) :=
    mul_le_mul_of_nonneg_left hcorr (le_max_right C 0)
  have s3 : max C 0 * (2 * totient_ratio h) = 2 * max C 0 * totient_ratio h := by ring
  calc (gap_pair_count h N : ℝ)
      ≤ C * odd_divisor_correction h * ((N : ℝ) / Real.log N ^ 2) := hb
    _ ≤ 2 * max C 0 * totient_ratio h * ((N : ℝ) / Real.log N ^ 2) := by
        rw [← s3]
        exact mul_le_mul_of_nonneg_right (s1.trans s2) hQ

end RNS.GapPairs

#print axioms RNS.GapPairs.gap_pair_bound_ford_step
#print axioms RNS.GapPairs.correction_le_two_totient_ratio_holds
#print axioms RNS.GapPairs.gap_pair_bound_ford_totient_step
