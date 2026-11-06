/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.HurwitzZetaZero.Conclusions
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.Complex.AbelLimit                     -- Abel's limit theorem
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds    -- `hasSum_taylorSeries_neg_log`
import Mathlib.Analysis.SpecificLimits.Normed                 -- Dirichlet's test
import Mathlib.NumberTheory.LSeries.SumCoeff                  -- Abel summation for L-series
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd            -- `LSeriesHasSum_sin`

/-!
# Proofs for HurwitzZetaZero

Imports claims only, never other nodes' proofs. The value of the Hurwitz zeta
function at 0 rests on `sin_zeta_at_one`, which rests on `sawtooth_partial_sums`
and `sin_zeta_at_one_eq_series`; all are proved here, from Mathlib alone, and
chained at the end (`hurwitz_zeta_at_zero_holds`).

Idea. Mathlib's Hurwitz zeta function is its even part plus its odd part. At 0
the even part is `-1/2` at the point 0 of the circle and 0 elsewhere
(`hurwitzZetaEven_apply_zero`). The functional equation
(`hurwitzZetaOdd_one_sub` at `s = 1`) makes the odd part at 0 equal to
`sinZeta` at 1 divided by π. At `x = 1`, the point 0 of the circle, `sinZeta`
vanishes, being odd; for `0 < x < 1`, `sin_zeta_at_one` gives `π (1/2 - x)`.

The sawtooth series. Put `w = e^(2πix)`. The partial sums of `∑ wⁿ` are
bounded, so `∑ wⁿ/n` converges (Dirichlet's test). Inside the disc,
`∑ (rw)ⁿ/n = -log(1 - rw)`; letting `r` rise to 1, Abel's limit theorem makes
the sum `-log(1 - w)`. Writing `1 - w = 2 sin(πx) e^(i(πx - π/2))` gives its
argument `πx - π/2`, so the imaginary part of the sum is `π/2 - πx`.

Built clean by `lake build RNSSolutions` on 2026-11-05; `#print axioms` shows only
the standard three.
-/

namespace RNS.HurwitzZetaZero

open HurwitzZeta

/-- At 0, the odd part of the Hurwitz zeta function is `sinZeta` at 1 divided
by π. -/
private theorem odd_at_zero (a : UnitAddCircle) :
    hurwitzZetaOdd a 0 = sinZeta a 1 / (Real.pi : ℂ) := by
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have h2 : (1 : ℝ) = -(n : ℝ) := by simpa using congrArg Complex.re h
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := hurwitzZetaOdd_one_sub a hs
  rw [sub_self, Complex.cpow_neg_one, Complex.Gamma_one, mul_one, mul_one,
    Complex.sin_pi_div_two] at h
  rw [h, mul_inv, div_eq_mul_inv]
  ring

theorem hurwitz_zeta_at_zero_step (h_sin : sin_zeta_at_one) : hurwitz_zeta_at_zero := by
  intro x hx0 hx1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold HurwitzZeta.hurwitzZeta
  rw [hurwitzZetaEven_apply_zero, odd_at_zero]
  rcases hx1.lt_or_eq with hlt | rfl
  · -- `0 < x < 1`: not the point 0 of the circle
    have hne : (x : UnitAddCircle) ≠ 0 := by
      intro h0
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_of_pos_iff (1 : ℝ) one_pos hx0).mp h0
      have hn' : (n : ℝ) = x := by simpa using hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp at hn'
        linarith
      · have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hpos
        linarith
    simp only [hne, ↓reduceIte]
    rw [h_sin x hx0 hlt, zero_add]
    exact mul_div_cancel_left₀ _ hπ
  · -- `x = 1`: the point 0 of the circle, where `sinZeta` vanishes
    have h0 : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period (1 : ℝ)
    have hs0 : sinZeta (0 : UnitAddCircle) 1 = 0 := by
      have h := sinZeta_neg (0 : UnitAddCircle) 1
      rw [neg_zero] at h
      linear_combination h / 2
    simp only [h0, ↓reduceIte]
    rw [hs0, zero_div]
    norm_num

/-! ## The sawtooth series -/

/-- The `n`-th term of the series `∑ wⁿ / n` for `-log (1 - w)`. -/
private noncomputable def logTerm (w : ℂ) (n : ℕ) : ℂ := w ^ n / n

/-- `1 - e^(2it) = 2 sin t · e^(i(t - π/2))`. -/
private theorem one_sub_exp (t : ℝ) :
    (1 : ℂ) - Complex.exp (↑(2 * t) * Complex.I) =
      ↑(2 * Real.sin t) * (Complex.cos ↑(t - Real.pi / 2) +
        Complex.sin ↑(t - Real.pi / 2) * Complex.I) := by
  have h1 := Real.sin_sq_add_cos_sq t
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
      Complex.I_im]
    rw [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.cos_two_mul]
    linear_combination (-2) * h1
  · simp only [Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
      Complex.I_im]
    rw [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.sin_two_mul]
    ring

theorem sawtooth_partial_sums_holds : sawtooth_partial_sums := by
  intro x hx0 hx1
  have hπx0 : 0 < Real.pi * x := mul_pos Real.pi_pos hx0
  have hπx1 : Real.pi * x < Real.pi := mul_lt_of_lt_one_right Real.pi_pos hx1
  have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_pos_of_lt_pi hπx0 hπx1
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = Complex.exp (↑(2 * (Real.pi * x)) * Complex.I) := ⟨_, rfl⟩
  have hwn1 : ‖w‖ = 1 := by
    rw [hw]
    exact Complex.norm_exp_ofReal_mul_I _
  -- `1 - w` lies in the right half plane
  have hre : 0 < (1 - w).re := by
    rw [hw]
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x), pow_pos hsin 2]
  have hslit : 1 - w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, sub_self] at hre
    simp at hre
  -- Dirichlet's test: the partial sums of `wⁱ⁺¹` are bounded
  have hb : ∀ n, ‖∑ i ∈ Finset.range n, w ^ (i + 1)‖ ≤ 2 / ‖w - 1‖ := by
    intro n
    have he : ∑ i ∈ Finset.range n, w ^ (i + 1) = w * ((w ^ n - 1) / (w - 1)) := by
      rw [← geom_sum_eq hw1 n, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => pow_succ' w i)
    rw [he, norm_mul, norm_div, hwn1, one_mul]
    gcongr
    calc ‖w ^ n - 1‖ ≤ ‖w ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hwn1, one_pow, norm_one]; norm_num
  have hfa : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := by
    intro a b hab
    have : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
    dsimp only
    gcongr
  have hcs := Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) (z := fun i : ℕ => w ^ (i + 1)) hfa
    tendsto_one_div_add_atTop_nhds_zero_nat hb
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
  -- the same partial sums, as those of `∑ wⁿ / n`
  have hsum : ∀ n, ∑ i ∈ Finset.range (n + 1), logTerm w i
      = ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) • w ^ (i + 1) := by
    intro n
    rw [Finset.sum_range_succ']
    simp only [logTerm, Nat.cast_zero, div_zero, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.real_smul]
    push_cast
    ring
  have hg : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, logTerm w i) Filter.atTop (nhds l) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simp only [hsum]
    exact hl
  -- Abel's limit theorem, and `∑ (rw)ⁿ/n = -log(1 - rw)` inside the disc
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hg
  rw [Filter.tendsto_map'_iff] at habel
  have heq : ((fun z : ℂ => ∑' n, logTerm w n * z ^ n) ∘ Complex.ofReal)
      =ᶠ[nhdsWithin 1 (Set.Iio 1)] fun r : ℝ => -Complex.log (1 - (r : ℂ) * w) := by
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with r hr
    have hn : ‖(r : ℂ) * w‖ < 1 := by
      rw [norm_mul, hwn1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      exact ⟨hr.1, hr.2⟩
    rw [Function.comp_apply, ← (Complex.hasSum_taylorSeries_neg_log hn).tsum_eq]
    congr 1
    ext n
    unfold logTerm
    ring
  have hcont : Filter.Tendsto (fun r : ℝ => -Complex.log (1 - (r : ℂ) * w))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (-Complex.log (1 - w))) := by
    have h1 : ContinuousAt (fun r : ℝ => 1 - (r : ℂ) * w) 1 :=
      (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    have hc : ContinuousAt (fun r : ℝ => -Complex.log (1 - (r : ℂ) * w)) 1 :=
      ((continuousAt_clog hslit).comp_of_eq h1 (by simp)).neg
    have h2 := hc.tendsto
    simp only [Complex.ofReal_one, one_mul] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hl_eq : l = -Complex.log (1 - w) := tendsto_nhds_unique (habel.congr' heq) hcont
  -- the imaginary part
  have harg : Complex.arg (1 - w) = Real.pi * x - Real.pi / 2 := by
    rw [hw, one_sub_exp (Real.pi * x)]
    have hr2 : 0 < 2 * Real.sin (Real.pi * x) := by linarith
    exact Complex.arg_mul_cos_add_sin_mul_I hr2 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hval : l.im = Real.pi * (1 / 2 - x) := by
    rw [hl_eq, Complex.neg_im, Complex.log_im, harg]
    ring
  have hgi : ∀ i : ℕ, (logTerm w i).im = Real.sin (2 * Real.pi * x * i) / i := by
    intro i
    have e : w ^ i = Complex.exp (↑(2 * Real.pi * x * i) * Complex.I) := by
      rw [hw, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    unfold logTerm
    rw [e, ← Complex.ofReal_natCast, Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im]
  have him := (Complex.continuous_im.tendsto l).comp hg
  rw [hval] at him
  refine him.congr (fun N => ?_)
  rw [Function.comp_apply, Complex.im_sum]
  exact Finset.sum_congr rfl (fun i _ => hgi i)

theorem sin_zeta_at_one_step (h_series : sin_zeta_at_one_eq_series) : sin_zeta_at_one := by
  intro x hx0 hx1
  have hr := sawtooth_partial_sums_holds x hx0 hx1
  have hc : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (Real.sin (2 * Real.pi * x * n) : ℂ) / (n : ℂ))
      Filter.atTop (nhds ((Real.pi * (1 / 2 - x) : ℝ) : ℂ)) := by
    refine ((Complex.continuous_ofReal.tendsto _).comp hr).congr (fun N => ?_)
    simp only [Function.comp_apply, Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [tendsto_nhds_unique (h_series x hx0 hx1) hc]
  push_cast
  ring

/-! ## `sinZeta` at 1 is the sum of its series

Write `A(t)` for the partial sum of `sin(2π k x)` over `1 ≤ k ≤ t`; it is
bounded. Abel summation (the argument of Mathlib's `LSeries_eq_mul_integral`,
which needs no absolute convergence) makes the partial sums of the series at 1
tend to `G(1)`, where `G(s) = ∫₁^∞ A(t) t^(-s-1) dt`. For real `s > 1` Mathlib
gives `sinZeta x s = s G(s)`. As `s` falls to 1, `sinZeta` is continuous (it is
entire) and so is `s G(s)` (dominated convergence, with bound `B t⁻²`), so
`sinZeta x 1 = G(1)`. -/

section edge

open Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology

/-- Abel summation for an L-series whose coefficient sums are `O(nʳ)`, at any
`s` with `r < re s`, without absolute convergence: the partial sums tend to
`s ∫₁^∞ A(t) t^(-s-1) dt`. The argument is that of Mathlib's
`LSeries_eq_mul_integral`, with the summability step left out. -/
private theorem partial_sums_tendsto_integral {f : ℕ → ℂ} (hf : f 0 = 0) {r : ℝ} (hr : 0 ≤ r)
    {s : ℂ} (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k * (k : ℂ) ^ (-s)) atTop
      (𝓝 (s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1)))) := by
  have h₁ : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  have h₂ : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have h₃ (t : ℝ) (ht : t ∈ Set.Ici 1) : DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr h₂)
  have h₄ : ∀ n, ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := fun n ↦ by
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by aesop), hf, zero_add, zero_add]
  simp_rw [← h₄] at hO
  rw [← integral_const_mul]
  simp_rw [mul_comm (f _)]
  convert
    tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun x ↦ (x : ℂ) ^ (-s)) (l := 0) ?_ hf h₃ ?_
      ?_ ?_ (integrableAtFilter_rpow_atTop_iff.mpr h₁)
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne', h₄]
    · ring_nf
    · exact neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  · refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi <|
      integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by simpa using! hr.trans_lt hs)).locallyIntegrableOn
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _ ?_ hO ?_).trans_tendsto hlim
    · exact isBigO_norm_left.mp (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · linarith
  · refine .mul_atTop_rpow_of_isBigO_rpow (-(s + 1).re) r _ ?_ ?_ (by rw [← neg_re, neg_add'])
    · simpa [-neg_add_rev, neg_add'] using! isBigO_deriv_ofReal_cpow_const_atTop _
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
        isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)

/-- The imaginary part of `e^(2πix)` to the `m` is `sin(2π x m)`. -/
private theorem pow_exp_im (x : ℝ) (m : ℕ) :
    ((Complex.exp (↑(2 * (Real.pi * x)) * Complex.I)) ^ m).im = Real.sin (2 * Real.pi * x * m) := by
  rw [← Complex.exp_nat_mul]
  have e : (m : ℂ) * (↑(2 * (Real.pi * x)) * Complex.I) = ↑(2 * Real.pi * x * m) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.exp_ofReal_mul_I_im]

/-- For `0 < x < 1` the partial sums of `sin(2π k x)` are bounded. -/
private theorem sin_partial_bound (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ B : ℝ, ∀ n : ℕ, ‖∑ k ∈ Icc 1 n, ((Real.sin (2 * Real.pi * x * k) : ℝ) : ℂ)‖ ≤ B := by
  have hπx0 : 0 < Real.pi * x := mul_pos Real.pi_pos hx0
  have hπx1 : Real.pi * x < Real.pi := mul_lt_of_lt_one_right Real.pi_pos hx1
  have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_pos_of_lt_pi hπx0 hπx1
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = Complex.exp (↑(2 * (Real.pi * x)) * Complex.I) := ⟨_, rfl⟩
  have hwn1 : ‖w‖ = 1 := by
    rw [hw]
    exact Complex.norm_exp_ofReal_mul_I _
  have hre : 0 < (1 - w).re := by
    rw [hw]
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x), pow_pos hsin 2]
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, sub_self] at hre
    simp at hre
  have hb : ∀ n, ‖∑ i ∈ range n, w ^ (i + 1)‖ ≤ 2 / ‖w - 1‖ := by
    intro n
    have he : ∑ i ∈ range n, w ^ (i + 1) = w * ((w ^ n - 1) / (w - 1)) := by
      rw [← geom_sum_eq hw1 n, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => pow_succ' w i)
    rw [he, norm_mul, norm_div, hwn1, one_mul]
    gcongr
    calc ‖w ^ n - 1‖ ≤ ‖w ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hwn1, one_pow, norm_one]; norm_num
  have key : ∀ n : ℕ, ∑ k ∈ Icc 1 n, ((Real.sin (2 * Real.pi * x * k) : ℝ) : ℂ)
      = (((∑ i ∈ range n, w ^ (i + 1)).im : ℝ) : ℂ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ,
        Complex.add_im, Complex.ofReal_add, hw, pow_exp_im]
  refine ⟨2 / ‖w - 1‖, fun n => ?_⟩
  rw [key, Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans (hb n)

theorem sin_zeta_at_one_eq_series_holds : sin_zeta_at_one_eq_series := by
  intro x hx0 hx1
  -- the coefficients and their partial-sum function
  set a : ℕ → ℂ := fun n => ((Real.sin (2 * Real.pi * x * n) : ℝ) : ℂ) with ha_def
  have ha0 : a 0 = 0 := by simp [ha_def]
  obtain ⟨B, hB⟩ := sin_partial_bound x hx0 hx1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hO : (fun n ↦ ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
    refine IsBigO.of_bound B (Eventually.of_forall fun n => ?_)
    rw [Real.rpow_zero, norm_one, mul_one]
    exact hB n
  -- Abel summation at 1
  have hA := partial_sums_tendsto_integral (f := a) ha0 le_rfl (s := 1) (by simp) hO
  simp only [Complex.cpow_neg_one] at hA
  -- `G(s) = ∫₁^∞ A(t) t^(-s-1) dt`, continuous as `s` falls to 1
  set A : ℝ → ℂ := fun t => ∑ k ∈ Icc 1 ⌊t⌋₊, a k with hA_def
  have hAmeas : Measurable A := by
    rw [hA_def]
    exact (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, a k)).comp Nat.measurable_floor
  have hAbound : ∀ t : ℝ, ‖A t‖ ≤ B := fun t => hB _
  have hGcont : ContinuousWithinAt
      (fun σ : ℝ => ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-((σ : ℂ) + 1))) (Set.Ici 1) 1 := by
    refine continuousWithinAt_of_dominated (bound := fun t : ℝ => B * t ^ (-2 : ℝ)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun σ => hAmeas.aestronglyMeasurable.mul ?_
      refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      exact ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 ht0)).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have hσ1 : (1 : ℝ) ≤ σ := hσ
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-((σ : ℂ) + 1)).re = -(σ + 1) := by simp
      rw [hre]
      have hpow : t ^ (-(σ + 1)) ≤ t ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      exact mul_le_mul (hAbound t) hpow (Real.rpow_nonneg ht0.le _) hB0
    · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul B
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one ht).ne'
      have hlin : ContinuousAt (fun σ : ℝ => -((σ : ℂ) + 1)) 1 :=
        (Complex.continuous_ofReal.add continuous_const).neg.continuousAt
      exact (continuousAt_const.mul ((continuousAt_const_cpow ht0).comp hlin)).continuousWithinAt
  -- for real `s > 1`, `sinZeta x s = s G(s)`
  have hEq : ∀ σ : ℝ, 1 < σ → HurwitzZeta.sinZeta (x : UnitAddCircle) σ
      = (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-((σ : ℂ) + 1)) := by
    intro σ hσ
    have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
    have hsum := HurwitzZeta.LSeriesHasSum_sin x hσ'
    rw [← hsum.LSeries_eq]
    exact LSeries_eq_mul_integral a le_rfl (by simp; linarith) hsum.LSeriesSummable hO
  -- let `s` fall to 1
  have hlim1 : Tendsto (fun σ : ℝ => HurwitzZeta.sinZeta (x : UnitAddCircle) σ) (𝓝[>] 1)
      (𝓝 (HurwitzZeta.sinZeta (x : UnitAddCircle) 1)) := by
    have h := ((HurwitzZeta.differentiableAt_sinZeta (x : UnitAddCircle)).continuous.tendsto
      ((1 : ℝ) : ℂ)).comp (Complex.continuous_ofReal.tendsto (1 : ℝ))
    simp only [Complex.ofReal_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] 1) (𝓝 ((1 : ℂ) * ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-((1 : ℂ) + 1)))) := by
    have h1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    have h2 := (hGcont.tendsto).mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    have h3 := h1.mul h2
    simp only [Complex.ofReal_one] at h3
    exact h3
  have hval : HurwitzZeta.sinZeta (x : UnitAddCircle) 1
      = (1 : ℂ) * ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-((1 : ℂ) + 1)) := by
    refine tendsto_nhds_unique hlim1 (hlim2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hEq σ hσ).symm
  -- the partial sums of the claim
  rw [hval, ← Filter.tendsto_add_atTop_iff_nat 1]
  refine hA.congr (fun N => ?_)
  rw [Nat.range_succ_eq_Icc_zero]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ha_def, div_eq_mul_inv]

end edge

theorem sin_zeta_at_one_holds : sin_zeta_at_one :=
  sin_zeta_at_one_step sin_zeta_at_one_eq_series_holds

theorem hurwitz_zeta_at_zero_holds : hurwitz_zeta_at_zero :=
  hurwitz_zeta_at_zero_step sin_zeta_at_one_holds

end RNS.HurwitzZetaZero

#print axioms RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_step
#print axioms RNS.HurwitzZetaZero.sawtooth_partial_sums_holds
#print axioms RNS.HurwitzZetaZero.sin_zeta_at_one_step
#print axioms RNS.HurwitzZetaZero.sin_zeta_at_one_eq_series_holds
#print axioms RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds
