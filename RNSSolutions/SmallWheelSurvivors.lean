/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunPureSieve.Conclusions
import RNSNetwork.Nodes.MertensThird.Conclusions
import RNSNetwork.Nodes.SmallWheelSurvivors.Conclusions
import Mathlib

/-!
# Proofs for SmallWheelSurvivors

Imports claims only, never other nodes' proofs. Both claims are steps:
`legendre_error` takes `BrunPureSieve.legendre_exact`, and
`small_wheel_survivors` takes `legendre_error` and `MertensThird.mertens_third`,
joined in `RNSSolutions/Assemble.lean`.

Idea. Expand the share as a sum over sets of wheels (`Finset.prod_add`): the
same sum as Legendre's, without rounding down; each rounding loses less than
one, and there are 2 to the number of wheels sets. With the wheels up to
`log x` there are at most `log x + 1` of them, so the error is at most
`2 · x ^ log 2`; times `log log x / x` that tends to 0 (a logarithm is small
next to any positive power). What is left is the share times `log log x`,
which tends to e to minus Euler's constant by Mertens' third theorem at
`log x`.
-/

namespace RNS.SmallWheelSurvivors

open Filter Topology

/-- Rounding `N / d` down loses less than one. -/
private theorem nat_div_err (N d : ℕ) (hd : 0 < d) :
    |((N / d : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have e : (N : ℝ) = d * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N d).symm
  have hr : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N hd
  have h2 : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hdR]
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The share as a signed sum over the sets of wheels. -/
private theorem share_expand (W : Finset ℕ) (N : ℕ) :
    (N : ℝ) * ∏ p ∈ W, (1 - 1 / (p : ℝ)) =
      ∑ D ∈ W.powerset, (-1 : ℝ) ^ D.card * ((N : ℝ) / ((D.prod id : ℕ) : ℝ)) := by
  have hp : ∏ p ∈ W, (1 - 1 / (p : ℝ)) = ∏ p ∈ W, (-(1 / (p : ℝ)) + 1) :=
    Finset.prod_congr rfl (fun p _ => by ring)
  rw [hp, Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun D _ => ?_)
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Nat.cast_prod, Finset.prod_div_distrib,
    Finset.prod_const_one]
  simp only [id]
  ring

theorem legendre_error_step (h : RNS.BrunPureSieve.legendre_exact) : legendre_error := by
  intro W N hW
  have hS := h W N W.card hW le_rfl
  have hfilter : W.powerset.filter (fun D => D.card ≤ W.card) = W.powerset :=
    Finset.filter_true_of_mem (fun D hD => Finset.card_le_card (Finset.mem_powerset.mp hD))
  unfold RNS.BrunPureSieve.truncated_count at hS
  rw [hfilter] at hS
  have hSR : ((survivors_upto W N).card : ℝ) =
      ∑ D ∈ W.powerset, (-1 : ℝ) ^ D.card * ((N / D.prod id : ℕ) : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) hS
    push_cast at this
    exact this
  rw [hSR, share_expand, ← Finset.sum_sub_distrib]
  calc |∑ D ∈ W.powerset, ((-1 : ℝ) ^ D.card * ((N / D.prod id : ℕ) : ℝ) -
          (-1 : ℝ) ^ D.card * ((N : ℝ) / ((D.prod id : ℕ) : ℝ)))|
      ≤ ∑ D ∈ W.powerset, |(-1 : ℝ) ^ D.card * ((N / D.prod id : ℕ) : ℝ) -
          (-1 : ℝ) ^ D.card * ((N : ℝ) / ((D.prod id : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ D ∈ W.powerset, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        have hDW := Finset.mem_powerset.mp hD
        have hd : 0 < D.prod id := Finset.prod_pos (fun p hp => (hW p (hDW hp)).pos)
        rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact nat_div_err N _ hd
    _ = 2 ^ W.card := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]
        norm_num

/-- At most `log x + 1` wheels up to `log x`, so 2 to their number is at most
`2 · x ^ log 2`. -/
private theorem two_pow_card_le {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ (active_primes (⌊Real.log x⌋₊ + 1)).card ≤ 2 * x ^ Real.log 2 := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hcard : (active_primes (⌊Real.log x⌋₊ + 1)).card ≤ ⌊Real.log x⌋₊ + 1 := by
    unfold active_primes
    exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  calc (2 : ℝ) ^ (active_primes (⌊Real.log x⌋₊ + 1)).card ≤ (2 : ℝ) ^ (⌊Real.log x⌋₊ + 1) :=
        pow_le_pow_right₀ (by norm_num) hcard
    _ = 2 * (2 : ℝ) ^ ((⌊Real.log x⌋₊ : ℕ) : ℝ) := by rw [pow_succ, Real.rpow_natCast]; ring
    _ ≤ 2 * (2 : ℝ) ^ Real.log x := by
        have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) (Nat.floor_le hlog)
        linarith
    _ = 2 * x ^ Real.log 2 := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
          Real.rpow_def_of_pos (by linarith : (0 : ℝ) < x), mul_comm (Real.log 2)]

theorem small_wheel_survivors_step (hle : legendre_error) (hm : RNS.MertensThird.mertens_third) :
    small_wheel_survivors := by
  unfold small_wheel_survivors
  unfold RNS.MertensThird.mertens_third at hm
  have hy : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hV := hm.comp hy
  have hδ : 0 < 1 - Real.log 2 := by
    have := Real.log_two_lt_d9
    linarith
  have ha : Tendsto (fun x : ℕ => 2 * (Real.log (x : ℝ) / (x : ℝ) ^ (1 - Real.log 2)))
      atTop (𝓝 0) := by
    have h0 := ((isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
    have := h0.const_mul 2
    rw [mul_zero] at this
    exact this
  have hE : Tendsto (fun x : ℕ =>
      (((survivors_upto (active_primes (⌊Real.log x⌋₊ + 1)) x).card : ℝ) -
        (x : ℝ) * RNS.MertensThird.survivor_share (Real.log x)) * Real.log (Real.log x) / x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [eventually_ge_atTop 3] with x hx
    have hx3 : (3 : ℝ) ≤ x := by exact_mod_cast hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlogx : 1 ≤ Real.log x := by
      have he := Real.exp_one_lt_d9
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) (by linarith)
    have hll0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlogx
    have hll : Real.log (Real.log x) ≤ Real.log x :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have herr := hle (active_primes (⌊Real.log x⌋₊ + 1)) x
      (fun q hq => (Finset.mem_filter.mp hq).2)
    have hpow := two_pow_card_le (x := (x : ℝ)) (by linarith)
    have hxl : 0 < (x : ℝ) ^ Real.log 2 := Real.rpow_pos_of_pos hxpos _
    unfold RNS.MertensThird.survivor_share
    calc ‖(((survivors_upto (active_primes (⌊Real.log x⌋₊ + 1)) x).card : ℝ) -
            (x : ℝ) * ∏ p ∈ active_primes (⌊Real.log x⌋₊ + 1), (1 - 1 / (p : ℝ))) *
            Real.log (Real.log x) / x‖
        = |((survivors_upto (active_primes (⌊Real.log x⌋₊ + 1)) x).card : ℝ) -
            (x : ℝ) * ∏ p ∈ active_primes (⌊Real.log x⌋₊ + 1), (1 - 1 / (p : ℝ))| *
            Real.log (Real.log x) / x := by
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hll0, abs_of_pos hxpos]
      _ ≤ (2 : ℝ) ^ (active_primes (⌊Real.log x⌋₊ + 1)).card * Real.log x / x :=
          div_le_div_of_nonneg_right (mul_le_mul herr hll hll0 (by positivity)) hxpos.le
      _ ≤ 2 * (x : ℝ) ^ Real.log 2 * Real.log x / x :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (by linarith)) hxpos.le
      _ = 2 * (Real.log (x : ℝ) / (x : ℝ) ^ (1 - Real.log 2)) := by
          rw [Real.rpow_sub hxpos, Real.rpow_one]
          first | (field_simp; ring) | field_simp
  have hsum := hE.add hV
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  show (((survivors_upto (active_primes (⌊Real.log x⌋₊ + 1)) x).card : ℝ) -
        (x : ℝ) * RNS.MertensThird.survivor_share (Real.log x)) * Real.log (Real.log x) / x +
      RNS.MertensThird.survivor_share (Real.log x) * Real.log (Real.log x) =
    ((survivors_upto (active_primes (⌊Real.log x⌋₊ + 1)) x).card : ℝ) *
      Real.log (Real.log x) / x
  first | (field_simp; ring) | field_simp

#print axioms RNS.SmallWheelSurvivors.legendre_error_step
#print axioms RNS.SmallWheelSurvivors.small_wheel_survivors_step

end RNS.SmallWheelSurvivors
