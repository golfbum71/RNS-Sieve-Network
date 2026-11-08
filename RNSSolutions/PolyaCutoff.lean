/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.ShareAsymptotics.Conclusions
import RNSNetwork.Nodes.PolyaCutoff.Conclusions
import Mathlib

/-!
# Proofs for PolyaCutoff

Imports claims only, never other nodes' proofs. The claim is a step taking
`ShareAsymptotics.pattern_share_asymptotic` as a named hypothesis, joined in
`RNSSolutions/Assemble.lean`.

Idea. Write `c` for e to minus Euler's constant and `N` for the integer part
of `x ^ c`. Then `N` tends to infinity, so the share times `log N` to the `k`
tends to the constant times `c ^ k`. Also `log N / log x` tends to `c`: it is
at most `c` (as `N ≤ x ^ c`) and at least `c − log 2 / log x` (as
`N ≥ x ^ c / 2` once `x ^ c ≥ 2`). Multiply by `(log x / log N) ^ k`, which
tends to `c` to the minus `k`.
-/

namespace RNS.PolyaCutoff

open Filter Topology

theorem polya_cutoff_share_step (h : RNS.ShareAsymptotics.pattern_share_asymptotic) :
    polya_cutoff_share := by
  intro T hT hk
  have hlim := h T hT hk
  have hc : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  generalize Real.exp (-Real.eulerMascheroniConstant) = c at hlim hc ⊢
  have hpow : Tendsto (fun x : ℕ => (x : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hN : Tendsto (fun x : ℕ => ⌊(x : ℝ) ^ c⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hpow
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `log N / log x → c`
  have hratio : Tendsto (fun x : ℕ => Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ) / Real.log x) atTop (𝓝 c) := by
    have h0 : Tendsto (fun x : ℕ => Real.log 2 / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have hg1 : Tendsto (fun x : ℕ => c - Real.log 2 / Real.log x) atTop (𝓝 c) := by
      have := (tendsto_const_nhds (x := c)).sub h0
      rwa [sub_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg1 tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 2, hpow.eventually_ge_atTop 2] with x hx hx2
      have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx
      have hx2' : (2 : ℝ) ≤ (x : ℝ) ^ c := hx2
      have hlx : 0 < Real.log x := Real.log_pos (by linarith)
      have hNlow : (x : ℝ) ^ c / 2 ≤ ((⌊(x : ℝ) ^ c⌋₊ : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one ((x : ℝ) ^ c)
        linarith
      have key : c * Real.log x - Real.log 2 ≤ Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ) := by
        calc c * Real.log x - Real.log 2 = Real.log ((x : ℝ) ^ c / 2) := by
              rw [Real.log_div (show (x : ℝ) ^ c ≠ 0 by positivity) (show (2 : ℝ) ≠ 0 by norm_num),
                Real.log_rpow (show (0 : ℝ) < x by linarith)]
          _ ≤ Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ) := Real.log_le_log (by positivity) hNlow
      calc c - Real.log 2 / Real.log x = (c * Real.log x - Real.log 2) / Real.log x := by
            field_simp
        _ ≤ Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ) / Real.log x := div_le_div_of_nonneg_right key hlx.le
    · filter_upwards [eventually_ge_atTop 2] with x hx
      have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx
      have hlx : 0 < Real.log x := Real.log_pos (by linarith)
      rw [div_le_iff₀ hlx]
      rcases Nat.eq_zero_or_pos ⌊(x : ℝ) ^ c⌋₊ with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        positivity
      · calc Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ) ≤ Real.log ((x : ℝ) ^ c) :=
              Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le (by positivity))
          _ = c * Real.log x := Real.log_rpow (by linarith) c
  -- `log x / log N → 1 / c`
  have hinv : Tendsto (fun x : ℕ => Real.log x / Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ)) atTop (𝓝 c⁻¹) := by
    refine (hratio.inv₀ hc.ne').congr (fun x => ?_)
    exact inv_div _ _
  have hcomp := (hlim.comp hN).mul (hinv.pow T.card)
  have hval : hardy_littlewood_constant T * c ^ T.card * (c⁻¹) ^ T.card =
      hardy_littlewood_constant T := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, mul_one]
  rw [hval] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [hN.eventually_ge_atTop 2] with x hx
  have hx' : (2 : ℝ) ≤ ((⌊(x : ℝ) ^ c⌋₊ : ℕ) : ℝ) := by exact_mod_cast hx
  have hlN : Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have e : Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ) ^ T.card *
      (Real.log x / Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ)) ^ T.card = Real.log x ^ T.card := by
    rw [← mul_pow]
    congr 1
    field_simp
  show ((wheel_survivors_gen T (⌊(x : ℝ) ^ c⌋₊ + 1)).card : ℝ)
        / (primorial_modulus (⌊(x : ℝ) ^ c⌋₊ + 1) : ℝ) * Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ) ^ T.card
        * (Real.log x / Real.log (⌊(x : ℝ) ^ c⌋₊ : ℕ)) ^ T.card
      = ((wheel_survivors_gen T (⌊(x : ℝ) ^ c⌋₊ + 1)).card : ℝ)
        / (primorial_modulus (⌊(x : ℝ) ^ c⌋₊ + 1) : ℝ) * Real.log x ^ T.card
  rw [mul_assoc, e]

#print axioms RNS.PolyaCutoff.polya_cutoff_share_step

end RNS.PolyaCutoff
