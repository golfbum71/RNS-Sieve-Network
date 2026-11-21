/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.OrbitalTrace.Conclusions
import Mathlib.Analysis.Fourier.PoissonSummation          -- `SchwartzMap.tsum_eq_tsum_fourier`
import Mathlib.Analysis.Fourier.AddCircle                 -- `fourier_coe_apply`
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace      -- `Measure.integral_comp_mul_left`
import Mathlib.Topology.Algebra.Module.FiniteDimension    -- `LinearEquiv.toContinuousLinearEquiv`
import Mathlib.Analysis.SpecialFunctions.Pow.Real         -- `Real.rpow_def_of_pos`, `Real.rpow_intCast`

/-!
# Proofs for OrbitalTrace

Imports claims only, never other nodes' proofs.

Idea. Mathlib's Poisson summation is for the loop of length 1: the sum of a
Schwartz function at the whole numbers equals the sum of its Fourier
transform at the whole numbers. The loop here has length `log γ`, so apply
Mathlib's formula to the stretched function `u ↦ ψ(log γ · u)`, again a
Schwartz function. Substituting in the Fourier integral, its Fourier
transform at a whole number `m` is the Fourier transform of `ψ` at
`m / log γ`, divided by `log γ` (`fourier_scale`). That gives
`poisson_scaled`, and `ψ(log γ · k) = φ(γ^k)` gives `orbital_trace_poisson_holds`.

The vanishing: every whole power of `γ` is at most 1 (power zero or below) or
at least `γ` (power one or above), so `φ` is zero at all of them
(`orbital_trace_vanishes_step`).

Built clean by `lake build RNSSolutions` on 2026-11-21; `#print axioms` shows only
the standard three.
-/

open scoped FourierTransform SchwartzMap

namespace RNS.OrbitalTrace

/-- Stretching by `L > 0` divides the Fourier transform by `L` and shrinks its
variable by `L`. -/
private theorem fourier_scale (ψ : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L) (g : ℝ → ℂ)
    (hg : ∀ x, g x = ψ (L * x)) (w : ℝ) :
    𝓕 g w = ((L⁻¹ : ℝ) : ℂ) * 𝓕 (ψ : ℝ → ℂ) (w / L) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have h : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • g v) =
      fun v : ℝ => (fun y : ℝ =>
        Complex.exp (↑(-2 * Real.pi * y * (w / L)) * Complex.I) • ψ y) (L * v) := by
    funext v
    have hv : -2 * Real.pi * (L * v) * (w / L) = -2 * Real.pi * v * w := by
      calc -2 * Real.pi * (L * v) * (w / L) = -2 * Real.pi * v * (L * (w / L)) := by ring
        _ = -2 * Real.pi * v * w := by rw [mul_div_cancel₀ w hL.ne']
    simp only [hg, hv]
  rw [h, MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * (w / L)) * Complex.I) • ψ y) L]
  simp only [abs_of_pos (inv_pos.mpr hL), Complex.real_smul]

/-- Poisson summation on the loop of length `L`. -/
private theorem poisson_scaled (ψ : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L) :
    ∑' m : ℤ, 𝓕 (ψ : ℝ → ℂ) ((m : ℝ) / L) = (L : ℂ) * ∑' k : ℤ, ψ (L * k) := by
  let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ L hL.ne').toContinuousLinearEquiv
  let g : 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e ψ
  have hg : ∀ x, g x = ψ (L * x) := fun x => by
    first
    | rfl
    | simp [g, e, smul_eq_mul]
  have hP := SchwartzMap.tsum_eq_tsum_fourier g 0
  have h1 : ∀ n : ℤ, 𝓕 g (n : ℝ) * fourier n ((0 : ℝ) : UnitAddCircle) =
      ((L⁻¹ : ℝ) : ℂ) * 𝓕 (ψ : ℝ → ℂ) ((n : ℝ) / L) := by
    intro n
    have h0 : fourier n ((0 : ℝ) : UnitAddCircle) = 1 := by
      rw [fourier_coe_apply]
      simp
    rw [h0, mul_one, SchwartzMap.fourier_coe, fourier_scale ψ hL (g : ℝ → ℂ) hg]
  simp only [zero_add] at hP
  simp_rw [h1, hg] at hP
  rw [tsum_mul_left] at hP
  rw [hP, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne'), one_mul]

theorem orbital_trace_poisson_holds : orbital_trace_poisson := by
  intro γ hγ φ ψ hψ
  have hL : 0 < Real.log γ := Real.log_pos hγ
  have hk : ∀ k : ℤ, ψ (Real.log γ * k) = φ (γ ^ k) := by
    intro k
    rw [hψ, ← Real.rpow_def_of_pos (by linarith) (k : ℝ), Real.rpow_intCast]
  rw [poisson_scaled ψ hL]
  congr 1
  exact tsum_congr hk

theorem orbital_trace_vanishes_step (h : orbital_trace_poisson) : orbital_trace_vanishes := by
  intro γ hγ φ ψ hψ hsupp
  rw [h γ hγ φ ψ hψ]
  have hzero : ∀ k : ℤ, φ (γ ^ k) = 0 := by
    intro k
    apply hsupp
    rintro ⟨h1, h2⟩
    rcases le_or_gt k 0 with hk | hk
    · have hle := zpow_le_zpow_right₀ hγ.le hk
      rw [zpow_zero] at hle
      linarith
    · have hle := zpow_le_zpow_right₀ hγ.le (show (1 : ℤ) ≤ k by omega)
      rw [zpow_one] at hle
      linarith
  simp [hzero]

theorem orbital_trace_vanishes_holds : orbital_trace_vanishes :=
  orbital_trace_vanishes_step orbital_trace_poisson_holds

end RNS.OrbitalTrace

#print axioms RNS.OrbitalTrace.orbital_trace_poisson_holds
#print axioms RNS.OrbitalTrace.orbital_trace_vanishes_step
#print axioms RNS.OrbitalTrace.orbital_trace_vanishes_holds
