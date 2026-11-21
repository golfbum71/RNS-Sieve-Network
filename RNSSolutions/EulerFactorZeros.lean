/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.EulerFactorZeros.Conclusions
import Mathlib.Analysis.SpecialFunctions.Pow.Complex     -- `Complex.cpow_def_of_ne_zero`
import Mathlib.Analysis.SpecialFunctions.Complex.Log     -- `Complex.exp_eq_one_iff`, `Complex.natCast_log`
import Mathlib.Analysis.SpecialFunctions.Log.Basic       -- `Real.log_injOn_pos`, `Nat.Prime.log_pos`
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic -- `Real.pi_ne_zero`
import Mathlib.Data.Nat.Prime.Basic                      -- `Nat.Prime.dvd_of_dvd_pow`

/-!
# Proofs for EulerFactorZeros

Imports claims only, never other nodes' proofs.

The zeros of one wheel's factor. For a prime `p` the power `p^(-s)` is the
exponential of `-s log p`, and the exponential equals 1 exactly at the whole
multiples of `2πi` (Mathlib's `Complex.exp_eq_one_iff`). Dividing by `log p`
gives the zeros (`euler_factor_zeros_holds`).

The periods never line up. If a whole multiple of `log p` equals a whole
multiple of `log q`, take sizes: the size of the first multiple times `log p`
equals the size of the second times `log q`, so a power of `p` equals a power
of `q`. If the power of `p` is not the zeroth one, then `p` divides a power of
`q`, so `p` divides `q`, so `p = q`; for different primes that leaves only the
zeroth power (`log_periods_independent_holds`).

A common zero. A common zero is a whole multiple of `2πi / log p` and of
`2πi / log q`; clearing the denominators gives two whole multiples of `log p`
and `log q` that agree, so both are zero, and the zero is `s = 0`
(`euler_factor_common_zero_step`, from the two claims above).
-/

namespace RNS.EulerFactorZeros

theorem euler_factor_zeros_holds : euler_factor_zeros := by
  intro p hp s
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hL : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.log_ne_zero
  rw [show (1 : ℂ) - (p : ℂ) ^ (-s) = 0 ↔ (p : ℂ) ^ (-s) = 1 from sub_eq_zero.trans eq_comm,
    Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [eq_div_iff hL, Int.cast_neg]
    linear_combination -hn
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [hk, mul_neg, mul_div_cancel₀ _ hL, Int.cast_neg, neg_mul]

theorem log_periods_independent_holds : log_periods_independent := by
  intro p q hp hq hpq a b h
  have hlp := hp.log_pos
  have hlq := hq.log_pos
  have habs : (a.natAbs : ℝ) * Real.log p = (b.natAbs : ℝ) * Real.log q := by
    have h' := congrArg abs h
    rw [abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlq] at h'
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact h'
  have hpow : (p : ℝ) ^ a.natAbs = (q : ℝ) ^ b.natAbs := by
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq.pos
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hp' _)) (Set.mem_Ioi.mpr (pow_pos hq' _))
    rw [Real.log_pow, Real.log_pow]
    exact habs
  have hnat : p ^ a.natAbs = q ^ b.natAbs := by exact_mod_cast hpow
  have ha0 : a = 0 := by
    by_contra hne
    have hA : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hne
    have hdvd : p ∣ q ^ b.natAbs := by
      rw [← hnat]
      exact dvd_pow_self p hA
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))
  refine ⟨ha0, ?_⟩
  have hb : (b : ℝ) * Real.log q = 0 := by
    rw [← h, ha0]
    simp
  rcases mul_eq_zero.mp hb with h' | h'
  · exact_mod_cast h'
  · exact absurd h' hlq.ne'

theorem euler_factor_common_zero_step (hz : euler_factor_zeros)
    (hi : log_periods_independent) : euler_factor_common_zero := by
  intro p q hp hq hpq s h1 h2
  obtain ⟨a, ha⟩ := (hz p hp s).mp h1
  obtain ⟨b, hb⟩ := (hz q hq s).mp h2
  have hLp : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.log_ne_zero
  have hLq : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.log_ne_zero
  have hc : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have ea : s * (Real.log p : ℂ) = (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [ha]
    exact div_mul_cancel₀ _ hLp
  have eb : s * (Real.log q : ℂ) = (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hb]
    exact div_mul_cancel₀ _ hLq
  have key : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    have h0 : ((b : ℂ) * (Real.log p : ℂ) - (a : ℂ) * (Real.log q : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
      linear_combination (Real.log q : ℂ) * ea - (Real.log p : ℂ) * eb
    have h3 := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hc)
    exact_mod_cast h3
  obtain ⟨-, ha0⟩ := hi p q hp hq hpq b a key
  rw [ha, ha0]
  simp

theorem euler_factor_common_zero_holds : euler_factor_common_zero :=
  euler_factor_common_zero_step euler_factor_zeros_holds log_periods_independent_holds

end RNS.EulerFactorZeros

#print axioms RNS.EulerFactorZeros.euler_factor_zeros_holds
#print axioms RNS.EulerFactorZeros.log_periods_independent_holds
#print axioms RNS.EulerFactorZeros.euler_factor_common_zero_step
#print axioms RNS.EulerFactorZeros.euler_factor_common_zero_holds
