/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.MertensThird.Conclusions
import Mathlib.Topology.Algebra.Order.Field            -- `Filter.Tendsto.div_atTop`
import Mathlib.Analysis.Normed.Group.Continuity        -- `squeeze_zero_norm'`
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Proofs for MertensThird

Imports claims only. `mertens_third_remainder` is an outside source (PNT+
`Mertens.E₃.abs_le`, copied word for word) and is not proved here.

`product_identity_holds` is adapted from PNT+ `Mertens.prod_one_minus_div_prime_eq`
(PrimeNumberTheoremAnd, `PrimeNumberTheoremAnd/IEANTN/Mertens.lean`, commit
127b50e, Apache 2.0): the only change is the first step, matching the
network's wheels (primes below `⌊x⌋₊ + 1`) with PNT+'s primes in `Ioc 0 ⌊x⌋₊`.

The limit form: the remainder is at most a constant over the logarithm, so it
tends to 0; by the identity, the share times the logarithm is e to the minus
Euler's constant times e to the remainder, which tends to e to the minus
Euler's constant.
-/

namespace RNS.MertensThird

open Filter Topology

theorem product_identity_holds : product_identity := by
  intro x hx
  have hset : active_primes (⌊x⌋₊ + 1) = (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [active_primes, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨by omega, h3⟩
  unfold survivor_share
  rw [hset]
  -- From here on, the PNT+ proof of `Mertens.prod_one_minus_div_prime_eq`.
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, Real.exp_add, Real.exp_add, Real.exp_sum, Real.exp_log hlog, Real.exp_neg,
    Finset.prod_congr rfl fun p hp ↦ Real.exp_log (hpos (Finset.mem_filter.mp hp).2)]
  field_simp

theorem mertens_third_step (h : mertens_third_remainder) : mertens_third := by
  obtain ⟨C, hC⟩ := h
  have hE : Tendsto E₃ atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x => C / Real.log x)
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
      rw [Real.norm_eq_abs]
      exact hC x hx
    · exact Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  have h2 : Tendsto (fun x => Real.exp (-Real.eulerMascheroniConstant) * Real.exp (E₃ x))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) * Real.exp 0)) :=
    ((Real.continuous_exp.tendsto 0).comp hE).const_mul _
  rw [Real.exp_zero, mul_one] at h2
  unfold mertens_third
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  show Real.exp (-Real.eulerMascheroniConstant) * Real.exp (E₃ x) =
    survivor_share x * Real.log x
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [product_identity_holds x hx]
  first | (field_simp; ring) | field_simp | rw [div_mul_cancel₀ _ hl]

end RNS.MertensThird

#print axioms RNS.MertensThird.product_identity_holds
#print axioms RNS.MertensThird.mertens_third_step
