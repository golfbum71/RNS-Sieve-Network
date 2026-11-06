/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PrimeNumberTheorem.Conclusions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Proofs for PrimeNumberTheorem

Built clean by `lake build RNSSolutions` on 2026-11-06; `#print axioms` shows only
the standard three.

Imports claims only. `pnt_equivalent` is an outside source (PNT+ `pi_alt'`,
copied word for word) and is not proved here. The limit form follows: for `x`
above 1, `x` over its logarithm is not zero, so asymptotic equivalence is the
same as the ratio tending to 1, and the ratio of the prime count to `x` over
its logarithm is the prime count times the logarithm over `x`.
-/

namespace RNS.PrimeNumberTheorem

open Filter Topology

theorem prime_number_theorem_step (h : pnt_equivalent) : prime_number_theorem := by
  have hz : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_ne_zero (by linarith) (Real.log_pos hx).ne'
  have ht := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp h
  unfold prime_number_theorem
  refine ht.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  show (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) =
    (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x
  rw [div_div_eq_mul_div]

end RNS.PrimeNumberTheorem

#print axioms RNS.PrimeNumberTheorem.prime_number_theorem_step
