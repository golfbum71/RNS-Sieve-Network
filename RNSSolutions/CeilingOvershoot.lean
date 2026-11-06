/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.CeilingOvershoot.Conclusions
import Mathlib.Analysis.Real.Sqrt                      -- `Real.tendsto_sqrt_atTop`
import Mathlib.Topology.Algebra.GroupWithZero          -- `Filter.Tendsto.inv₀`
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Proofs for CeilingOvershoot

Built clean by `lake build RNSSolutions` on 2026-11-06; `#print axioms` shows only
the standard three.

Imports claims only. A step from `MertensThird.mertens_third` and
`PrimeNumberTheorem.prime_number_theorem`, both taken as named hypotheses.

Idea. The logarithm of the square root of `x` is half the logarithm of `x`.
So the share at the square root times `x` over the prime count is (share at
the square root times the logarithm of the square root) times 2 times (the
prime count times the logarithm of `x` over `x`) inverted. The first factor
tends to e to the minus Euler's constant (Mertens, along the square root), the
last to 1 (the prime number theorem, inverted).
-/

namespace RNS.CeilingOvershoot

open Filter Topology

theorem ceiling_overshoot_step (hm : RNS.MertensThird.mertens_third)
    (hp : RNS.PrimeNumberTheorem.prime_number_theorem) : ceiling_overshoot := by
  unfold ceiling_overshoot
  unfold RNS.MertensThird.mertens_third at hm
  unfold RNS.PrimeNumberTheorem.prime_number_theorem at hp
  have h1 := hm.comp Real.tendsto_sqrt_atTop
  have h2 := hp.inv₀ one_ne_zero
  have h3 := (h1.mul_const 2).mul h2
  have hlim : Real.exp (-Real.eulerMascheroniConstant) * 2 * (1 : ℝ)⁻¹ =
      2 * Real.exp (-Real.eulerMascheroniConstant) := by ring
  rw [hlim] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  show RNS.MertensThird.survivor_share (Real.sqrt x) * Real.log (Real.sqrt x) * 2 *
      ((Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x)⁻¹ =
    RNS.MertensThird.survivor_share (Real.sqrt x) * x / (Nat.primeCounting ⌊x⌋₊ : ℝ)
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hx0 : x ≠ 0 := by linarith
  rw [Real.log_sqrt (by linarith), inv_div]
  by_cases hπ : (Nat.primeCounting ⌊x⌋₊ : ℝ) = 0
  · rw [hπ]
    simp
  · first | (field_simp; ring) | field_simp

end RNS.CeilingOvershoot

#print axioms RNS.CeilingOvershoot.ceiling_overshoot_step
