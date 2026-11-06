/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.MertensSecond.Conclusions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proofs for MertensSecond

Imports claims only. `prime_reciprocal_upper` is a step from the outside
claim `mertens_second_remainder`, taken as a named hypothesis.

Idea. The remainder is at most its constant over the logarithm of `x`, and
for `x` at least 2 that is at most the absolute value of the constant over
the logarithm of 2. Adding the absolute value of the Meissel–Mertens
constant gives one constant that works for every `x` at least 2.
-/

namespace RNS.MertensSecond

theorem prime_reciprocal_upper_step (h : mertens_second_remainder) : prime_reciprocal_upper := by
  obtain ⟨M, C, hMC⟩ := h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|M| + |C| / Real.log 2, by positivity, fun x hx => ?_⟩
  have h1 := (abs_le.mp (hMC x hx)).2
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 < Real.log x := lt_of_lt_of_le hl2 hlx
  have h2 : C / Real.log x ≤ |C| / Real.log 2 :=
    calc C / Real.log x ≤ |C| / Real.log x := div_le_div_of_nonneg_right (le_abs_self C) hlx0.le
      _ ≤ |C| / Real.log 2 := div_le_div_of_nonneg_left (abs_nonneg C) hl2 hlx
  have h3 : M ≤ |M| := le_abs_self M
  linarith

end RNS.MertensSecond

#print axioms RNS.MertensSecond.prime_reciprocal_upper_step
