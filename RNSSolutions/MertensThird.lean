/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.MertensThird.Conclusions
import Mathlib.Topology.Algebra.Order.Field            -- `Filter.Tendsto.div_atTop`
import Mathlib.Analysis.Normed.Group.Continuity        -- `squeeze_zero_norm'`
import Mathlib.Topology.Algebra.Group.ContinuousDiv    -- `tendsto_sub_nhds_zero_iff`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Proofs for MertensThird

Imports claims only. `mertens_third_error` is an outside source (PNT+) and is
not proved here; the limit form is proved from it.

Idea. The survivor share times the logarithm, minus e to the minus Euler's
constant, equals the logarithm times (the share minus e to the minus Euler's
constant over the logarithm). By the error form that is at most the constant
over the logarithm, which tends to 0.
-/

namespace RNS.MertensThird

open Filter Topology

theorem mertens_third_step (h : mertens_third_error) : mertens_third := by
  obtain ⟨C, hC⟩ := h
  unfold mertens_third
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm' (a := fun x => C / Real.log x)
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    show ‖survivor_share x * Real.log x - Real.exp (-Real.eulerMascheroniConstant)‖ ≤
      C / Real.log x
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have hl' : Real.log x ≠ 0 := hl.ne'
    have hb := hC x hx
    have heq : survivor_share x * Real.log x - Real.exp (-Real.eulerMascheroniConstant) =
        Real.log x *
          (survivor_share x - Real.exp (-Real.eulerMascheroniConstant) / Real.log x) := by
      first | (field_simp; ring) | field_simp
    rw [Real.norm_eq_abs, heq, abs_mul, abs_of_pos hl]
    calc Real.log x *
          |survivor_share x - Real.exp (-Real.eulerMascheroniConstant) / Real.log x|
        ≤ Real.log x * (C / Real.log x ^ 2) := mul_le_mul_of_nonneg_left hb hl.le
      _ = C / Real.log x := by first | (field_simp; ring) | field_simp
  · exact Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop

end RNS.MertensThird

#print axioms RNS.MertensThird.mertens_third_step
