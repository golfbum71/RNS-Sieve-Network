/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunTwinSum.Conclusions
import RNSNetwork.Nodes.BrunTheorem.Conclusions
import Mathlib.Tactic.NormNum

/-!
# Proofs for BrunTwinSum

Imports claims only. `brun_sum_finite` is a step from
`BrunTheorem.brun_theorem`, taken as a named hypothesis: the two nodes add
the same terms (one over `p` plus one over `p + 2` for each twin pair), with
`p + 2` cast to the reals in two equal ways. The arrow is joined in
`RNSSolutions/Assemble.lean`.
-/

namespace RNS.BrunTwinSum

theorem brun_sum_finite_step (h : RNS.BrunTheorem.brun_theorem) : brun_sum_finite := by
  have e : twin_reciprocal = RNS.BrunTheorem.twin_reciprocal := by
    funext p
    unfold twin_reciprocal RNS.BrunTheorem.twin_reciprocal
    push_cast
    all_goals rfl
  unfold brun_sum_finite
  rw [e]
  exact h

end RNS.BrunTwinSum

#print axioms RNS.BrunTwinSum.brun_sum_finite_step
