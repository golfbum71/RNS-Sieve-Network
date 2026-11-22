/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.VonKochBound.Conclusions
import Mathlib.Tactic

/-!
# Proofs for VonKochBound

Built clean by `lake build RNSSolutions` on 2026-11-22; `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`. Von Koch's bound itself is cited, not proved. The size
comparison: past e⁴ the logarithm exceeds 4.
-/

namespace RNS.VonKochBound

theorem error_exceeds_window_holds : error_exceeds_window := by
  intro x hx
  have hx0 : 0 < x := lt_trans (Real.exp_pos 4) hx
  have hlog : 4 < Real.log x := (Real.lt_log_iff_exp_lt hx0).mpr hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  nlinarith

end RNS.VonKochBound

#print axioms RNS.VonKochBound.error_exceeds_window_holds
