/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrocardWindowLength.Conclusions
import RNSNetwork.Nodes.UnitSquares24.Conclusions
import Mathlib.Tactic

/-!
# Proofs for BrocardWindowLength

Built clean by `lake build RNSSolutions` on 2026-11-22; `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

Both squares leave remainder 1 on the cycle of 24
(`UnitSquares24.prime_sq_mod_24`, taken as a named hypothesis), so their
difference is a multiple of 24. Both primes are odd, so the larger is at least
the smaller plus 2, and its square at least the smaller square plus four times
the smaller prime plus 4.
-/

namespace RNS.BrocardWindowLength

theorem window_length_mod_24_step (h : RNS.UnitSquares24.prime_sq_mod_24) :
    window_length_mod_24 := by
  intro p q hp hq h5 hpq
  have hle : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hpq.le 2
  apply (Nat.modEq_iff_dvd' hle).mp
  show p ^ 2 % 24 = q ^ 2 % 24
  rw [h p hp h5, h q hq (by omega)]

theorem window_length_lower_holds : window_length_lower := by
  intro p q hp hq h3 hpq
  have hpo : p % 2 = 1 := by rcases hp.eq_two_or_odd with h | h <;> omega
  have hqo : q % 2 = 1 := by rcases hq.eq_two_or_odd with h | h <;> omega
  have h2 : p + 2 ≤ q := by omega
  have h4 : (p + 2) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h2 2
  have h5 : 4 * p + 4 + p ^ 2 ≤ q ^ 2 := by nlinarith
  exact Nat.le_sub_of_add_le h5

end RNS.BrocardWindowLength

#print axioms RNS.BrocardWindowLength.window_length_mod_24_step
#print axioms RNS.BrocardWindowLength.window_length_lower_holds
