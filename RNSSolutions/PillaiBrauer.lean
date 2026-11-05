/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PillaiBrauer.Conclusions

/-!
# Proofs for PillaiBrauer

Imports claims only, never other nodes' proofs. Rests on no other node.

Built clean by `lake build RNSSolutions` on 2026-11-05; `#print axioms` shows only
the standard three. The two `decide` calls are
finite checks (17 × 17 × 6 divisibility tests, and six divisibility tests);
the witness was checked numerically beforehand.

`pillai_sixteen` is cited, not proved: there is no proof of it here.
-/

namespace RNS.PillaiBrauer

/-- **The run of 17 from 2184**, by direct check. -/
theorem pillai_witness_17_holds : pillai_witness_17 := by
  unfold pillai_witness_17 small_wheels
  decide

/-- Every wheel up to 13 divides the cycle 30030. -/
private theorem small_wheels_dvd_cycle : ∀ p ∈ small_wheels, p ∣ 30030 := by
  unfold small_wheels
  decide

/-- Every wheel up to 13 is at least 2. -/
private theorem small_wheels_ge_two : ∀ p ∈ small_wheels, 2 ≤ p := by
  unfold small_wheels
  decide

/-- A wheel up to 13 dividing a member of the run from 2184 also divides the
same member of the run shifted by `m` cycles. -/
private theorem dvd_shift {p m i : Nat} (hp : p ∈ small_wheels) (h : p ∣ 2184 + i) :
    p ∣ 30030 * m + 2184 + i := by
  have e : 30030 * m + 2184 + i = 30030 * m + (2184 + i) := by omega
  rw [e]
  exact Nat.dvd_add (Dvd.dvd.mul_right (small_wheels_dvd_cycle p hp) m) h

/-- **The run repeats with the cycle**, from the run of 17 from 2184. -/
theorem pillai_witness_17_repeats_holds : pillai_witness_17_repeats := by
  intro m i hi
  obtain ⟨j, hj, hji, p, hp, hpi, hpj⟩ := pillai_witness_17_holds i hi
  refine ⟨j, hj, hji, ?_⟩
  have hdvd : p ∣ Nat.gcd (30030 * m + 2184 + i) (30030 * m + 2184 + j) :=
    Nat.dvd_gcd (dvd_shift hp hpi) (dvd_shift hp hpj)
  have hpos : 0 < Nat.gcd (30030 * m + 2184 + i) (30030 * m + 2184 + j) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  have hle := Nat.le_of_dvd hpos hdvd
  have h2 := small_wheels_ge_two p hp
  omega

end RNS.PillaiBrauer

#print axioms RNS.PillaiBrauer.pillai_witness_17_holds
#print axioms RNS.PillaiBrauer.pillai_witness_17_repeats_holds
