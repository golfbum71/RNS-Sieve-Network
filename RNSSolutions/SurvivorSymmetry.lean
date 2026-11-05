/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SurvivorSymmetry.Conclusions

/-!
# Proofs for SurvivorSymmetry

Imports claims only, never other nodes' proofs. Proves the node's one claim
directly; it rests on no other node.
-/

namespace RNS.SurvivorSymmetry

/-- A wheel of the cycle divides a position exactly when it divides the
position's reflection. -/
private theorem dvd_reflection_iff (W : Finset Nat) (k q : Nat) (hk : k ≤ W.prod id)
    (hq : q ∈ W) : q ∣ k ↔ q ∣ W.prod id - k := by
  have hP : q ∣ W.prod id := Finset.dvd_prod_of_mem id hq
  have e : W.prod id - k + k = W.prod id := Nat.sub_add_cancel hk
  constructor
  · intro h
    exact Nat.dvd_sub hP h
  · intro h
    rw [← e] at hP
    exact (Nat.dvd_add_right h).mp hP

/-- **Mirror symmetry**, proved. -/
theorem survivor_reflection_holds : survivor_reflection := by
  intro W k hk
  constructor
  · intro h q hq hd
    exact h q hq ((dvd_reflection_iff W k q hk hq).mpr hd)
  · intro h q hq hd
    exact h q hq ((dvd_reflection_iff W k q hk hq).mp hd)

end RNS.SurvivorSymmetry

#print axioms RNS.SurvivorSymmetry.survivor_reflection_holds
