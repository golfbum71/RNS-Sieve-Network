/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.ColumnAction.Conclusions

/-!
# Proofs for ColumnAction

Imports claims only, never other nodes' proofs. Proved directly: the
remainder of a product on division by 6 is the remainder of the product of
the two remainders. (`ColumnStructure`'s `columns_multiply` says the same for
numbers written as column entries; this form, by remainders, is the one the
column counts use, and needs nothing from it.)
-/

namespace RNS.ColumnAction

/-- **How a wheel moves the columns**, proved. -/
theorem column_action_holds : column_action := by
  intro p n
  refine ⟨fun hp => ?_, fun hp => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · rw [Nat.mul_mod, hp, Nat.one_mul, Nat.mod_mod]
  · rw [Nat.mul_mod, hp, hn]
  · rw [Nat.mul_mod, hp, hn]

end RNS.ColumnAction

#print axioms RNS.ColumnAction.column_action_holds
