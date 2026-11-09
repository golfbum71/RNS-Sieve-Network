/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.RailBrunTitchmarsh.Conclusions
import Mathlib

/-!
# Proofs for RailBrunTitchmarsh

Imports claims only, never other nodes' proofs. `column_window_weak` is a
step: it takes `BrunTitchmarshPNT.primes_between_le` as a named hypothesis,
joined in `RNSSolutions/Assemble.lean`.

Idea. The column primes of the window are a subset of its primes; then PNT+'s
bound for all the window's primes applies.
-/

namespace RNS.RailBrunTitchmarsh

theorem column_window_le_all_holds : column_window_le_all := by
  intro r a b
  unfold column_primes_between RNS.BrunTitchmarshPNT.primesBetween
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1⟩

theorem column_window_weak_step (h : RNS.BrunTitchmarshPNT.primes_between_le) :
    column_window_weak := by
  intro r x y z hx hy hz
  have h1 : (column_primes_between r x (x + y) : ℝ) ≤
      (RNS.BrunTitchmarshPNT.primesBetween x (x + y) : ℝ) := by
    exact_mod_cast column_window_le_all_holds r x (x + y)
  exact le_trans h1 (h x y z hx hy hz)

#print axioms RNS.RailBrunTitchmarsh.column_window_le_all_holds
#print axioms RNS.RailBrunTitchmarsh.column_window_weak_step

end RNS.RailBrunTitchmarsh
