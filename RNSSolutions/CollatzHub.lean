/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.CollatzHub.Conclusions
import Mathlib.Tactic.Ring

/-!
# Proofs for CollatzHub

Status: draft, waiting for its first GitHub build.

Most claims are remainder bookkeeping: unfold the two maps, split on each
`if`, and let `omega` check the linear arithmetic in every case. The run
formula is an induction on the run length (one factor of 2 traded for one
factor of 3 per loop), and exit pairing follows from it: both runs end on
`3^k·m` or `3^(k+1)·m`, and when `3^k·m` leaves remainder 1 on division by 4
the next loop sends both to `(3^(k+1)·m + 1)/4`.
-/

namespace RNS.CollatzHub

theorem hubIter_zero (n : Nat) : hubIter 0 n = n := rfl

theorem hubIter_succ (k n : Nat) : hubIter (k + 1) n = hubIter k (hubStep n) := rfl

theorem hubIter_one (n : Nat) : hubIter 1 n = hubStep n := rfl

theorem hubIter_add (a b n : Nat) : hubIter (a + b) n = hubIter b (hubIter a n) := by
  induction a generalizing n with
  | zero => rw [Nat.zero_add, hubIter_zero]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [hubIter_succ]
    exact ih _

theorem hubStep_double (t : Nat) : hubStep (2 * t) = 3 * t := by
  unfold hubStep
  split_ifs <;> omega

theorem hubStep_triple (x : Nat) (hx : x % 4 = 1) : hubStep (3 * x) = hubStep x := by
  unfold hubStep
  split_ifs <;> omega

theorem run (k m : Nat) : hubIter k (2 ^ k * m) = 3 ^ k * m := by
  induction k generalizing m with
  | zero => simp [hubIter_zero]
  | succ k ih =>
    rw [hubIter_succ, show (2 : Nat) ^ (k + 1) * m = 2 * (2 ^ k * m) by ring, hubStep_double,
      show 3 * (2 ^ k * m) = 2 ^ k * (3 * m) by ring, ih]
    ring

theorem hub_step_tracks_collatz_holds : hub_step_tracks_collatz := by
  unfold hub_step_tracks_collatz
  intro n hn
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    (unfold col hubStep; split_ifs <;> omega)

theorem run_formula_holds : run_formula := by
  unfold run_formula
  exact run

theorem exit_pairing_holds : exit_pairing := by
  unfold exit_pairing
  intro k m h
  have h1 : hubIter (k + 2) (2 ^ (k + 1) * m) = hubStep (3 ^ (k + 1) * m) := by
    rw [show k + 2 = (k + 1) + 1 by omega, hubIter_add, run, hubIter_one]
  have h2 : hubIter (k + 1) (2 ^ k * m) = hubStep (3 ^ k * m) := by
    rw [hubIter_add, run, hubIter_one]
  rw [h1, h2, show 3 ^ (k + 1) * m = 3 * (3 ^ k * m) by ring]
  exact hubStep_triple _ h

theorem predecessors_complete_holds : predecessors_complete := by
  unfold predecessors_complete
  intro u v h
  subst h
  unfold hubStep
  split_ifs <;> omega

theorem ladder_entry_holds : ladder_entry := by
  unfold ladder_entry
  intro v hv
  refine ⟨?_, by omega⟩
  unfold hubStep
  split_ifs <;> omega

theorem ladder_cycle_holds : ladder_cycle := by
  unfold ladder_cycle
  intro v hv
  omega

theorem run_entry_holds : run_entry := by
  unfold run_entry
  exact hubStep_double

theorem pairing_is_ladder_holds : pairing_is_ladder := by
  unfold pairing_is_ladder
  intro j
  refine ⟨?_, ?_⟩
  · unfold hubStep
    split_ifs <;> omega
  · show hubIter 0 (hubStep (hubStep (8 * j + 2))) = 3 * j + 1
    rw [hubIter_zero, show 8 * j + 2 = 2 * (4 * j + 1) by ring, hubStep_double]
    unfold hubStep
    split_ifs <;> omega

theorem up_only_on_bad_loop_holds : up_only_on_bad_loop := by
  unfold up_only_on_bad_loop
  intro n h
  unfold hubStep at h
  split_ifs at h <;> omega

theorem funnel_trunk_holds : funnel_trunk := by
  unfold funnel_trunk
  intro u P hP h3 h hlt
  subst h
  unfold hubStep at *
  split_ifs at * <;> omega

theorem fair_block_holds : fair_block := by
  unfold fair_block
  intro k
  unfold hubStep
  split_ifs <;> omega

end RNS.CollatzHub

#print axioms RNS.CollatzHub.hub_step_tracks_collatz_holds
#print axioms RNS.CollatzHub.run_formula_holds
#print axioms RNS.CollatzHub.exit_pairing_holds
#print axioms RNS.CollatzHub.predecessors_complete_holds
#print axioms RNS.CollatzHub.ladder_entry_holds
#print axioms RNS.CollatzHub.ladder_cycle_holds
#print axioms RNS.CollatzHub.run_entry_holds
#print axioms RNS.CollatzHub.pairing_is_ladder_holds
#print axioms RNS.CollatzHub.up_only_on_bad_loop_holds
#print axioms RNS.CollatzHub.funnel_trunk_holds
#print axioms RNS.CollatzHub.fair_block_holds
