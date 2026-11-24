/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.CollatzHub.Conclusions
import Mathlib.Tactic.Ring

/-!
# Proofs for CollatzHub

Status: all sixteen claims built clean on GitHub, 2026-11-24; `#print axioms`
shows only the standard axioms.

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

/-! ## The counting formula -/

namespace RNS.CollatzHub

theorem hubIter_succ' (k u : Nat) : hubIter (k + 1) u = hubStep (hubIter k u) := by
  rw [hubIter_add, hubIter_one]

theorem preds (u v : Nat) (h : hubStep u = v) :
    u = 4 * v - 1 ∨ (v % 3 = 0 ∧ 3 * u = 2 * v) ∨ (v % 3 = 1 ∧ 3 * u = 4 * v - 1) := by
  have hc := predecessors_complete_holds
  unfold predecessors_complete at hc
  exact hc u v h

theorem mem_ancBelow (B u v : Nat) : u ∈ ancBelow B v ↔ reachesBelow B u v := by
  classical
  unfold ancBelow
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨k, -, hk⟩ := h
    have h0 := hk 0 (Nat.zero_le _)
    rwa [hubIter_zero] at h0

theorem reachesBelow_self {B v : Nat} (hv : v < B) : reachesBelow B v v := by
  refine ⟨0, hubIter_zero v, fun j hj => ?_⟩
  have hj0 : j = 0 := by omega
  rw [hj0, hubIter_zero]
  exact hv

theorem reachesBelow_step {B u p v : Nat} (h : reachesBelow B u p) (hs : hubStep p = v)
    (hv : v < B) : reachesBelow B u v := by
  obtain ⟨k, hk, hb⟩ := h
  refine ⟨k + 1, by rw [hubIter_succ', hk, hs], fun j hj => ?_⟩
  rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
  · exact hb j (by omega)
  · have hjk : j = k + 1 := by omega
    rw [hjk, hubIter_succ', hk, hs]
    exact hv

theorem reachesBelow_cases {B u v : Nat} (h : reachesBelow B u v) :
    u = v ∨ ∃ p, hubStep p = v ∧ reachesBelow B u p := by
  obtain ⟨k, hk, hb⟩ := h
  cases k with
  | zero => exact Or.inl ((hubIter_zero u).symm.trans hk)
  | succ k =>
    refine Or.inr ⟨hubIter k u, ?_, k, rfl, fun j hj => hb j (by omega)⟩
    rw [← hubIter_succ', hk]

theorem hit_twice {u v a b : Nat} (ha : hubIter a u = v) (hb : hubIter b u = v) (hab : a < b) :
    hubIter (b - a - 1 + 1) v = v := by
  have hsplit : a + (b - a - 1 + 1) = b := by omega
  calc hubIter (b - a - 1 + 1) v = hubIter (b - a - 1 + 1) (hubIter a u) := by rw [ha]
    _ = hubIter (a + (b - a - 1 + 1)) u := (hubIter_add a (b - a - 1 + 1) u).symm
    _ = hubIter b u := congrArg (fun t => hubIter t u) hsplit
    _ = v := hb

theorem self_mem {B v : Nat} (hv : v < B) : v ∈ ancBelow B v := by
  rw [mem_ancBelow]
  exact reachesBelow_self hv

theorem mem_of_pred {B u p v : Nat} (h : u ∈ ancBelow B p) (hs : hubStep p = v) (hv : v < B) :
    u ∈ ancBelow B v := by
  rw [mem_ancBelow] at h ⊢
  exact reachesBelow_step h hs hv

theorem not_mem_pred {B v p : Nat} (nc : ∀ k, hubIter (k + 1) v ≠ v) (hs : hubStep p = v) :
    v ∉ ancBelow B p := by
  intro h
  rw [mem_ancBelow] at h
  obtain ⟨k, hk, -⟩ := h
  exact nc k (by rw [hubIter_succ', hk, hs])

theorem disjoint_preds {B v p q : Nat} (nc : ∀ k, hubIter (k + 1) v ≠ v)
    (hp : hubStep p = v) (hq : hubStep q = v) (hpq : p ≠ q) :
    Disjoint (ancBelow B p) (ancBelow B q) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  rw [mem_ancBelow] at hu hu'
  obtain ⟨a, ha, -⟩ := hu
  obtain ⟨b, hb, -⟩ := hu'
  have ha' : hubIter (a + 1) u = v := by rw [hubIter_succ', ha, hp]
  have hb' : hubIter (b + 1) u = v := by rw [hubIter_succ', hb, hq]
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact nc _ (hit_twice ha' hb' (by omega))
  · rw [h] at ha
    exact hpq (ha.symm.trans hb)
  · exact nc _ (hit_twice hb' ha' (by omega))

theorem mem_cases {B u v : Nat} (h : u ∈ ancBelow B v) :
    u = v ∨ u ∈ ancBelow B (4 * v - 1) ∨ (v % 3 = 0 ∧ u ∈ ancBelow B (2 * v / 3)) ∨
      (v % 3 = 1 ∧ u ∈ ancBelow B ((4 * v - 1) / 3)) := by
  rw [mem_ancBelow] at h
  rcases reachesBelow_cases h with h | ⟨p, hs, hr⟩
  · exact Or.inl h
  · rw [← mem_ancBelow] at hr
    rcases preds p v hs with h1 | ⟨h0, h2⟩ | ⟨h0, h2⟩
    · rw [h1] at hr
      exact Or.inr (Or.inl hr)
    · have hp : p = 2 * v / 3 := by omega
      rw [hp] at hr
      exact Or.inr (Or.inr (Or.inl ⟨h0, hr⟩))
    · have hp : p = (4 * v - 1) / 3 := by omega
      rw [hp] at hr
      exact Or.inr (Or.inr (Or.inr ⟨h0, hr⟩))

theorem counting_step_holds : counting_step := by
  unfold counting_step
  intro B v hv nc
  have hv1 : 1 ≤ v := by
    by_contra hcon
    have h0 : v = 0 := by omega
    subst h0
    exact nc 0 (by decide)
  have hL : hubStep (4 * v - 1) = v := by
    unfold hubStep
    split_ifs <;> omega
  have hR : v % 3 = 0 → hubStep (2 * v / 3) = v := by
    intro h0
    rw [show 2 * v / 3 = 2 * (v / 3) by omega, hubStep_double]
    omega
  have hD : v % 3 = 1 → hubStep ((4 * v - 1) / 3) = v := by
    intro h1
    unfold hubStep
    split_ifs <;> omega
  have key : ∀ u, u ∈ ancBelow B v ↔ (u = v ∨ u ∈ ancBelow B (4 * v - 1) ∨
      (v % 3 = 0 ∧ u ∈ ancBelow B (2 * v / 3)) ∨
      (v % 3 = 1 ∧ u ∈ ancBelow B ((4 * v - 1) / 3))) := by
    intro u
    constructor
    · exact mem_cases
    · rintro (h | h | ⟨h0, h⟩ | ⟨h1, h⟩)
      · rw [h]
        exact self_mem hv
      · exact mem_of_pred h hL hv
      · exact mem_of_pred h (hR h0) hv
      · exact mem_of_pred h (hD h1) hv
  rcases (by omega : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2) with h3 | h3 | h3
  · have hR' := hR h3
    have heq : ancBelow B v = insert v (ancBelow B (4 * v - 1) ∪ ancBelow B (2 * v / 3)) := by
      ext u
      rw [key u, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro (h | h | ⟨-, h⟩ | ⟨h1, -⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h1 (by omega)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨h3, h⟩))
    have hne : 4 * v - 1 ≠ 2 * v / 3 := by omega
    have hnot : v ∉ ancBelow B (4 * v - 1) ∪ ancBelow B (2 * v / 3) := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact not_mem_pred nc hL h
      · exact not_mem_pred nc hR' h
    rw [heq, Finset.card_insert_of_notMem hnot,
      Finset.card_union_of_disjoint (disjoint_preds nc hL hR' hne), if_pos h3,
      if_neg (show ¬ (v % 3 = 1) by omega)]
    omega
  · have hD' := hD h3
    have heq : ancBelow B v =
        insert v (ancBelow B (4 * v - 1) ∪ ancBelow B ((4 * v - 1) / 3)) := by
      ext u
      rw [key u, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro (h | h | ⟨h0, -⟩ | ⟨-, h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h0 (by omega)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr ⟨h3, h⟩))
    have hne : 4 * v - 1 ≠ (4 * v - 1) / 3 := by omega
    have hnot : v ∉ ancBelow B (4 * v - 1) ∪ ancBelow B ((4 * v - 1) / 3) := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact not_mem_pred nc hL h
      · exact not_mem_pred nc hD' h
    rw [heq, Finset.card_insert_of_notMem hnot,
      Finset.card_union_of_disjoint (disjoint_preds nc hL hD' hne),
      if_neg (show ¬ (v % 3 = 0) by omega), if_pos h3]
    omega
  · have heq : ancBelow B v = insert v (ancBelow B (4 * v - 1)) := by
      ext u
      rw [key u, Finset.mem_insert]
      constructor
      · rintro (h | h | ⟨h0, -⟩ | ⟨h1, -⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h0 (by omega)
        · exact absurd h1 (by omega)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    rw [heq, Finset.card_insert_of_notMem (not_mem_pred nc hL),
      if_neg (show ¬ (v % 3 = 0) by omega), if_neg (show ¬ (v % 3 = 1) by omega)]
    omega

theorem count_zero_at_ceiling_holds : count_zero_at_ceiling := by
  unfold count_zero_at_ceiling
  intro B v hBv
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro u hu
  rw [mem_ancBelow] at hu
  obtain ⟨k, hk, hb⟩ := hu
  have hlt := hb k (Nat.le_refl k)
  rw [hk] at hlt
  omega

end RNS.CollatzHub

/-! ## The unrolled ladder sum -/

namespace RNS.CollatzHub

theorem rung_zero (v : Nat) : rung v 0 = v := rfl

theorem rung_succ (v i : Nat) : rung v (i + 1) = rung (4 * v - 1) i := rfl

theorem rung_hub_value_holds : rung_hub_value := by
  unfold rung_hub_value
  intro v i
  induction i generalizing v with
  | zero => intro hv; rw [rung_zero, Nat.pow_zero, Nat.one_mul]
  | succ i ih =>
    intro hv
    rw [rung_succ, ih (4 * v - 1) (by omega), show 6 * (4 * v - 1) - 2 = 4 * (6 * v - 2) by omega]
    generalize 6 * v - 2 = w
    ring

/-- A value on the ladder above `v` that cycles would bring `v` round too. -/
theorem no_cycle_ladder {v : Nat} (hv1 : 1 ≤ v) (nc : ∀ k, hubIter (k + 1) v ≠ v) :
    ∀ k, hubIter (k + 1) (4 * v - 1) ≠ 4 * v - 1 := by
  intro k hk
  have hL : hubStep (4 * v - 1) = v := by
    unfold hubStep
    split_ifs <;> omega
  apply nc k
  calc hubIter (k + 1) v = hubIter (k + 1) (hubIter 1 (4 * v - 1)) := by rw [hubIter_one, hL]
    _ = hubIter (1 + (k + 1)) (4 * v - 1) := (hubIter_add 1 (k + 1) _).symm
    _ = hubIter ((k + 1) + 1) (4 * v - 1) := by rw [Nat.add_comm 1 (k + 1)]
    _ = hubIter 1 (hubIter (k + 1) (4 * v - 1)) := hubIter_add (k + 1) 1 _
    _ = v := by rw [hk, hubIter_one, hL]

theorem ladder_sum_holds : ladder_sum := by
  unfold ladder_sum
  intro B v L
  induction L generalizing v with
  | zero =>
    intro _ hB _
    rw [rung_zero] at hB
    rw [Finset.range_zero, Finset.sum_empty]
    have hz := count_zero_at_ceiling_holds
    unfold count_zero_at_ceiling at hz
    exact hz B v hB
  | succ L ih =>
    intro hlt hB nc
    have hv : v < B := by
      have h0 := hlt 0 (Nat.succ_pos L)
      rwa [rung_zero] at h0
    have hv1 : 1 ≤ v := by
      by_contra hcon
      have h0 : v = 0 := by omega
      subst h0
      exact nc 0 (by decide)
    have hstep := counting_step_holds
    unfold counting_step at hstep
    have ih' := ih (4 * v - 1) (fun i hi => by rw [← rung_succ]; exact hlt (i + 1) (by omega))
      (by rw [← rung_succ]; exact hB) (no_cycle_ladder hv1 nc)
    rw [Finset.sum_range_succ', hstep B v hv nc, ih']
    simp only [rung_succ, rung_zero, rungCount]
    ring

end RNS.CollatzHub

/-! ## Smaller peaks inside a mountain -/

namespace RNS.CollatzHub

theorem reach_back {B u q v : Nat} (hs : hubStep u = q) (hu : u < B) (h : reachesBelow B q v) :
    reachesBelow B u v := by
  obtain ⟨k, hk, hb⟩ := h
  refine ⟨k + 1, by rw [hubIter_succ, hs, hk], fun j hj => ?_⟩
  rcases j with _ | j
  · rw [hubIter_zero]
    exact hu
  · rw [hubIter_succ, hs]
    exact hb j (by omega)

theorem sub_peak_rule_holds : sub_peak_rule := by
  unfold sub_peak_rule
  intro B v q hq
  have hqB : q < B := by
    rw [mem_ancBelow] at hq
    obtain ⟨k, -, hb⟩ := hq
    have h0 := hb 0 (Nat.zero_le _)
    rwa [hubIter_zero] at h0
  constructor
  · intro h6
    have hstep : hubStep (2 * q / 3) = q := by
      rw [show 2 * q / 3 = 2 * (q / 3) by omega, hubStep_double]
      omega
    have hmem : 2 * q / 3 ∈ ancBelow B v := by
      rw [mem_ancBelow] at hq ⊢
      exact reach_back hstep (by omega) hq
    exact ⟨by omega, 2 * q / 3, hmem, by omega, hstep⟩
  · rintro ⟨hodd, u, -, heven, hs⟩
    unfold hubStep at hs
    rw [if_pos heven] at hs
    omega

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
#print axioms RNS.CollatzHub.counting_step_holds
#print axioms RNS.CollatzHub.count_zero_at_ceiling_holds
#print axioms RNS.CollatzHub.rung_hub_value_holds
#print axioms RNS.CollatzHub.ladder_sum_holds
#print axioms RNS.CollatzHub.sub_peak_rule_holds
