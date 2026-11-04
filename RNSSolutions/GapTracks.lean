/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Tactic.NormNum.Prime      -- `norm_num` proving small numbers prime
import RNSNetwork.Nodes.Wheel6.Conclusions
import RNSNetwork.Nodes.GapTracks.Conclusions

/-!
# Proofs for GapTracks

Imports claims only. The prime-pair claims are steps from
`Wheel6.prime_gt_three_is_candidate` (`h_w6`). Tactic proofs are copied from
`twin_cousin_sexy_tracks.lean` and `prime_gap_track_constraint.lean`, with
each call to `prime_gt_three_is_candidate` replaced by `h_w6`.
-/

namespace RNS.GapTracks

/-- **Step:** `Wheel6` implies twin primes start in the 6n-1 column. -/
theorem twin_prime_mod_six_step (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate) :
    twin_prime_mod_six := by
  unfold twin_prime_mod_six
  intro p hp_prime hq_prime hgt
  have hcand := h_w6 p hp_prime hgt
  unfold is_candidate at hcand
  simp only [Bool.or_eq_true, beq_iff_eq] at hcand
  rcases hcand with h1 | h5
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 1 := ⟨p / 6, by omega⟩
    have h3dvd : (3 : Nat) ∣ (p + 2) := ⟨2 * k + 1, by rw [hk]; ring⟩
    rcases hq_prime.eq_one_or_self_of_dvd 3 h3dvd with hc | hc <;> omega
  · exact h5

/-- **Step:** `Wheel6` implies cousin primes start in the 6n+1 column. -/
theorem cousin_prime_mod_six_step (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate) :
    cousin_prime_mod_six := by
  unfold cousin_prime_mod_six
  intro p hp_prime hq_prime hgt
  have hcand := h_w6 p hp_prime hgt
  unfold is_candidate at hcand
  simp only [Bool.or_eq_true, beq_iff_eq] at hcand
  rcases hcand with h1 | h5
  · exact h1
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 5 := ⟨p / 6, by omega⟩
    have h3dvd : (3 : Nat) ∣ (p + 4) := ⟨2 * k + 3, by rw [hk]; ring⟩
    rcases hq_prime.eq_one_or_self_of_dvd 3 h3dvd with hc | hc <;> omega

theorem sexy_prime_same_track_holds : sexy_prime_same_track := by
  unfold sexy_prime_same_track
  intro p
  omega

theorem sexy_middle_not_always_blocked_holds : sexy_middle_not_always_blocked := by
  unfold sexy_middle_not_always_blocked
  intro h
  have heq : sexy_middle 5 = 7 := by decide
  have hmid : (sexy_middle 5).Prime := by
    rw [heq]
    norm_num
  exact h 5 (by norm_num) (by norm_num) (by norm_num) hmid

/-- **Step:** `Wheel6` implies a gap from the 6n-1 column never leaves
remainder 4. -/
theorem prime_gap_forbidden_four_from_six_minus_one_step
    (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate) :
    prime_gap_forbidden_four_from_six_minus_one := by
  unfold prime_gap_forbidden_four_from_six_minus_one
  intro p q _hp hq hp3 hpq hptrack
  have hcand := h_w6 q hq (by omega)
  unfold is_candidate at hcand
  simp only [Bool.or_eq_true, beq_iff_eq] at hcand
  rcases hcand with h1 | h5 <;> omega

/-- **Step:** `Wheel6` implies a gap from the 6n+1 column never leaves
remainder 2. -/
theorem prime_gap_forbidden_two_from_six_plus_one_step
    (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate) :
    prime_gap_forbidden_two_from_six_plus_one := by
  unfold prime_gap_forbidden_two_from_six_plus_one
  intro p q _hp hq hp3 hpq hptrack
  have hcand := h_w6 q hq (by omega)
  unfold is_candidate at hcand
  simp only [Bool.or_eq_true, beq_iff_eq] at hcand
  rcases hcand with h1 | h5 <;> omega

/-- **Step:** `Wheel6` implies a gap that is a multiple of 6 keeps both primes
in the same column. -/
theorem prime_gap_same_track_of_six_dvd_step
    (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate) :
    prime_gap_same_track_of_six_dvd := by
  unfold prime_gap_same_track_of_six_dvd
  intro p q hp hq hp3 hpq hgap
  have hpcand := h_w6 p hp hp3
  have hqcand := h_w6 q hq (by omega)
  unfold is_candidate at hpcand hqcand
  simp only [Bool.or_eq_true, beq_iff_eq] at hpcand hqcand
  rcases hpcand with hp1 | hp5 <;> rcases hqcand with h1 | h5 <;> omega

end RNS.GapTracks

#print axioms RNS.GapTracks.twin_prime_mod_six_step
#print axioms RNS.GapTracks.cousin_prime_mod_six_step
#print axioms RNS.GapTracks.sexy_prime_same_track_holds
#print axioms RNS.GapTracks.sexy_middle_not_always_blocked_holds
#print axioms RNS.GapTracks.prime_gap_forbidden_four_from_six_minus_one_step
#print axioms RNS.GapTracks.prime_gap_forbidden_two_from_six_plus_one_step
#print axioms RNS.GapTracks.prime_gap_same_track_of_six_dvd_step
