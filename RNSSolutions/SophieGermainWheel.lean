/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.Wheel6.Conclusions
import RNSNetwork.Nodes.WheelOrder.Conclusions
import RNSNetwork.Nodes.SophieGermainWheel.Conclusions

/-!
# Proofs for SophieGermainWheel

Imports claims only. The column claim is a step from
`Wheel6.prime_gt_three_is_candidate` (`h_w6`); the last-digit claim is a step
from `WheelOrder.prime_gt_five_digit_ok` (`h_d5`). Tactic proofs are copied
from `sophie_germain_wheel.lean`, with those two calls replaced by the
hypotheses.
-/

namespace RNS.SophieGermainWheel

/-- **Step:** `Wheel6` implies Sophie Germain primes above 3 sit in the 6n-1
column. -/
theorem sophie_germain_mod_six_step (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate) :
    sophie_germain_mod_six := by
  unfold sophie_germain_mod_six
  intro p hp hgt
  obtain ⟨hp_prime, hq_prime⟩ := hp
  have hcand := h_w6 p hp_prime hgt
  unfold is_candidate at hcand
  simp only [Bool.or_eq_true, beq_iff_eq] at hcand
  rcases hcand with h1 | h5
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 1 := ⟨p / 6, by omega⟩
    have h3dvd : (3 : Nat) ∣ (2 * p + 1) := ⟨4 * k + 1, by rw [hk]; ring⟩
    rcases hq_prime.eq_one_or_self_of_dvd 3 h3dvd with hc | hc <;> omega
  · exact h5

private theorem not_ends_in_seven_aux (p : Nat) (hp : sophie_germain p) : p % 10 ≠ 7 := by
  obtain ⟨_, hq_prime⟩ := hp
  intro h7
  obtain ⟨k, hk⟩ : ∃ k, p = 10 * k + 7 := ⟨p / 10, by omega⟩
  have h5dvd : (5 : Nat) ∣ (2 * p + 1) := ⟨4 * k + 3, by rw [hk]; ring⟩
  rcases hq_prime.eq_one_or_self_of_dvd 5 h5dvd with hc | hc <;> omega

theorem sophie_germain_not_ends_in_seven_holds : sophie_germain_not_ends_in_seven := by
  unfold sophie_germain_not_ends_in_seven
  exact not_ends_in_seven_aux

/-- **Step:** the last-digit wheel implies a Sophie Germain prime above 5 ends
in 1, 3 or 9. -/
theorem sophie_germain_last_digit_step (h_d5 : RNS.WheelOrder.prime_gt_five_digit_ok) :
    sophie_germain_last_digit := by
  unfold sophie_germain_last_digit
  intro p hp hgt
  have hne7 := not_ends_in_seven_aux p hp
  obtain ⟨hp_prime, _⟩ := hp
  have hdigit := h_d5 p hp_prime hgt
  unfold digit_ok at hdigit
  simp only [Bool.or_eq_true, beq_iff_eq] at hdigit
  omega

end RNS.SophieGermainWheel

#print axioms RNS.SophieGermainWheel.sophie_germain_mod_six_step
#print axioms RNS.SophieGermainWheel.sophie_germain_not_ends_in_seven_holds
#print axioms RNS.SophieGermainWheel.sophie_germain_last_digit_step
