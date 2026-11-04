/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.Wheel6.Conclusions

/-!
# Proof for Wheel6

Proves `RNS.Wheel6.prime_gt_three_is_candidate`. The tactic proof is copied
unchanged from `prime_gt_three_is_candidate` in `rns_sieve_6.lean`, Part A,
Step 1, after unfolding the stated claim.

Idea: a prime above 3 is divisible by neither 2 nor 3 (either would force it
to equal that small prime), and the only remainders on division by 6 that
avoid both are 1 and 5.
-/

namespace RNS.Wheel6

theorem prime_gt_three_is_candidate_holds : prime_gt_three_is_candidate := by
  unfold prime_gt_three_is_candidate
  intro p hp h_gt
  have h2 : ¬ (2 ∣ p) := by
    intro hdvd
    rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega
  have h3 : ¬ (3 ∣ p) := by
    intro hdvd
    rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega
  unfold is_candidate
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

end RNS.Wheel6

#print axioms RNS.Wheel6.prime_gt_three_is_candidate_holds
