/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# Admissibility — which offset patterns can repeat forever

An offset pattern is admissible when no wheel is completely covered by it.
This node records four facts about that test: it only ever needs checking at
the wheels no larger than the number of offsets; the twin pattern {0, 2}
passes; the pattern {0, 2, 4} fails at the wheel of size 3; and an evenly
spaced run passes exactly when every wheel up to its length divides the
spacing (the Lagrange–Waring condition).

Proof: `RNSSolutions/Admissibility.lean`. Metadata: `formalization.yaml`.
Source of record: `rns_sieve_6.lean`, Part B Step 1
(`admissible_of_large_primes`, the `{0, 2}` example,
`admissible_zero_two_four_false`) and Part D (`ap_offsets_admissible_iff`).
-/

namespace RNS.Admissibility

/-- **Only the small wheels need checking.** If no wheel no larger than the
number of offsets is completely covered, the pattern is admissible: a larger
wheel has more positions than the pattern has offsets, so it can never be
covered. -/
def admissible_of_large_primes : Prop :=
  ∀ T : Finset Nat, (∀ p, p.Prime → p ≤ T.card → w T p < p) → is_admissible T

/-- **The twin pattern is admissible.** The offsets {0, 2} never cover every
position of any wheel. -/
def zero_two_admissible : Prop :=
  is_admissible ({0, 2} : Finset Nat)

/-- **The pattern {0, 2, 4} is not admissible.** It covers all three
positions of the wheel of size 3, so one of any three such numbers is always
a multiple of 3. -/
def zero_two_four_not_admissible : Prop :=
  ¬ is_admissible ({0, 2, 4} : Finset Nat)

/-- **The Lagrange–Waring condition.** For a nonzero spacing, the pattern of
an evenly spaced run passes the admissibility test exactly when every prime
no larger than the run length divides the spacing. -/
def ap_offsets_admissible_iff : Prop :=
  ∀ d k : Nat, d ≠ 0 →
    (is_admissible (ap_offsets d k) ↔ ∀ p, p.Prime → p ≤ k → p ∣ d)

end RNS.Admissibility
