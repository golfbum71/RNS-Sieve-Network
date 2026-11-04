/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# GapTracks — which gaps each column allows

The smaller of two twin primes above 3 always lies in the 6n-1 column, and
the smaller of two cousin primes in the 6n+1 column. In general, a gap
starting from the 6n-1 column never leaves remainder 4 on division by 6, and
a gap starting from the 6n+1 column never leaves remainder 2; a gap that is a
multiple of 6 keeps both primes in the same column. One claim is refuted
rather than proved: the wheel number between two primes six apart is not
always composite.

These say which gaps are forbidden, not which ones actually occur.

Proof: `RNSSolutions/GapTracks.lean`. The prime-pair claims assume
`Wheel6.prime_gt_three_is_candidate`. Metadata: `formalization.yaml`.

Source of record: `twin_cousin_sexy_tracks.lean` and
`prime_gap_track_constraint.lean`.
-/

namespace RNS.GapTracks

/-- **Twin primes start in the 6n-1 column.** -/
def twin_prime_mod_six : Prop :=
  ∀ p : Nat, p.Prime → (p + 2).Prime → 3 < p → p % 6 = 5

/-- **Cousin primes start in the 6n+1 column.** -/
def cousin_prime_mod_six : Prop :=
  ∀ p : Nat, p.Prime → (p + 4).Prime → 3 < p → p % 6 = 1

/-- **Adding 6 keeps the column** (true for every number, prime or not). -/
def sexy_prime_same_track : Prop :=
  ∀ p : Nat, p % 6 = (p + 6) % 6

/-- The one wheel number strictly between a number and that number plus 6, in
the other column. Defined here because only this node uses it. -/
def sexy_middle (p : Nat) : Nat := if p % 6 = 5 then p + 2 else p + 4

/-- **Refuted: the middle number is not always composite.** It is false that,
for every pair of primes six apart above 3, the wheel number between them is
composite (5, 7, 11 is a counterexample). -/
def sexy_middle_not_always_blocked : Prop :=
  ¬ (∀ p : Nat, p.Prime → (p + 6).Prime → 3 < p → ¬ (sexy_middle p).Prime)

/-- **From the 6n-1 column, no gap leaves remainder 4.** -/
def prime_gap_forbidden_four_from_six_minus_one : Prop :=
  ∀ p q : Nat, p.Prime → q.Prime → 3 < p → p < q → p % 6 = 5 → (q - p) % 6 ≠ 4

/-- **From the 6n+1 column, no gap leaves remainder 2.** -/
def prime_gap_forbidden_two_from_six_plus_one : Prop :=
  ∀ p q : Nat, p.Prime → q.Prime → 3 < p → p < q → p % 6 = 1 → (q - p) % 6 ≠ 2

/-- **A gap that is a multiple of 6 keeps both primes in the same column.** -/
def prime_gap_same_track_of_six_dvd : Prop :=
  ∀ p q : Nat, p.Prime → q.Prime → 3 < p → p < q → (q - p) % 6 = 0 → p % 6 = q % 6

end RNS.GapTracks
