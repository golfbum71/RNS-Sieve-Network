/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# BlockingRuns — blocking runs and the largest survivor gap

A **setting of the wheels** chooses one blocked position on each active wheel
(the ordinary sieve blocks position 0 on every wheel). A **blocked run** is a
stretch of consecutive numbers each landing on its wheel's blocked position
for some wheel.

Every setting is a shift of the ordinary one: by the Chinese Remainder
Theorem there is one position of the combined cycle that moves every wheel's
blocked position to 0 at once. So a run blocked by any setting reappears,
shifted, as a run of numbers each divisible by some wheel. And such a run
sits between two consecutive survivors. Together: a run of a given length can
be blocked by some setting exactly when some gap between consecutive
survivors is at least one longer. The longest blocked run is one less than
the largest gap between survivors (Jacobsthal's function of the cycle length).

Proof: `RNSSolutions/BlockingRuns.lean`, which assumes `CRT`'s
`crt_map_bijective` and nothing else. Metadata: `formalization.yaml`.

Standard terms: covering consecutive integers by one residue class per prime;
Jacobsthal's function of the primorial; Erdős Problem 687.
-/

namespace RNS.BlockingRuns

/-- **Every setting of the wheels is a shift of the ordinary sieve.** For the
wheels below `limit`, a setting `b` (one blocked position per wheel), and a
run of `L` numbers from `s` each landing on its blocked position on some
wheel: there is a starting point `s'` (at least 1) from which `L` consecutive
numbers are each divisible by some wheel. -/
def blocked_run_is_shift : Prop :=
  ∀ (limit s L : Nat) (b : ∀ q : active_primes limit, ZMod (q : Nat)),
    (∀ i < L, ∃ q : active_primes limit, ((s + i : Nat) : ZMod (q : Nat)) = b q) →
    ∃ s', 1 ≤ s' ∧ ∀ i < L, ∃ q ∈ active_primes limit, q ∣ s' + i

/-- **The longest blocked run is one less than the largest survivor gap.** For
the wheels below `limit` and a length `L`: some setting of the wheels blocks
a run of `L` consecutive numbers exactly when there are two consecutive
survivors `a < c` (no survivor strictly between) with `c - a` at least
`L + 1`. -/
def longest_blocked_run_eq_max_gap_sub_one : Prop :=
  ∀ (limit L : Nat),
    (∃ (b : ∀ q : active_primes limit, ZMod (q : Nat)) (s : Nat),
        ∀ i < L, ∃ q : active_primes limit, ((s + i : Nat) : ZMod (q : Nat)) = b q) ↔
    (∃ a c : Nat, (∀ q ∈ active_primes limit, ¬ q ∣ a) ∧ (∀ q ∈ active_primes limit, ¬ q ∣ c) ∧
        a < c ∧ (∀ m, a < m → m < c → ∃ q ∈ active_primes limit, q ∣ m) ∧ L + 1 ≤ c - a)

end RNS.BlockingRuns
