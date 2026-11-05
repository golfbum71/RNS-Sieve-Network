/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# PillaiBrauer — runs where no member is coprime to all the others

Pillai (1940) showed that among any 16 or fewer consecutive positive integers
one is coprime to all the others; Pillai and Brauer (1941) showed that for
every length from 17 on there are runs where none is.

In RNS terms the two halves sit on the wheels up to 13. Two members of a run
of 16 share a factor only through a wheel below 16, so only the wheels
2, 3, 5, 7, 11, 13 matter; and a run of 17 where every member shares a wheel
with another member is a setting of those six wheels, which repeats with
their combined cycle 30030.

Stated here:
* `pillai_sixteen` — the "at most 16" half, cited from Pillai (not proved in
  Lean: it needs a case analysis over all positions of the cycle 30030);
* `pillai_witness_17` — the run 2184, ..., 2200: every member shares one of
  the wheels 2, 3, 5, 7, 11, 13 with another member (a finite check);
* `pillai_witness_17_repeats` — shifting that run by any multiple of the
  cycle 30030 keeps the property, so there are infinitely many such runs.

Proofs: `RNSSolutions/PillaiBrauer.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.PillaiBrauer

/-- The six wheels up to 13. -/
def small_wheels : Finset Nat := {2, 3, 5, 7, 11, 13}

/-- **Pillai's theorem** (cited). Any run of between 1 and 16 consecutive
positive integers contains a member coprime to every other member. -/
def pillai_sixteen : Prop :=
  ∀ n k : Nat, 1 ≤ n → 1 ≤ k → k ≤ 16 →
    ∃ i < k, ∀ j < k, j ≠ i → Nat.Coprime (n + i) (n + j)

/-- **The run of 17 from 2184.** Each of 2184, ..., 2200 shares one of the
wheels 2, 3, 5, 7, 11, 13 with some other member of the run. -/
def pillai_witness_17 : Prop :=
  ∀ i < 17, ∃ j < 17, j ≠ i ∧ ∃ p ∈ small_wheels, p ∣ 2184 + i ∧ p ∣ 2184 + j

/-- **The run repeats with the cycle.** For every number of cycles `m`, in the
run of 17 starting at `30030 * m + 2184` no member is coprime to all the
others. -/
def pillai_witness_17_repeats : Prop :=
  ∀ m : Nat, ∀ i < 17, ∃ j < 17, j ≠ i ∧
    1 < Nat.gcd (30030 * m + 2184 + i) (30030 * m + 2184 + j)

end RNS.PillaiBrauer
