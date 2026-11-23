/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PileUpLock.Conclusions

/-!
# TeamShift — a team sharing a factor: shift the clock, the team stays put

The runner to be lonely stands still. A team of at least two moving runners
has a lonely moment, and every team speed is a multiple of some number that
does not divide the speed of one more runner. Step the clock forward by
multiples of one over that number: every team runner comes back to the same
place, while the extra runner visits evenly spaced spots, at least two of them.
One spot is at least a quarter of a lap from the start, which is enough for the
enlarged field of at least four runners. So the enlarged set has a lonely
moment (`team_shift`). With the Lonely Runner Conjecture for one runner fewer
as a named hypothesis, this is Rosenfeld's reduction (`team_shift_step`).

Rosenfeld 2025, Lemma 5 (arXiv 2509.14111), in a slightly stronger form: the
team's common factor need only fail to divide the extra speed (the same
"not locked" condition as `PileUpLock`), rather than all speeds sharing no
factor. Requires a team of at least two runners (Rosenfeld's lemma is used for
at least three moving runners).

Proof: `RNSSolutions/TeamShift.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.TeamShift

open RNS.PileUpLock

/-- **Team shift.** If the team `T` (at least two moving runners) has a lonely
moment, every team speed is a multiple of `q`, and `q` does not divide the speed
`u` of one more runner, then the team together with that runner has a lonely
moment. -/
def team_shift : Prop :=
  ∀ (T : Finset ℤ) (u q : ℤ), 2 ≤ T.card → u ∉ T → (∀ v ∈ T, q ∣ v) → ¬ q ∣ u →
    has_lonely_time T → has_lonely_time (insert u T)

/-- **Rosenfeld's reduction.** If the Lonely Runner Conjecture holds for fields
of up to `c + 1` runners, then a set made of a team of `2` to `c` nonzero speeds
sharing a factor, plus one speed that factor does not divide, has a lonely
moment. -/
def team_shift_step : Prop :=
  ∀ c : ℕ, lonely_runner_upto c →
    ∀ (T : Finset ℤ) (u q : ℤ), 0 ∉ T → 2 ≤ T.card → T.card ≤ c → u ∉ T →
      (∀ v ∈ T, q ∣ v) → ¬ q ∣ u → has_lonely_time (insert u T)

end RNS.TeamShift
