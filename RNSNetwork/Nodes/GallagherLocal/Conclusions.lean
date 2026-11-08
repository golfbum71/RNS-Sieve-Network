/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# GallagherLocal — one wheel's correction averages to 1

For a single prime wheel, the correction factor of a pattern of `k` offsets
is one minus the number of positions the pattern occupies over the wheel
size, divided by one minus one over the wheel size, to the `k`: the true
surviving fraction on that wheel over the naive guess that each offset is
blocked independently. Averaged over all patterns of `k` distinct offsets
below `h`, this factor tends to 1 as `h` grows: on average the wheel is
unbiased.

The proof counts by position: one minus the occupied share is the share of
the wheel's positions the pattern avoids, and for each position the patterns
avoiding it are the `k`-sets of the offsets below `h` outside that position's
class, about `h` times one minus one over the wheel size of them. This is the
one-wheel step of Gallagher's theorem (Soundararajan, Lecture 1), which
`GallagherAverage` cites for all the wheels together.

Proof: `RNSSolutions/GallagherLocal.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.GallagherLocal

open Filter Topology

/-- The correction factor of the wheel of size `p` for the pattern `T`. -/
noncomputable def one_wheel_factor (p : Nat) (T : Finset Nat) : ℝ :=
  (1 - (w T p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ T.card

/-- **One wheel's correction averages to 1.** For a prime wheel `p` and
`k ≥ 1`, the average of the correction factor over the sets of `k` offsets
below `h` tends to 1 as `h` tends to infinity. -/
def one_wheel_average : Prop :=
  ∀ p k : Nat, p.Prime → 1 ≤ k →
    Tendsto (fun h : Nat => (∑ T ∈ (Finset.range h).powersetCard k, one_wheel_factor p T) /
        (h.choose k : ℝ))
      atTop (𝓝 1)

end RNS.GallagherLocal
