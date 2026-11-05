/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# GallagherAverage — the wheel correction is 1 on average

Fix a number of offsets `k`. Over all offset patterns made of `k` distinct
numbers from 1 to `h`, average the Hardy–Littlewood constant: the product,
over all wheels, of each wheel's correction factor (node `SingularSeries`).
As `h` grows the average tends to 1. So, averaged over patterns, the wheels
block as if each blocked independently: the per-wheel correction factors
cancel out on average.

This is Gallagher's theorem (1976). Gallagher averages over ordered tuples
of distinct offsets; averaging over sets of offsets, as here, divides the
sum and the count by the same number of orderings, so the limit is the same.

Cited, not proved in Lean.

Metadata: `formalization.yaml`.
-/

namespace RNS.GallagherAverage

/-- **Gallagher's average** (cited). For every number of offsets `k` from 1
on, the average of the Hardy–Littlewood constant over the sets of `k`
distinct offsets from 1 to `h` tends to 1 as `h` grows. -/
def singular_series_average_one : Prop :=
  ∀ k : Nat, 1 ≤ k →
    Filter.Tendsto
      (fun h : Nat =>
        (∑ T ∈ (Finset.Icc 1 h).powersetCard k, hardy_littlewood_constant T)
          / (((Finset.Icc 1 h).powersetCard k).card : Real))
      Filter.atTop (nhds 1)

end RNS.GallagherAverage
