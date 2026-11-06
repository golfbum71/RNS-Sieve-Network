/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunTwinBound.Conclusions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BrunAnalytic — how few twin primes there are (Brun stage 5)

Brun's sieve, stage 5: choose the wheels and the stopping point.

* `twin_product_bound`: for the wheels below `L`, the product of one minus
  each wheel's twin share is the twin share of the cycle, so `ShareBounds`
  bounds it by twice one over the logarithm of `L`, squared.
* `twin_prime_count_bound`: the twin prime pairs up to `N` number at most a
  constant times `N` divided by the logarithm of `N` to the power three
  halves, for all `N` from some point on.

The choice, for `N` from some point on: let `u` be the eighth root of the
logarithm of `N`. Take the wheels below the first whole number past `e` to the
`u⁶` (so the logarithm of the largest wheel is about the logarithm of `N` to
the power three quarters), and stop inclusion–exclusion after the sets of
about `46 u` wheels. Then each of the four parts of `BrunTwinBound`'s bound
(the small positions, the product, the truncation error and the twin roots
over the sets used) is at most a small multiple of `N` over `u¹²`, which is
`N` over the logarithm of `N` to the three halves. The truncation error is
small by `BrunTruncation`'s power bound, using Mertens' second theorem for
the total twin share.

The power three halves is more than one, which is what makes the sum of the
reciprocals of the twin primes converge (Brun's theorem).

Proof: `RNSSolutions/BrunAnalytic.lean`. Rests on `SurvivorCount`,
`ShareBounds`, `BrunTwinBound`, `BrunTruncation` and `MertensSecond`.
Metadata: `formalization.yaml`.
-/

namespace RNS.BrunAnalytic

open RNS.BrunTwinBound

/-- **The twin product for the wheels below `L`.** -/
def twin_product_bound : Prop :=
  ∀ L : Nat, 2 ≤ L → ∏ p ∈ active_primes L, (1 - twin_g p) ≤ 2 * (1 / Real.log L) ^ 2

/-- **Brun's bound on the twin primes.** -/
def twin_prime_count_bound : Prop :=
  ∃ C N₀ : ℝ, ∀ N : Nat, N₀ ≤ (N : ℝ) →
    (twin_prime_count N : ℝ) ≤ C * N / Real.log N ^ ((3 : ℝ) / 2)

end RNS.BrunAnalytic
