/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.MertensThird.Conclusions

/-!
# SmallWheelSurvivors — survivors match the share when the wheels stay below log x

Legendre's identity counts the survivors of a set of wheels up to `x` exactly,
as a sum over the sets of wheels of `x` divided by their product, rounded
down, with alternating signs. Without the rounding the sum is `x` times the
survivor share, so the count differs from `x` times the share by at most one
per set of wheels: at most 2 to the number of wheels.

With the wheels up to `log x`, that error is at most twice `x` to the power
`log 2` (about 0.69), which is small next to `x` over `log log x`. So the
survivors up to `x` number `x` times the share, and by Mertens' third theorem
that is about e to minus Euler's constant times `x` over the logarithm of the
largest wheel: the survivors times `log log x` over `x` tend to e to minus
Euler's constant. Heath-Brown, Lectures on sieves, Corollary 1.2.

Compare `CeilingOvershoot`: with the wheels up to the square root of `x` the
same share overshoots the primes by a fixed factor; the exact match holds
only while the wheels stay small.

Proof: `RNSSolutions/SmallWheelSurvivors.lean`. Rests on `BrunPureSieve`
(`legendre_exact`) and `MertensThird` (`mertens_third`).
Metadata: `formalization.yaml`.
-/

namespace RNS.SmallWheelSurvivors

open Filter Topology

/-- **Legendre's error.** For prime wheels `W`, the survivors up to `N` differ
from `N` times the survivor share by at most 2 to the number of wheels. -/
def legendre_error : Prop :=
  ∀ (W : Finset ℕ) (N : ℕ), (∀ q ∈ W, q.Prime) →
    |((survivors_upto W N).card : ℝ) - (N : ℝ) * ∏ p ∈ W, (1 - 1 / (p : ℝ))| ≤ 2 ^ W.card

/-- **Survivors of the wheels up to log x.** The numbers up to `x` that no
prime up to `log x` divides, times `log log x`, over `x`, tend to e to minus
Euler's constant. -/
def small_wheel_survivors : Prop :=
  Tendsto (fun x : ℕ =>
      ((survivors_upto (active_primes (⌊Real.log x⌋₊ + 1)) x).card : ℝ) *
        Real.log (Real.log x) / x)
    atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

end RNS.SmallWheelSurvivors
