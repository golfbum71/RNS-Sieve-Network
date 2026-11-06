/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.MertensThird.Conclusions
import RNSNetwork.Nodes.PrimeNumberTheorem.Conclusions

/-!
# CeilingOvershoot — the wheel product overshoots the primes by about 12%

Freeze the wheels up to the square root of `x`, so that `x` sits at the
ceiling. Below the ceiling the survivors are exactly 1 and the primes above
the wheels (`ShieldCertificates.window_prime_iff`). The naive estimate of how
many survive is `x` times the survivor share. That estimate does not match the
number of primes: their ratio tends to twice e to the minus Euler's constant,
about 1.1229. So the wheel product overshoots the true count by about 12%.

This is the classical demonstration that the sieve's error terms do not
vanish once the wheels reach the square root (Mertens' factor 2e^(-γ) instead
of 1), next to the parity obstruction recorded in `AlmostPrimeWindow`.
Numerically the ratio climbs slowly: 0.91 at a thousand, 1.01 at a hundred
thousand, 1.05 at ten million.

Proof: `RNSSolutions/CeilingOvershoot.lean`, a step from
`MertensThird.mertens_third` and `PrimeNumberTheorem.prime_number_theorem`.
Metadata: `formalization.yaml`.
-/

namespace RNS.CeilingOvershoot

open Filter Topology

/-- **The overshoot at the ceiling.** With the wheels up to the square root of
`x`, the survivor share times `x`, divided by the number of primes up to `x`,
tends to twice e to the minus Euler's constant. -/
def ceiling_overshoot : Prop :=
  Tendsto (fun x : ℝ =>
      RNS.MertensThird.survivor_share (Real.sqrt x) * x / (Nat.primeCounting ⌊x⌋₊ : ℝ))
    atTop (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant)))

end RNS.CeilingOvershoot
