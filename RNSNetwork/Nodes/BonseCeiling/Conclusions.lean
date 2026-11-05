/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# BonseCeiling — from four wheels on, the ceiling sits inside one cycle

Take the wheels below a prime `p`. Their ceiling is `p` squared: below it,
surviving every wheel is the same as being prime. Their combined cycle is the
product of the wheels. With the wheels 2, 3, 5 the ceiling (49) lies outside
the cycle (30); once the wheel 7 is in, the ceiling (121) lies inside the
cycle (210), and it stays inside for every larger set of wheels.

This is Bonse's inequality (1907): the product of the first `n` primes exceeds
the square of the next prime once `n` is at least 4. In the network's terms,
`p` ranges over the primes from 11 on (the next prime after four wheels).

Proof: `RNSSolutions/BonseCeiling.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.BonseCeiling

/-- **The ceiling lies inside one combined cycle.** For every prime `p` from
11 on, the square of `p` (the ceiling of the wheels below `p`) is smaller
than the product of the wheels below `p` (their combined cycle). -/
def ceiling_inside_cycle : Prop :=
  ∀ p : Nat, p.Prime → 11 ≤ p → p ^ 2 < primorial_modulus p

end RNS.BonseCeiling
