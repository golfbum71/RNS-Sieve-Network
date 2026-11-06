/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# MenonIdentity — a gcd sum over the survivors of one cycle

Take a set of prime wheels and their combined cycle. For each survivor of the
cycle, take the greatest common divisor of (the survivor minus one) with the
cycle length, and add these up. The total is the number of survivors times
two to the number of wheels.

This is Menon's identity (1965) for a squarefree modulus: the sum of
gcd(k - 1, n) over the k from 1 to n coprime to n equals the totient of n
times the number of divisors of n. For the cycle of `k` prime wheels the
number of divisors is two to the `k`.

Proved in `RNSSolutions/MenonIdentity.lean` (elementary counting). Checked
numerically first, on 2026-11-05, for every set
of wheels drawn from the primes up to 13.

Metadata: `formalization.yaml`.
-/

namespace RNS.MenonIdentity

/-- **Menon's identity, wheel form**. For a finite set `W` of prime
wheels with cycle length `W.prod id`, the sum over the survivors `k` of one
cycle of `gcd (k - 1, cycle length)` equals the number of survivors times
two to the number of wheels. -/
def menon_wheel_sum : Prop :=
  ∀ (W : Finset Nat), (∀ q ∈ W, q.Prime) →
    ∑ k ∈ survivors_upto W (W.prod id), Nat.gcd (k - 1) (W.prod id)
      = (survivors_upto W (W.prod id)).card * 2 ^ W.card

end RNS.MenonIdentity
