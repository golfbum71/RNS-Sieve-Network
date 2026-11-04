/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# Infinitude — two independent proofs that primes never run out

The same fact, proved two different ways. First, Euclid's argument using the
combined cycle plus one. Second, a counting argument: a fixed finite set of
wheels can only build boundedly many square-free numbers, too few to serve
as the square-free part of every number up to a large enough bound.

Proof: `RNSSolutions/Infinitude.lean`; rests on no other node. Metadata:
`formalization.yaml`.

Source of record: `rns_sieve_6.lean` (`rns_primes_unbounded`,
`rns_wheel_supply_cannot_be_finite`).
-/

namespace RNS.Infinitude

/-- **Euclid, via the combined cycle.** Above every bound there is a prime:
the combined cycle of all primes below the bound, plus one, has a prime
factor that cannot be below the bound. -/
def euclid_primes_unbounded : Prop :=
  ∀ limit : Nat, ∃ p, p.Prime ∧ limit ≤ p

/-- **No finite supply of wheels, by counting.** For no bound are all primes
below it: if they were, every number would be a square times a divisor of the
fixed combined cycle, and there are too few such pairs to cover every number
up to a large enough ceiling. -/
def squarefree_counting_no_finite_supply : Prop :=
  ∀ limit : Nat, ¬ ∀ p, p.Prime → p < limit

end RNS.Infinitude
