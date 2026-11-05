/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# KanoldBound — every stretch of 2^k numbers holds a survivor of k wheels

For any `k` prime wheels, every stretch of two to the `k` consecutive numbers
contains a number that survives every wheel. Equivalently, the largest gap
between consecutive survivors (Jacobsthal's function of the cycle length) is
at most two to the number of wheels.

This is Kanold's explicit bound on Jacobsthal's function (1967). It is weaker
than the quadratic bound (node `JacobsthalQuadratic`) for many wheels, but it
has no hidden constant, so it can be evaluated for any concrete set of frozen
wheels.

Cited, not proved in Lean. Checked numerically on 2026-11-05 for every set of
up to six wheels drawn from the primes up to 23 (the bound is attained by one
wheel and by two wheels).

Metadata: `formalization.yaml`.
-/

namespace RNS.KanoldBound

/-- **Kanold's bound** (cited). For any finite set `W` of prime wheels and any
starting point `x`, one of the two-to-the-`|W|` numbers `x, x + 1, ...`
survives every wheel. -/
def stretch_holds_survivor : Prop :=
  ∀ (W : Finset Nat), (∀ q ∈ W, q.Prime) →
    ∀ x : Nat, ∃ i < 2 ^ W.card, ∀ q ∈ W, ¬ q ∣ x + i

end RNS.KanoldBound
