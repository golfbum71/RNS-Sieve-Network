/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# BrunTwinSum — the twin primes' reciprocals add up to a finite total

Brun's theorem (1919): the reciprocals of the twin primes,
1/3 + 1/5 + 1/5 + 1/7 + 1/11 + 1/13 + ..., add up to a finite total (Brun's
constant, about 1.902). It holds whether or not there are infinitely many
twin primes.

Its sieve heart is the RNS twin count: with the wheels below a bound, the
twin survivors make up at most about the square of the survivor share, which
falls like one over the logarithm squared (node `ShareBounds`). Brun's sieve
turns that wheel-level share into a bound on actual twin primes up to a
number, of order the number times (log log of it) squared over (log of it)
squared, and summing that bound gives convergence.

Cited, not proved in Lean. The statement follows the one on lean-lang.org's
problem list.

Metadata: `formalization.yaml`.
-/

namespace RNS.BrunTwinSum

/-- The contribution of `p` to Brun's sum: `1/p + 1/(p+2)` when `p` and
`p + 2` are both prime, and 0 otherwise. -/
noncomputable def twin_reciprocal (p : Nat) : ℝ :=
  if p.Prime ∧ (p + 2).Prime then 1 / (p : ℝ) + 1 / ((p + 2 : Nat) : ℝ) else 0

/-- **Brun's theorem** (cited). The twin-prime reciprocals have a finite sum. -/
def brun_sum_finite : Prop :=
  Summable twin_reciprocal

end RNS.BrunTwinSum
