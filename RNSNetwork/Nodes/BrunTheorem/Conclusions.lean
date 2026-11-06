/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunAnalytic.Conclusions
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# BrunTheorem — the reciprocals of the twin primes have a finite sum

Brun's theorem (1919): adding one over `p` and one over `p + 2` for every
twin prime pair `p`, `p + 2` gives a finite total (Brun's constant, about
1.902). The sum of the reciprocals of all primes is infinite, so this says
twin primes are rare in a precise sense, whether or not there are
infinitely many.

The proof cuts the positions into stretches from a power of 2 to the next.
In the stretch from `2ᵏ` to `2ᵏ⁺¹`, each twin pair adds at most `2 / 2ᵏ`, and
by `BrunAnalytic` there are at most a constant times `2ᵏ⁺¹` over
`((k + 1) log 2)` to the three halves of them, once `2ᵏ⁺¹` is large. So the
stretch adds at most a constant over `k` to the three halves, and those add
up to a finite total. The finitely many early stretches add at most 4 each.

Proof: `RNSSolutions/BrunTheorem.lean`. Rests on `BrunAnalytic`.
Metadata: `formalization.yaml`.
-/

namespace RNS.BrunTheorem

/-- One over `n` plus one over `n + 2` when `n` and `n + 2` are both prime,
and zero otherwise. -/
noncomputable def twin_reciprocal (n : Nat) : ℝ :=
  if n.Prime ∧ (n + 2).Prime then 1 / (n : ℝ) + 1 / ((n : ℝ) + 2) else 0

/-- **Brun's theorem.** -/
def brun_theorem : Prop := Summable twin_reciprocal

end RNS.BrunTheorem
