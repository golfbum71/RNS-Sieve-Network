/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# LehmerExcess — the closed form when every wheel is one short

Suppose every wheel leaves remainder one less than the number of equal
intervals (for six intervals: every wheel on the 6n-1 side). Then at the end
of each interval the survivor count's excess over its proportional share is
known exactly: minus (minus one, to the number of wheels) times two to the
number of wheels, times the count of intervals over the number of intervals
minus one half. Stated multiplied through by twice the number of intervals,
so everything stays a whole number. So the excess never averages out: its
size at the first interval's end is two to the number of wheels, times one
half minus one over the number of intervals.

Proof: `RNSSolutions/LehmerExcess.lean`, which assumes `Sawtooth`'s
`sawtooth_identity` and nothing else. Metadata: `formalization.yaml`.

Source: P. Codecà and M. Nair, "Extremal values of Δ(x, N)", Canad. Math.
Bull. 41 (1998), Theorem 2 and the identity in its proof (their gap at the
fraction `a / k` of the cycle).
-/

namespace RNS.LehmerExcess

/-- **The closed form for wheels one short.** For a nonempty set of prime
wheels `W`, each leaving remainder `k - 1` on division by the number of
intervals `k`, and a count of intervals `a` strictly between 0 and `k`: twice
`k` times the survivors up to `a` `k`-ths of the cycle (rounded down), minus
twice `a` times the survivors of the whole cycle, equals minus (minus one, to
the number of wheels) times two to the number of wheels times `2 a - k`. -/
def lehmer_excess_closed_form : Prop :=
  ∀ (W : Finset Nat) (k a : Nat), (∀ q ∈ W, q.Prime) → (∀ q ∈ W, q % k = k - 1) →
    W.Nonempty → 0 < a → a < k →
    2 * (k : Int) * (survivors_upto W (a * W.prod id / k)).card
        - 2 * (a : Int) * (survivors_upto W (W.prod id)).card
      = -((-1 : Int) ^ W.card * 2 ^ W.card * (2 * (a : Int) - k))

end RNS.LehmerExcess
