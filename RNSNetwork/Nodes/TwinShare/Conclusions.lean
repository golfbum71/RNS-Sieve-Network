/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# TwinShare — the twin share of the cycle

Among the positions of the combined cycle that survive every active wheel
(the offset pattern `{0}`), the share that also survive the twin pattern is
exactly the product, over the active wheels other than 2, of the wheel size
minus 2 over the wheel size minus 1. That product splits into the partial
twin-prime constant (the product of one minus one over the wheel size minus
1, squared) times the share of numbers the odd wheels leave open (the product
of the wheel size minus 1 over the wheel size).

Proof: `RNSSolutions/TwinShare.lean`; `twin_share_eq_prod` assumes two claims
of `SurvivorCount`, and `twin_share_split` is finite arithmetic. Metadata:
`formalization.yaml`.

Source: J. S. Birdsey and G. Schay, "A Sieve for Twin Primes",
arXiv:1906.09220 (2019): the exact share their second method uses.
-/

namespace RNS.TwinShare

/-- **The twin share of the cycle.** For the wheels below `limit`, the twin
survivors of the cycle divided by the survivors of the pattern `{0}` equal
the product, over the active wheels other than 2, of the wheel size minus 2
over the wheel size minus 1. -/
def twin_share_eq_prod : Prop :=
  ∀ limit : Nat,
    ((wheel_survivors limit).card : Real) / (wheel_survivors_gen {0} limit).card
      = ∏ q ∈ (active_primes limit).erase 2, ((q : Real) - 2) / ((q : Real) - 1)

/-- **The twin share, split.** The same product equals the partial twin-prime
constant (one minus one over the wheel size minus 1, squared, over the odd
active wheels) times the share the odd active wheels leave open (the wheel
size minus 1 over the wheel size). -/
def twin_share_split : Prop :=
  ∀ limit : Nat,
    ∏ q ∈ (active_primes limit).erase 2, ((q : Real) - 2) / ((q : Real) - 1)
      = (∏ q ∈ (active_primes limit).erase 2, (1 - 1 / ((q : Real) - 1) ^ 2))
        * ∏ q ∈ (active_primes limit).erase 2, ((q : Real) - 1) / (q : Real)

end RNS.TwinShare
