/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# Pruning — which starting positions are worth testing

Once the Lagrange–Waring condition is met (every prime no larger than the
run length divides the spacing), the number of starting positions left to
test for an evenly spaced prime run is an exact product over the wheels.

Proof: `RNSSolutions/Pruning.lean`, which assumes
`SurvivorCount.general_survivor_count`. Metadata: `formalization.yaml`.

Source of record: `rns_sieve_6.lean`, Part E
(`valid_starting_residues_card_formula`). The source names the surviving set
`valid_starting_residues d k L`; here it is written out as
`wheel_survivors_gen (ap_offsets d k) L`, which is its definition.
-/

namespace RNS.Pruning

/-- **Exact pruning count.** For a nonzero spacing, a run length of at least
1, and the Lagrange–Waring condition met, the starting positions of the
combined cycle that survive every active wheel number exactly the product
over those wheels of: one fewer than the wheel size where the wheel divides
the spacing, and the run length fewer elsewhere. -/
def valid_starting_residues_card_formula : Prop :=
  ∀ d k L : Nat, d ≠ 0 → 1 ≤ k → (∀ p, p.Prime → p ≤ k → p ∣ d) →
    (wheel_survivors_gen (ap_offsets d k) L).card =
      ∏ q ∈ active_primes L, (if q ∣ d then q - 1 else q - k)

end RNS.Pruning
