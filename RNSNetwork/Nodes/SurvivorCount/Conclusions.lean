/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# SurvivorCount — the exact number of open positions

The number of positions in the combined cycle that survive every wheel is
the product, over the wheels, of the open positions on each one.

Proof: `RNSSolutions/SurvivorCount.lean`, which assumes the `CRT` claim and
nothing else. Metadata: `formalization.yaml`.

Source of record: `rns_sieve_6.lean`, Part A Step 4
(`wheel_survivors_card_formula`) and Part B Step 4
(`local_survivors_gen_card`, `wheel_survivors_gen_card_formula`). The source
gives the last two an admissibility hypothesis that their proofs never use;
it is dropped here, which makes both claims stronger.
-/

namespace RNS.SurvivorCount

/-- **Twin-pattern survivors.** The positions of the combined cycle that
survive the twin pattern number exactly the product over the active wheels
of: 1 at the wheel of size 2, and two fewer than the wheel size elsewhere. -/
def twin_survivor_count : Prop :=
  ∀ limit : Nat,
    (wheel_survivors limit).card = ∏ q ∈ active_primes limit, (if q = 2 then 1 else q - 2)

/-- **Survivors on one wheel.** On the wheel of size `p`, exactly `p` minus
`w` positions survive an offset pattern: each distinct position the pattern
occupies blocks one position. -/
def local_survivor_count : Prop :=
  ∀ (T : Finset Nat) (p : Nat) (hp : p.Prime), (local_survivors_gen T p hp).card = p - w T p

/-- **Survivors of the whole cycle.** For any offset pattern, the positions of
the combined cycle surviving every active wheel number exactly the product,
over the active wheels, of the wheel size minus `w`. -/
def general_survivor_count : Prop :=
  ∀ (T : Finset Nat) (limit : Nat),
    (wheel_survivors_gen T limit).card = ∏ q ∈ active_primes limit, (q - w T q)

end RNS.SurvivorCount
