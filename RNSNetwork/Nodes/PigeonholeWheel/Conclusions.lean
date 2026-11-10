/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# PigeonholeWheel — one pigeon per wheel

When a new wheel joins, each position that survived the earlier wheels has
one copy in the longer cycle for every slot of the new wheel. No two copies
share a slot, so by pigeonhole every slot receives exactly one copy: one copy
is closed (the pigeon) and the others, one fewer than the wheel size, stay
open (the holes). Starting from the two open positions of wheels 2 and 3
(the 6n+1 and 6n-1 positions), two survivors are carried through every
further wheel. If every prime were a wheel, only position 1 would be open:
two survivors, one safe spot, so the primes never run out.

Proof: `RNSSolutions/PigeonholeWheel.lean`; rests on no other node. Metadata:
`formalization.yaml`.
-/

namespace RNS.PigeonholeWheel

/-- The slot of the wheel of size `q` on which copy number `i` of the
position `start` lands, when `M` is the product of the earlier wheels: the
copy is `start + i * M`. Defined here because only this node uses it. -/
def lift_slot (q M start : Nat) (i : Fin q) : ZMod q :=
  ((start + i.val * M : Nat) : ZMod q)

/-- A position survives the wheels 2 and 3 and every wheel in `W`: none of
them divides it. Defined here because only this node uses it. -/
def survives (W : Finset Nat) (x : Nat) : Prop :=
  ¬ 2 ∣ x ∧ ¬ 3 ∣ x ∧ ∀ q ∈ W, ¬ q ∣ x

/-- **One pigeon per wheel.** For a new wheel whose size `q` does not divide
the product `M` of the earlier wheels, exactly one copy of any position lands
on the blocked slot. -/
def one_closed_copy : Prop :=
  ∀ q M start : Nat, q.Prime → ¬ q ∣ M → ∃! i : Fin q, lift_slot q M start i = 0

/-- **The holes.** Under the same conditions, the copies left open number
exactly one fewer than the wheel size. -/
def open_copies : Prop :=
  ∀ q M start : Nat, q.Prime → ¬ q ∣ M →
    (Finset.univ.filter (fun i : Fin q => lift_slot q M start i ≠ 0)).card = q - 1

/-- **Two survivors persist.** For any set `W` of wheels of size at least 5,
the cycle of length 6 times the product of `W` has two different positions
open on the wheels 2, 3 and every wheel in `W`. -/
def two_survivors_persist : Prop :=
  ∀ W : Finset Nat, (∀ q ∈ W, q.Prime ∧ 5 ≤ q) →
    ∃ x y, x < 6 * ∏ p ∈ W, p ∧ y < 6 * ∏ p ∈ W, p ∧ x ≠ y ∧
      survives W x ∧ survives W y

/-- **Infinitude by pigeonhole.** Above every bound there is a prime: if every
prime were below the bound, every position other than 1 would be closed, yet
two different positions survive. -/
def pigeonhole_primes_unbounded : Prop :=
  ∀ limit : Nat, ∃ p, p.Prime ∧ limit ≤ p

end RNS.PigeonholeWheel
